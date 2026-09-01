"""TTY-aware Tokyo Night status rendering for pane runners and controllers."""

from __future__ import annotations

import os
import sys
import threading
import time
from dataclasses import dataclass
from typing import TextIO

_RESET = "\x1b[0m"
_CLEAR = "\r\x1b[2K"
_DISABLE_WRAP = "\x1b[?7l"
_ENABLE_WRAP = "\x1b[?7h"
_PURPLE = "\x1b[38;2;187;154;247m"
_BLUE = "\x1b[38;2;122;162;247m"
_GREEN = "\x1b[38;2;158;206;106m"
_YELLOW = "\x1b[38;2;224;175;104m"
_RED = "\x1b[38;2;247;118;142m"
_MUTED = "\x1b[38;2;169;177;214m"
_FRAMES = ("⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏")
_REFRESH_SECONDS = 1.0


def format_elapsed(seconds: float) -> str:
    """Format a nonnegative duration as HH:MM:SS."""
    total = max(0, int(seconds))
    hours, remainder = divmod(total, 3600)
    minutes, secs = divmod(remainder, 60)
    return f"{hours:02d}:{minutes:02d}:{secs:02d}"


def _color_enabled(stream: TextIO) -> bool:
    return (
        hasattr(stream, "isatty")
        and stream.isatty()
        and "NO_COLOR" not in os.environ
        and os.environ.get("TERM", "") != "dumb"
    )


def _paint(text: str, color: str, enabled: bool) -> str:
    return f"{color}{text}{_RESET}" if enabled else text


def _terminal_columns(stream: TextIO) -> int:
    try:
        return os.get_terminal_size(stream.fileno()).columns
    except (AttributeError, OSError):
        return 80


def _truncate(text: str, width: int) -> str:
    if len(text) <= width:
        return text
    if width <= 1:
        return text[:width]
    return text[: width - 1] + "…"


class PaneHeartbeat:
    """Render one live role spinner without contaminating retained OMP output."""

    def __init__(self, role_id: str, *, stream: TextIO | None = None) -> None:
        self.role_id = role_id
        self.stream = stream or sys.stdout
        self.started = time.monotonic()
        self._color = _color_enabled(self.stream)
        self._interactive = hasattr(self.stream, "isatty") and self.stream.isatty()
        self._stop = threading.Event()
        self._lock = threading.Lock()
        self._thread: threading.Thread | None = None
        self._frame = 0

    def start(self) -> None:
        self.started = time.monotonic()
        if not self._interactive:
            return
        self._render()
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()

    def _line(self) -> str:
        elapsed_text = format_elapsed(time.monotonic() - self.started)
        columns = max(1, _terminal_columns(self.stream) - 1)
        fixed_width = len(_FRAMES[0]) + len(elapsed_text) + 4
        role_width = max(1, columns - fixed_width)
        role_text = _truncate(self.role_id, role_width)
        frame = _paint(_FRAMES[self._frame % len(_FRAMES)], _PURPLE, self._color)
        role = _paint(role_text, _BLUE, self._color)
        elapsed = _paint(elapsed_text, _MUTED, self._color)
        return f"{frame} [{role}] {elapsed}"

    def _render_locked(self) -> None:
        self.stream.write(_DISABLE_WRAP + _CLEAR + self._line() + _ENABLE_WRAP)
        self.stream.flush()

    def _render(self) -> None:
        with self._lock:
            self._render_locked()

    def _run(self) -> None:
        while not self._stop.wait(_REFRESH_SECONDS):
            self._frame += 1
            self._render()

    def write(self, destination: TextIO, text: str) -> None:
        """Print subprocess output while preserving one bottom status line."""
        with self._lock:
            if self._interactive:
                self.stream.write(_ENABLE_WRAP + _CLEAR)
            destination.write(text)
            destination.flush()
            if self._interactive:
                if text and not text.endswith("\n"):
                    self.stream.write("\n")
                self._render_locked()

    def finish(self, status: str) -> None:
        self._stop.set()
        if self._thread is not None:
            self._thread.join(timeout=1)
        color = _GREEN if status == "succeeded" else _RED
        symbol = "✓" if status == "succeeded" else "✗"
        elapsed = format_elapsed(time.monotonic() - self.started)
        with self._lock:
            if self._interactive:
                self.stream.write(_ENABLE_WRAP + _CLEAR)
            self.stream.write(
                f"{_paint(symbol, color, self._color)} "
                f"[{_paint(self.role_id, _BLUE, self._color)}] "
                f"{_paint(status, color, self._color)} · "
                f"{_paint(elapsed, _MUTED, self._color)}\n"
            )
            self.stream.flush()


@dataclass(frozen=True, slots=True)
class RoleStatus:
    role_id: str
    state: str
    elapsed_seconds: float = 0.0


class ControllerDashboard:
    """Compact aggregate DAG status line for the launching terminal."""

    def __init__(
        self, role_ids: tuple[str, ...], *, stream: TextIO | None = None
    ) -> None:
        self.role_ids = role_ids
        self.stream = stream or sys.stdout
        self._color = _color_enabled(self.stream)
        self._interactive = hasattr(self.stream, "isatty") and self.stream.isatty()
        self._frame = 0
        self._last_plain: tuple[tuple[str, str], ...] | None = None

    def _segment(self, status: RoleStatus) -> str:
        if status.state == "running":
            symbol = _paint(_FRAMES[self._frame % len(_FRAMES)], _PURPLE, self._color)
            state = _paint(format_elapsed(status.elapsed_seconds), _MUTED, self._color)
        elif status.state == "succeeded":
            symbol = _paint("✓", _GREEN, self._color)
            state = _paint("done", _GREEN, self._color)
        elif status.state == "failed":
            symbol = _paint("✗", _RED, self._color)
            state = _paint("failed", _RED, self._color)
        elif status.state == "skipped":
            symbol = _paint("–", _YELLOW, self._color)
            state = _paint("skipped", _YELLOW, self._color)
        else:
            symbol = _paint("·", _MUTED, self._color)
            state = _paint(status.state, _MUTED, self._color)
        name = _paint(status.role_id, _BLUE, self._color)
        return f"{symbol} {name} {state}"

    def render(self, statuses: tuple[RoleStatus, ...], *, final: bool = False) -> None:
        self._frame += 1
        if not self._interactive:
            snapshot = tuple((status.role_id, status.state) for status in statuses)
            if snapshot == self._last_plain and not final:
                return
            self._last_plain = snapshot
        line = "  |  ".join(self._segment(status) for status in statuses)
        prefix = _paint("proof-builder", _PURPLE, self._color)
        if self._interactive:
            self.stream.write(
                _DISABLE_WRAP + _CLEAR + prefix + "  " + line + _ENABLE_WRAP
            )
            if final:
                self.stream.write("\n")
        else:
            self.stream.write(prefix + "  " + line + "\n")
        self.stream.flush()
