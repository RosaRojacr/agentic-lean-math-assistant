"""Small, typed client for the Herdr terminal-workspace CLI."""

from __future__ import annotations

import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .command import CapturedCommand, run_captured_command


class HerdrError(RuntimeError):
    """Herdr could not create or control the requested workspace."""

    def __init__(self, message: str, *, code: str | None = None) -> None:
        super().__init__(message)
        self.code = code


@dataclass(frozen=True, slots=True)
class HerdrWorkspace:
    workspace_id: str
    root_pane_id: str


@dataclass(frozen=True, slots=True)
class HerdrWorkspaceRecord:
    workspace_id: str
    label: str


class HerdrClient:
    def __init__(self, executable: str = "herdr", *, timeout: float = 30.0) -> None:
        if not executable.strip():
            raise ValueError("Herdr executable must not be empty")
        if timeout <= 0:
            raise ValueError("Herdr timeout must be positive")
        self.executable = executable
        self.timeout = timeout

    def _run(self, *arguments: str) -> CapturedCommand:
        return run_captured_command(
            (self.executable, *arguments),
            cwd=Path.cwd(),
            env=os.environ,
            timeout=self.timeout,
        )

    def _json(self, *arguments: str) -> dict[str, Any]:
        completed = self._run(*arguments)
        if completed.error is not None:
            raise HerdrError(f"cannot execute Herdr: {completed.error}")
        if completed.exit_code != 0:
            detail = completed.stderr.strip() or completed.stdout.strip()
            code: str | None = None
            try:
                failure = json.loads(detail)
            except json.JSONDecodeError:
                failure = None
            if isinstance(failure, dict):
                error = failure.get("error")
                if isinstance(error, dict) and isinstance(error.get("code"), str):
                    code = error["code"]
            raise HerdrError(
                f"Herdr command failed with exit {completed.exit_code}: {detail}",
                code=code,
            )
        try:
            value = json.loads(completed.stdout)
        except json.JSONDecodeError as exc:
            raise HerdrError(
                f"Herdr returned invalid JSON: {completed.stdout!r}"
            ) from exc
        if not isinstance(value, dict):
            raise HerdrError("Herdr response must be a JSON object")
        return value

    @staticmethod
    def _result(response: dict[str, Any]) -> dict[str, Any]:
        result = response.get("result")
        if not isinstance(result, dict):
            raise HerdrError("Herdr response is missing a result object")
        return result

    def create_workspace(
        self,
        *,
        cwd: Path,
        label: str,
        focus: bool,
        environment: dict[str, str] | None = None,
    ) -> HerdrWorkspace:
        arguments = ["workspace", "create", "--cwd", str(cwd), "--label", label]
        for key, value in sorted((environment or {}).items()):
            arguments.extend(("--env", f"{key}={value}"))
        arguments.append("--focus" if focus else "--no-focus")
        result = self._result(self._json(*arguments))
        workspace = result.get("workspace")
        root_pane = result.get("root_pane")
        if not isinstance(workspace, dict) or not isinstance(root_pane, dict):
            raise HerdrError("workspace creation response is missing workspace or pane")
        workspace_id = workspace.get("workspace_id")
        pane_id = root_pane.get("pane_id")
        if not isinstance(workspace_id, str) or not isinstance(pane_id, str):
            raise HerdrError("workspace creation response has invalid IDs")
        return HerdrWorkspace(workspace_id=workspace_id, root_pane_id=pane_id)

    def list_workspaces(self) -> tuple[HerdrWorkspaceRecord, ...]:
        result = self._result(self._json("workspace", "list"))
        workspaces = result.get("workspaces")
        if not isinstance(workspaces, list):
            raise HerdrError("workspace list response is missing workspaces")
        records: list[HerdrWorkspaceRecord] = []
        for workspace in workspaces:
            if not isinstance(workspace, dict):
                raise HerdrError(
                    "workspace list response contains an invalid workspace"
                )
            workspace_id = workspace.get("workspace_id")
            label = workspace.get("label")
            if not isinstance(workspace_id, str) or not isinstance(label, str):
                raise HerdrError(
                    "workspace list response contains invalid identity fields"
                )
            records.append(HerdrWorkspaceRecord(workspace_id=workspace_id, label=label))
        return tuple(records)

    def split_pane(self, pane_id: str, *, cwd: Path) -> str:
        result = self._result(
            self._json(
                "pane",
                "split",
                pane_id,
                "--direction",
                "right",
                "--ratio",
                "0.5",
                "--cwd",
                str(cwd),
                "--no-focus",
            )
        )
        pane = result.get("pane")
        if not isinstance(pane, dict) or not isinstance(pane.get("pane_id"), str):
            raise HerdrError("pane split response is missing a pane ID")
        return pane["pane_id"]

    def rename_pane(self, pane_id: str, label: str) -> None:
        self._json("pane", "rename", pane_id, label)

    def run_in_pane(self, pane_id: str, command: tuple[str, ...]) -> None:
        if not command or any(not argument for argument in command):
            raise ValueError("pane command must contain nonempty arguments")
        completed = self._run("pane", "run", pane_id, " env", *command)
        if completed.error is not None:
            raise HerdrError(f"cannot execute Herdr: {completed.error}")
        if completed.exit_code != 0:
            detail = completed.stderr.strip() or completed.stdout.strip()
            raise HerdrError(
                f"cannot start command in pane {pane_id}: "
                f"{detail or completed.exit_code}"
            )

    def close_workspace(self, workspace_id: str) -> None:
        self._json("workspace", "close", workspace_id)
