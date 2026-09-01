#!/usr/bin/env python3
"""Minimal Herdr CLI double for campaign integration tests."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path


def emit(result: dict[str, object]) -> None:
    print(json.dumps({"id": "fake", "result": result}, separators=(",", ":")))


def load_state() -> tuple[Path, dict[str, object]]:
    path = Path(os.environ["FAKE_HERDR_STATE"])
    if path.exists():
        return path, json.loads(path.read_text(encoding="utf-8"))
    return path, {"workspace": 0, "pane": 0, "workspaces": {}}


def save_state(path: Path, state: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state), encoding="utf-8")


def main() -> int:
    arguments = sys.argv[1:]
    path, state = load_state()
    if arguments[:2] == ["workspace", "create"]:
        state["workspace"] = int(state["workspace"]) + 1
        state["pane"] = int(state["pane"]) + 1
        workspace_id = f"w{state['workspace']}"
        label = arguments[arguments.index("--label") + 1]
        workspaces = state.setdefault("workspaces", {})
        assert isinstance(workspaces, dict)
        workspaces[workspace_id] = label
        save_state(path, state)
        emit(
            {
                "workspace": {"workspace_id": workspace_id},
                "root_pane": {"pane_id": f"{workspace_id}:p{state['pane']}"},
            }
        )
        return 0
    if arguments[:2] == ["workspace", "list"]:
        workspaces = state.setdefault("workspaces", {})
        assert isinstance(workspaces, dict)
        emit(
            {
                "type": "workspace_list",
                "workspaces": [
                    {"workspace_id": workspace_id, "label": label}
                    for workspace_id, label in sorted(workspaces.items())
                ],
            }
        )
        return 0
    if arguments[:2] == ["pane", "split"]:
        state["pane"] = int(state["pane"]) + 1
        save_state(path, state)
        workspace_id = arguments[2].split(":", 1)[0]
        emit({"pane": {"pane_id": f"{workspace_id}:p{state['pane']}"}})
        return 0
    if arguments[:2] == ["pane", "rename"]:
        emit({"type": "ok"})
        return 0
    if arguments[:2] == ["pane", "run"]:
        command = arguments[3:]
        if command and command[0] == " env":
            command[0] = "env"
        subprocess.Popen(
            command,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
            env=os.environ.copy(),
        )
        emit({"type": "ok"})
        return 0
    if arguments[:2] == ["workspace", "close"]:
        workspaces = state.setdefault("workspaces", {})
        assert isinstance(workspaces, dict)
        workspace_id = arguments[2]
        if workspace_id not in workspaces:
            print(
                '{"error":{"code":"workspace_not_found","message":"missing"}}',
                file=sys.stderr,
            )
            return 1
        del workspaces[workspace_id]
        save_state(path, state)
        emit({"type": "ok"})
        return 0
    print(f"unsupported fake Herdr command: {arguments}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
