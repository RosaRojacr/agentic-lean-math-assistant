#!/usr/bin/env python3
"""Run targeted certificate and checker mutations through the real fail-closed CLI."""
from __future__ import annotations

import hashlib
import json
import platform
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "manifest.json"
CHECKER = ROOT / "check_tiling.py"
KERNEL = ROOT.parent / "face_bridge_pilot" / "check_bridge.py"
FIXTURES = ROOT / "mutation_fixtures.json"


def semantic_hash(raw: dict[str, Any]) -> str:
    payload = {key: value for key, value in raw.items() if key != "payload_sha256"}
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def byte_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, raw: dict[str, Any]) -> None:
    path.write_text(json.dumps(raw, indent=2, sort_keys=True) + "\n")


def set_path(raw: Any, path: list[Any], value: Any) -> None:
    target = raw
    for key in path[:-1]:
        target = target[key]
    target[path[-1]] = value


def delete_path(raw: Any, path: list[Any]) -> None:
    target = raw
    for key in path[:-1]:
        target = target[key]
    del target[path[-1]]


def run(checker: Path, manifest: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["python3", str(checker), str(manifest)], text=True, capture_output=True, check=False)


def make_data_mutation(case: dict[str, Any], directory: Path) -> Path:
    shutil.copytree(ROOT / "bricks", directory / "bricks")
    manifest_path = directory / "manifest.json"
    manifest = json.loads(MANIFEST.read_text())
    operation = case["operation"]
    if operation in {"manifest_set", "manifest_no_rehash"}:
        set_path(manifest, case["path"], case["value"])
        if operation == "manifest_set":
            manifest["payload_sha256"] = semantic_hash(manifest)
        write_json(manifest_path, manifest)
    elif operation == "manifest_corrupt_hash":
        manifest["payload_sha256"] = "0" * 64
        write_json(manifest_path, manifest)
    elif operation == "swap_entries":
        first, second = case["indices"]
        manifest["bricks"][first], manifest["bricks"][second] = manifest["bricks"][second], manifest["bricks"][first]
        manifest["payload_sha256"] = semantic_hash(manifest)
        write_json(manifest_path, manifest)
    elif operation == "duplicate_manifest_schema":
        text = MANIFEST.read_text()
        text = text.replace('  "schema":', '  "schema": "duplicate",\n  "schema":', 1)
        manifest_path.write_text(text)
    elif operation in {"shard_set", "shard_delete", "shard_no_rehash", "shard_corrupt_payload_hash"}:
        index = case["brick"]
        shard_path = directory / manifest["bricks"][index]["path"]
        shard = json.loads(shard_path.read_text())
        if operation == "shard_delete":
            delete_path(shard, case["path"])
        elif operation == "shard_corrupt_payload_hash":
            shard["payload_sha256"] = "0" * 64
        else:
            set_path(shard, case["path"], case["value"])
        if operation not in {"shard_no_rehash", "shard_corrupt_payload_hash"}:
            shard["payload_sha256"] = semantic_hash(shard)
        write_json(shard_path, shard)
        if operation != "shard_no_rehash":
            manifest["bricks"][index]["certificate_sha256"] = byte_hash(shard_path)
            manifest["payload_sha256"] = semantic_hash(manifest)
        write_json(manifest_path, manifest)
    else:
        raise ValueError(f"unsupported data operation: {operation}")
    return manifest_path


def make_source_mutation(case: dict[str, Any], directory: Path) -> Path:
    checker_text = CHECKER.read_text()
    if case["operation"] == "checker_replace":
        require_single(checker_text, case["old"], case["id"])
        checker_text = checker_text.replace(case["old"], case["new"], 1)
    else:
        kernel_text = KERNEL.read_text()
        require_single(kernel_text, case["old"], case["id"])
        kernel_text = kernel_text.replace(case["old"], case["new"], 1)
        kernel_path = ROOT / f".mutation_kernel_{case['id']}.py"
        kernel_path.write_text(kernel_text)
        old_assignment = 'KERNEL_PATH = PROOF_ROOT / "face_bridge_pilot" / "check_bridge.py"'
        require_single(checker_text, old_assignment, case["id"])
        checker_text = checker_text.replace(old_assignment, f'KERNEL_PATH = Path({str(kernel_path)!r})', 1)
        old_kernel_hash = f'KERNEL_SHA256 = "{byte_hash(KERNEL)}"'
        require_single(checker_text, old_kernel_hash, case["id"])
        checker_text = checker_text.replace(old_kernel_hash, f'KERNEL_SHA256 = "{byte_hash(kernel_path)}"', 1)
    checker_path = ROOT / f".mutation_checker_{case['id']}.py"
    checker_path.write_text(checker_text)
    return checker_path


def require_single(text: str, needle: str, mutation_id: str) -> None:
    count = text.count(needle)
    if count != 1:
        raise RuntimeError(f"{mutation_id}: source needle count {count}: {needle}")


def cleanup_source(case: dict[str, Any], checker_path: Path) -> None:
    checker_path.unlink(missing_ok=True)
    if case["operation"] == "kernel_replace":
        (ROOT / f".mutation_kernel_{case['id']}.py").unlink(missing_ok=True)


def parse_failure(process: subprocess.CompletedProcess[str], mutation_id: str) -> dict[str, Any]:
    try:
        receipt = json.loads(process.stdout)
        failure = receipt["failure"]
    except Exception as exc:
        raise RuntimeError(f"{mutation_id}: non-JSON failure; stdout={process.stdout!r}; stderr={process.stderr!r}") from exc
    return {"receipt": receipt, "failure": failure}


def main() -> None:
    baseline = run(CHECKER, MANIFEST)
    if baseline.returncode != 0 or json.loads(baseline.stdout).get("status") != "PASS":
        raise SystemExit(f"baseline checker failed: {baseline.stdout} {baseline.stderr}")
    fixtures = json.loads(FIXTURES.read_text())
    if set(fixtures) != {"schema", "mutations"} or fixtures["schema"] != "cmv-middle-face-tiling-mutations-v1":
        raise SystemExit("mutation fixture schema failed")
    results: list[dict[str, Any]] = []
    source_operations = {"kernel_replace", "checker_replace"}
    with tempfile.TemporaryDirectory() as temporary:
        temp_root = Path(temporary)
        for case in fixtures["mutations"]:
            operation = case["operation"]
            checker_path = CHECKER
            if operation in source_operations:
                checker_path = make_source_mutation(case, temp_root)
                manifest_path = MANIFEST
            else:
                case_dir = temp_root / case["id"]
                case_dir.mkdir()
                manifest_path = make_data_mutation(case, case_dir)
            process = run(checker_path, manifest_path)
            if operation in source_operations:
                cleanup_source(case, checker_path)
            parsed = parse_failure(process, case["id"])
            actual = parsed["failure"].get("code")
            accepted = process.returncode != 0 and parsed["receipt"].get("status") == "FAIL" and actual == case["expected_code"]
            if not accepted:
                raise SystemExit(f"{case['id']}: expected {case['expected_code']}, got rc={process.returncode}, code={actual}, receipt={parsed['receipt']}")
            results.append({
                "id": case["id"],
                "category": case["category"],
                "operation": operation,
                "expected_code": case["expected_code"],
                "actual_code": actual,
                "first_failure": parsed["failure"],
                "rejected": True,
            })
    categories = sorted({result["category"] for result in results})
    output = {
        "status": "PASS",
        "schema": "cmv-middle-face-tiling-mutation-receipt-v1",
        "rejected": len(results),
        "total": len(fixtures["mutations"]),
        "categories": categories,
        "results": results,
        "python": platform.python_version(),
        "manifest_sha256": byte_hash(MANIFEST),
        "checker_sha256": byte_hash(CHECKER),
        "kernel_sha256": byte_hash(KERNEL),
        "fixtures_sha256": byte_hash(FIXTURES),
        "runner_sha256": byte_hash(Path(__file__)),
    }
    text = json.dumps(output, indent=2, sort_keys=True) + "\n"
    (ROOT / "mutation_receipt.json").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
