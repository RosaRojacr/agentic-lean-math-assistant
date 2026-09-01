"""Digest-bound, transactional publication of verified campaign artifacts."""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import re
import secrets
import shutil
import stat
import tempfile
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

from .artifacts import (
    Artifact,
    atomic_write_json,
    digest_file,
    utc_now,
    verify_evidence_for_repair,
    verify_evidence_index,
)
from .config import CampaignSpec, ConfigurationError, PublishSpec
from .runtime import (
    CampaignRunError,
    campaign_resolved_for_run,
    campaign_run_lock,
    campaign_status,
    refresh_campaign_evidence,
)

_SHA256 = re.compile(r"[0-9a-f]{64}")
_CANONICAL_RECEIPT_FIELDS = (
    "schema_version",
    "campaign_id",
    "run_id",
    "evidence_sha256",
    "source",
    "root",
    "destination",
    "preserve",
    "preserved_entries",
    "artifacts",
    "changes",
)
_PUBLICATION_RECEIPT_FIELDS = (
    *_CANONICAL_RECEIPT_FIELDS,
    "approved_digest",
    "sha256",
    "phase",
    "recorded_at",
)
_RECOVERY_FIELDS = (
    "staging",
    "backup",
    "failed_destination",
    "had_destination",
)
_PUBLICATION_EVIDENCE_RECEIPTS = frozenset(
    {"publication.json", "publication.pending.json"}
)


def _publication_destination_for_lock(run_dir: Path) -> Path:
    try:
        campaign = CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir))
        if campaign.publish is None:
            raise CampaignRunError("retained campaign has no publish configuration")
        return campaign.publish.destination.resolve(strict=False)
    except (CampaignRunError, ConfigurationError):
        raise
    except (OSError, ValueError) as exc:
        raise CampaignRunError(
            f"cannot determine publication destination: {exc}"
        ) from exc


@contextmanager
def _destination_publication_lock(destination: Path) -> Iterator[None]:
    """Serialize every transaction targeting one canonical filesystem path."""

    canonical = destination.resolve(strict=False)
    identity = hashlib.sha256(os.fsencode(canonical)).hexdigest()
    lock_root = (
        Path(tempfile.gettempdir()).resolve()
        / f"agentic-lean-math-assistant-publication-{os.getuid()}"
    )
    root_descriptor: int | None = None
    descriptor: int | None = None
    locked = False
    try:
        lock_root.mkdir(mode=0o700, exist_ok=True)
        root_descriptor = os.open(
            lock_root,
            os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_DIRECTORY,
        )
        root_stat = os.fstat(root_descriptor)
        if (
            not stat.S_ISDIR(root_stat.st_mode)
            or root_stat.st_uid != os.getuid()
            or stat.S_IMODE(root_stat.st_mode) & 0o077
        ):
            raise CampaignRunError(
                "publication lock directory is not private to the current user"
            )
        descriptor = os.open(
            f"{identity}.lock",
            os.O_CREAT | os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
            dir_fd=root_descriptor,
        )
        lock_stat = os.fstat(descriptor)
        if (
            not stat.S_ISREG(lock_stat.st_mode)
            or lock_stat.st_uid != os.getuid()
            or lock_stat.st_nlink != 1
        ):
            raise CampaignRunError("publication destination lock is not a safe file")
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        locked = True
    except (CampaignRunError, OSError) as exc:
        if descriptor is not None:
            os.close(descriptor)
        if root_descriptor is not None:
            os.close(root_descriptor)
        if isinstance(exc, CampaignRunError):
            raise
        raise CampaignRunError(
            f"cannot acquire publication destination lock: {exc}"
        ) from exc
    try:
        yield
    finally:
        try:
            if locked:
                assert descriptor is not None
                fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            if descriptor is not None:
                os.close(descriptor)
            if root_descriptor is not None:
                os.close(root_descriptor)


@dataclass(frozen=True, slots=True)
class PublicationPlan:
    """Every identity, byte, and location authorized by one digest."""

    run_dir: Path
    campaign_id: str
    run_id: str
    evidence_sha256: str
    source: Path
    source_relative: str
    source_kind: str
    root: Path
    destination: Path
    preserve: tuple[str, ...]
    preserved_entries: tuple[tuple[str, str], ...]
    artifacts: tuple[Artifact, ...]
    changes: tuple[tuple[str, str], ...]
    digest: str

    def canonical_dict(self) -> dict[str, object]:
        """Return the complete plan payload committed to by ``digest``."""

        return {
            "schema_version": 1,
            "campaign_id": self.campaign_id,
            "run_id": self.run_id,
            "evidence_sha256": self.evidence_sha256,
            "source": {"path": self.source_relative, "kind": self.source_kind},
            "root": str(self.root),
            "destination": str(self.destination),
            "preserve": list(self.preserve),
            "preserved_entries": [
                {"path": path, "type": entry_type}
                for path, entry_type in self.preserved_entries
            ],
            "artifacts": [artifact.to_dict() for artifact in self.artifacts],
            "changes": [
                {"path": path, "status": status} for path, status in self.changes
            ],
        }

    def to_dict(self) -> dict[str, object]:
        """Return stable operator-facing JSON, including the approval digest."""

        return {**self.canonical_dict(), "approved_digest": self.digest}


def plan_publication(run_dir: Path) -> PublicationPlan:
    """Validate a complete run and return its deterministic, read-only plan."""

    run_dir = _validated_run_dir(run_dir)
    with campaign_run_lock(run_dir):
        destination = _publication_destination_for_lock(run_dir)
        with _destination_publication_lock(destination):
            return _plan_publication_locked(run_dir)


def publish_campaign(run_dir: Path, approve_digest: str) -> PublicationPlan:
    """Publish only the exact complete plan approved by the operator."""

    if _SHA256.fullmatch(approve_digest) is None:
        raise CampaignRunError("approve-digest must be a lowercase SHA-256 digest")
    run_dir = _validated_run_dir(run_dir)
    with campaign_run_lock(run_dir):
        destination = _publication_destination_for_lock(run_dir)
        with _destination_publication_lock(destination):
            plan = _plan_publication_locked(run_dir)
            if approve_digest != plan.digest:
                raise CampaignRunError(
                    "publication digest mismatch: "
                    f"approved {approve_digest}, planned {plan.digest}"
                )
            _publish_locked(plan)
            return plan


def _recover_pending_publication(run_dir: Path) -> None:
    """Deterministically finish or roll back a durable publication transaction."""

    pending = run_dir / "publication.pending.json"
    if not pending.is_file():
        return
    try:
        value = json.loads(pending.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignRunError(
            f"cannot recover pending publication receipt: {exc}"
        ) from exc
    if not isinstance(value, dict):
        raise CampaignRunError("pending publication receipt is malformed")
    _validate_pending_publication_receipt(value)
    phase = value.get("phase")
    terminal_receipt: dict[str, object] | None = None
    if phase in {"committed", "rolled_back"}:
        try:
            receipt_value = json.loads(
                (run_dir / "publication.json").read_text(encoding="utf-8")
            )
        except (OSError, json.JSONDecodeError) as exc:
            raise CampaignRunError(
                f"cannot validate {phase} publication receipt: {exc}"
            ) from exc
        if not isinstance(receipt_value, dict):
            raise CampaignRunError(f"{phase} publication receipt is malformed")
        terminal_receipt = receipt_value

    required = {
        "destination": str,
        "staging": str,
        "backup": str,
        "failed_destination": str,
        "had_destination": bool,
        "preserve": list,
    }
    for name, expected_type in required.items():
        if not isinstance(value.get(name), expected_type):
            raise CampaignRunError(f"pending publication receipt has invalid {name}")
    destination = Path(value["destination"])
    staging = Path(value["staging"])
    backup = Path(value["backup"])
    failed = Path(value["failed_destination"])
    if not destination.is_absolute():
        raise CampaignRunError("pending publication destination is not absolute")
    try:
        campaign = CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir))
    except (ConfigurationError, OSError, ValueError) as exc:
        raise CampaignRunError(
            f"cannot validate pending publication destination: {exc}"
        ) from exc
    if campaign.publish is None or destination != campaign.publish.destination:
        raise CampaignRunError(
            "pending publication destination does not match retained configuration"
        )
    preserve_value = value["preserve"]
    if not all(
        isinstance(item, str) and item and "/" not in item and item not in {".", ".."}
        for item in preserve_value
    ):
        raise CampaignRunError("pending publication preserve list is invalid")
    preserve = tuple(preserve_value)
    if preserve != campaign.publish.preserve:
        raise CampaignRunError(
            "pending publication preserve list does not match retained configuration"
        )
    parent = destination.parent
    expected_prefixes = {
        staging: f".{destination.name}.publish-",
        backup: f".{destination.name}.previous-",
        failed: f".{destination.name}.failed-",
    }
    if any(
        path.parent != parent or not path.name.startswith(prefix)
        for path, prefix in expected_prefixes.items()
    ):
        raise CampaignRunError("pending publication recovery paths are invalid")
    suffixes = {
        path.name.removeprefix(prefix) for path, prefix in expected_prefixes.items()
    }
    if (
        len(suffixes) != 1
        or (token := next(iter(suffixes))) == ""
        or len(token) != 12
        or any(character not in "0123456789abcdef" for character in token)
    ):
        raise CampaignRunError("pending publication recovery token is invalid")

    if terminal_receipt is not None:
        _validate_terminal_publication_receipts(run_dir, value, terminal_receipt, phase)
        repair_evidence = _verify_terminal_publication_evidence(run_dir)
        for path in (staging, backup, failed):
            if path.exists() or path.is_symlink():
                _remove_path(path)
        _fsync_directory(parent)
        if repair_evidence:
            refresh_campaign_evidence(run_dir)
        return
    _validate_nonterminal_publication_identity(run_dir, value, campaign)
    _validate_nonterminal_recovery_state(
        destination,
        staging,
        backup,
        failed,
        value["had_destination"],
    )

    had_destination = value["had_destination"]
    if phase not in {"prepared", "swapped"}:
        raise CampaignRunError(f"pending publication has unknown phase {phase!r}")
    if backup.exists() or backup.is_symlink():
        preserved_source = (
            staging
            if staging.is_dir() and not staging.is_symlink()
            else destination
            if destination.is_dir() and not destination.is_symlink()
            else None
        )
        if preserved_source is not None:
            for name in preserve:
                source = preserved_source / name
                target = backup / name
                if (source.exists() or source.is_symlink()) and not (
                    target.exists() or target.is_symlink()
                ):
                    os.replace(source, target)
            _fsync_directory(preserved_source)
            _fsync_directory(backup)
        if destination.exists() or destination.is_symlink():
            if failed.exists() or failed.is_symlink():
                _remove_path(failed)
            os.replace(destination, failed)
        os.replace(backup, destination)
        _fsync_directory(parent)
    elif not had_destination and (destination.exists() or destination.is_symlink()):
        if failed.exists() or failed.is_symlink():
            _remove_path(failed)
        os.replace(destination, failed)
        _fsync_directory(parent)
    elif had_destination and not (destination.exists() or destination.is_symlink()):
        raise CampaignRunError(
            "pending publication cannot restore its missing destination"
        )
    value["phase"] = "rolled_back"
    value["recorded_at"] = utc_now()
    receipt = {name: value[name] for name in _PUBLICATION_RECEIPT_FIELDS}
    atomic_write_json(run_dir / "publication.json", receipt)
    atomic_write_json(pending, value)
    try:
        verify_evidence_for_repair(
            run_dir, permitted_paths=_PUBLICATION_EVIDENCE_RECEIPTS
        )
    except (OSError, TypeError, ValueError) as exc:
        raise CampaignRunError(f"cannot repair publication evidence: {exc}") from exc
    for path in (staging, backup, failed):
        if path.exists() or path.is_symlink():
            _remove_path(path)
    _fsync_directory(parent)
    refresh_campaign_evidence(run_dir)


def _validate_pending_publication_receipt(value: dict[str, object]) -> None:
    expected_fields = set(_PUBLICATION_RECEIPT_FIELDS) | set(_RECOVERY_FIELDS)
    if set(value) != expected_fields:
        raise CampaignRunError("pending publication receipt has invalid structure")
    if value["schema_version"] != 1:
        raise CampaignRunError("pending publication receipt has invalid schema version")
    for name in ("campaign_id", "run_id", "root", "destination", "recorded_at"):
        if not isinstance(value[name], str) or not value[name]:
            raise CampaignRunError(f"pending publication receipt has invalid {name}")
    for name in ("evidence_sha256", "approved_digest", "sha256"):
        field = value[name]
        if not isinstance(field, str) or _SHA256.fullmatch(field) is None:
            raise CampaignRunError(f"pending publication receipt has invalid {name}")
    source = value["source"]
    if (
        not isinstance(source, dict)
        or set(source) != {"path", "kind"}
        or not isinstance(source["path"], str)
        or not source["path"]
        or source["kind"] not in {"file", "directory"}
    ):
        raise CampaignRunError("pending publication receipt has invalid source")
    preserve = value["preserve"]
    if not isinstance(preserve, list) or not all(
        isinstance(item, str) and item and "/" not in item and item not in {".", ".."}
        for item in preserve
    ):
        raise CampaignRunError("pending publication receipt has invalid preserve")
    preserved_entries = value["preserved_entries"]
    if not isinstance(preserved_entries, list) or any(
        not isinstance(entry, dict)
        or set(entry) != {"path", "type"}
        or not isinstance(entry["path"], str)
        or entry["path"] not in preserve
        or entry["type"] not in {"missing", "file", "directory"}
        for entry in preserved_entries
    ):
        raise CampaignRunError(
            "pending publication receipt has invalid preserved_entries"
        )
    artifacts = value["artifacts"]
    if not isinstance(artifacts, list) or any(
        not isinstance(artifact, dict)
        or set(artifact) != {"path", "sha256", "size"}
        or not isinstance(artifact["path"], str)
        or not artifact["path"]
        or not isinstance(artifact["sha256"], str)
        or _SHA256.fullmatch(artifact["sha256"]) is None
        or not isinstance(artifact["size"], int)
        or isinstance(artifact["size"], bool)
        or artifact["size"] < 0
        for artifact in artifacts
    ):
        raise CampaignRunError("pending publication receipt has invalid artifacts")
    changes = value["changes"]
    if not isinstance(changes, list) or any(
        not isinstance(change, dict)
        or set(change) != {"path", "status"}
        or not isinstance(change["path"], str)
        or not change["path"]
        or change["status"] not in {"added", "unchanged", "modified", "deleted"}
        for change in changes
    ):
        raise CampaignRunError("pending publication receipt has invalid changes")
    if not isinstance(value["phase"], str) or value["phase"] not in {
        "prepared",
        "swapped",
        "committed",
        "rolled_back",
    }:
        raise CampaignRunError("pending publication receipt has invalid phase")
    if not isinstance(value["had_destination"], bool):
        raise CampaignRunError(
            "pending publication receipt has invalid had_destination"
        )
    for name in ("staging", "backup", "failed_destination"):
        if not isinstance(value[name], str) or not value[name]:
            raise CampaignRunError(f"pending publication receipt has invalid {name}")
    canonical = {name: value[name] for name in _CANONICAL_RECEIPT_FIELDS}
    if (
        value["approved_digest"] != value["sha256"]
        or _plan_digest(canonical) != value["sha256"]
    ):
        raise CampaignRunError("pending publication receipt digest is invalid")


def _validate_nonterminal_publication_identity(
    run_dir: Path, value: dict[str, object], campaign: CampaignSpec
) -> None:
    spec = campaign.publish
    if spec is None:
        raise CampaignRunError(
            "pending publication does not match retained configuration"
        )
    source = run_dir / spec.source
    source_kind = (
        "file"
        if source.is_file() and not source.is_symlink()
        else "directory"
        if source.is_dir() and not source.is_symlink()
        else None
    )
    if (
        value["campaign_id"] != campaign.campaign_id
        or value["source"] != {"path": spec.source, "kind": source_kind}
        or value["root"] != str(spec.root)
    ):
        raise CampaignRunError(
            "pending publication plan does not match retained configuration"
        )
    try:
        state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
        evidence_sha256 = digest_file(
            run_dir / "evidence.json", relative_to=run_dir
        ).sha256
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        raise CampaignRunError(
            f"cannot validate pending publication identity: {exc}"
        ) from exc
    if (
        not isinstance(state, dict)
        or state.get("campaign_id") != value["campaign_id"]
        or state.get("run_id") != value["run_id"]
        or evidence_sha256 != value["evidence_sha256"]
    ):
        raise CampaignRunError(
            "pending publication identity does not match retained run"
        )


def _validate_nonterminal_recovery_state(
    destination: Path,
    staging: Path,
    backup: Path,
    failed: Path,
    had_destination: object,
) -> None:
    destination_exists = destination.exists() or destination.is_symlink()
    staging_exists = staging.exists() or staging.is_symlink()
    backup_exists = backup.exists() or backup.is_symlink()
    failed_exists = failed.exists() or failed.is_symlink()
    if not had_destination:
        if (
            backup_exists
            or sum((destination_exists, staging_exists, failed_exists)) != 1
        ):
            raise CampaignRunError(
                "pending publication recovery identity does not match retained paths"
            )
        return
    if backup_exists:
        if not any((destination_exists, staging_exists, failed_exists)):
            raise CampaignRunError(
                "pending publication recovery identity does not match retained paths"
            )
        return
    if not destination_exists or not (staging_exists or failed_exists):
        raise CampaignRunError(
            "pending publication recovery identity does not match retained paths"
        )


def _validate_terminal_publication_receipts(
    run_dir: Path,
    recovery: dict[str, object],
    receipt: dict[str, object],
    phase: object,
) -> None:
    if set(receipt) != set(_PUBLICATION_RECEIPT_FIELDS) or set(recovery) != (
        set(_PUBLICATION_RECEIPT_FIELDS) | set(_RECOVERY_FIELDS)
    ):
        raise CampaignRunError(f"{phase} publication receipt has invalid structure")
    if any(
        receipt[name] != recovery[name]
        for name in _PUBLICATION_RECEIPT_FIELDS
        if name != "recorded_at"
    ):
        raise CampaignRunError(
            f"{phase} publication receipt does not match pending recovery"
        )
    canonical = {name: receipt[name] for name in _CANONICAL_RECEIPT_FIELDS}
    digest = receipt["sha256"]
    if (
        not isinstance(digest, str)
        or _SHA256.fullmatch(digest) is None
        or receipt["approved_digest"] != digest
        or _plan_digest(canonical) != digest
    ):
        raise CampaignRunError(f"{phase} publication receipt digest is invalid")
    evidence_sha256 = receipt["evidence_sha256"]
    evidence_matches_prior = (
        isinstance(evidence_sha256, str)
        and digest_file(run_dir / "evidence.json", relative_to=run_dir).sha256
        == evidence_sha256
    )
    if not evidence_matches_prior:
        try:
            verify_evidence_index(run_dir)
        except (OSError, TypeError, ValueError) as exc:
            raise CampaignRunError(
                f"{phase} publication receipt does not bind the prior evidence index"
            ) from exc


def _verify_terminal_publication_evidence(run_dir: Path) -> bool:
    try:
        verify_evidence_index(run_dir)
    except (OSError, TypeError, ValueError):
        try:
            verify_evidence_for_repair(
                run_dir, permitted_paths=_PUBLICATION_EVIDENCE_RECEIPTS
            )
        except (OSError, TypeError, ValueError) as exc:
            raise CampaignRunError(
                f"cannot repair publication evidence: {exc}"
            ) from exc
        return True
    return False


def _plan_publication_locked(run_dir: Path) -> PublicationPlan:
    _recover_pending_publication(run_dir)
    if campaign_status(run_dir) != "complete":
        raise CampaignRunError("only a complete campaign run can be published")
    try:
        verified = verify_evidence_index(run_dir)
    except (OSError, TypeError, ValueError) as exc:
        raise CampaignRunError(f"campaign evidence verification failed: {exc}") from exc
    indexed = {artifact.path: artifact for artifact in verified}
    if "state.json" not in indexed:
        raise CampaignRunError("campaign evidence does not index retained state")
    resolved_path = campaign_resolved_for_run(run_dir)
    try:
        resolved_relative = resolved_path.relative_to(run_dir).as_posix()
    except ValueError as exc:
        raise CampaignRunError("resolved campaign escapes the retained run") from exc
    if resolved_relative not in indexed:
        raise CampaignRunError(
            "campaign evidence does not index resolved configuration"
        )
    campaign = CampaignSpec.load_resolved(resolved_path)
    spec = campaign.publish
    if spec is None:
        raise CampaignRunError("retained campaign has no publish configuration")
    campaign_id, run_id, evidence_sha256 = _verify_evidence_identity(
        run_dir, campaign, indexed
    )
    source = _resolve_run_source(run_dir, spec)
    preserved_entries = _validate_publication_paths(run_dir, source, spec)
    artifacts = _publication_artifacts(run_dir, source, indexed)
    changes = _publication_changes(source, spec, artifacts)
    source_relative = source.relative_to(run_dir).as_posix()
    source_kind = "file" if source.is_file() else "directory"
    draft = PublicationPlan(
        run_dir=run_dir,
        campaign_id=campaign_id,
        run_id=run_id,
        evidence_sha256=evidence_sha256,
        source=source,
        source_relative=source_relative,
        source_kind=source_kind,
        root=spec.root,
        destination=spec.destination,
        preserve=spec.preserve,
        preserved_entries=preserved_entries,
        artifacts=artifacts,
        changes=changes,
        digest="",
    )
    return PublicationPlan(
        run_dir=draft.run_dir,
        campaign_id=draft.campaign_id,
        run_id=draft.run_id,
        evidence_sha256=draft.evidence_sha256,
        source=draft.source,
        source_relative=draft.source_relative,
        source_kind=draft.source_kind,
        root=draft.root,
        destination=draft.destination,
        preserve=draft.preserve,
        preserved_entries=draft.preserved_entries,
        artifacts=draft.artifacts,
        changes=draft.changes,
        digest=_plan_digest(draft.canonical_dict()),
    )


def _validated_run_dir(value: Path) -> Path:
    candidate = value.expanduser().absolute()
    _reject_symlink_ancestry(candidate, "campaign run")
    resolved = candidate.resolve()
    if not resolved.is_dir():
        raise CampaignRunError(f"campaign run is not a directory: {resolved}")
    return resolved


def _verify_evidence_identity(
    run_dir: Path, campaign: CampaignSpec, indexed: dict[str, Artifact]
) -> tuple[str, str, str]:
    try:
        evidence = json.loads((run_dir / "evidence.json").read_text(encoding="utf-8"))
        state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignRunError(f"cannot read campaign identity: {exc}") from exc
    if not isinstance(evidence, dict) or not isinstance(state, dict):
        raise CampaignRunError("campaign evidence or state has invalid structure")
    if evidence.get("status") != "complete":
        raise CampaignRunError("campaign evidence is not for a complete run")
    campaign_id = state.get("campaign_id")
    run_id = state.get("run_id")
    if (
        campaign_id != campaign.campaign_id
        or evidence.get("campaign_id") != campaign_id
    ):
        raise CampaignRunError("campaign evidence belongs to a different campaign")
    if not isinstance(run_id, str) or not run_id:
        raise CampaignRunError("retained state has no run ID")
    state_artifact = indexed["state.json"]
    if digest_file(run_dir / "state.json", relative_to=run_dir) != state_artifact:
        raise CampaignRunError("retained state does not match campaign evidence")
    evidence_sha256 = digest_file(run_dir / "evidence.json", relative_to=run_dir).sha256
    return campaign_id, run_id, evidence_sha256


def _resolve_run_source(run_dir: Path, spec: PublishSpec) -> Path:
    candidate = run_dir / spec.source
    _reject_symlink_ancestry(candidate, "publication source", stop=run_dir)
    source = candidate.resolve()
    try:
        source.relative_to(run_dir)
    except ValueError as exc:
        raise CampaignRunError("publication source escapes the retained run") from exc
    if not source.exists():
        raise CampaignRunError(f"publication source is missing: {spec.source}")
    mode = source.stat(follow_symlinks=False).st_mode
    if not stat.S_ISREG(mode) and not stat.S_ISDIR(mode):
        raise CampaignRunError(f"publication source is unsupported: {spec.source}")
    if stat.S_ISREG(mode) and spec.preserve:
        raise CampaignRunError("publish.preserve requires a directory source")
    return source


def _validate_publication_paths(
    run_dir: Path, source: Path, spec: PublishSpec
) -> tuple[tuple[str, str], ...]:
    root = spec.root.absolute()
    destination = spec.destination.absolute()
    _reject_symlink_ancestry(root, "publish root")
    if not root.is_dir():
        raise CampaignRunError(f"publish root is not a directory: {root}")
    try:
        relative = destination.relative_to(root)
    except ValueError as exc:
        raise CampaignRunError("publication destination escapes publish root") from exc
    if not relative.parts:
        raise CampaignRunError(
            "publication destination must be strictly below publish root"
        )
    _reject_symlink_ancestry(destination, "publication destination", stop=root)
    if _paths_overlap(destination, run_dir) or _paths_overlap(destination, source):
        raise CampaignRunError(
            "publication destination overlaps the retained run or source"
        )
    if destination.parent == source or source.parent == destination:
        raise CampaignRunError("publication source and destination are not disjoint")
    return _validate_destination_entries(destination, spec.preserve)


def _paths_overlap(left: Path, right: Path) -> bool:
    try:
        left.relative_to(right)
        return True
    except ValueError:
        pass
    try:
        right.relative_to(left)
        return True
    except ValueError:
        return False


def _reject_symlink_ancestry(
    path: Path, label: str, *, stop: Path | None = None
) -> None:
    current = path
    chain: list[Path] = []
    while True:
        chain.append(current)
        if stop is not None and current == stop:
            break
        if current == current.parent:
            break
        current = current.parent
    for entry in reversed(chain):
        try:
            mode = entry.lstat().st_mode
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(mode):
            raise CampaignRunError(f"{label} has symlink ancestry: {entry}")


def _publication_artifacts(
    run_dir: Path, source: Path, indexed: dict[str, Artifact]
) -> tuple[Artifact, ...]:
    files: tuple[Path, ...]
    relative_to: Path
    if source.is_file():
        files = (source,)
        relative_to = source.parent
    else:
        files = tuple(_regular_tree_files(source, "publication source"))
        relative_to = source
    artifacts: list[Artifact] = []
    for path in files:
        run_relative = path.relative_to(run_dir).as_posix()
        indexed_artifact = indexed.get(run_relative)
        if indexed_artifact is None:
            raise CampaignRunError(
                f"publication source contains an unindexed file: {run_relative}"
            )
        observed = digest_file(path, relative_to=run_dir)
        if observed != indexed_artifact:
            raise CampaignRunError(
                f"publication source changed after evidence verification: {run_relative}"
            )
        artifacts.append(digest_file(path, relative_to=relative_to))
    return tuple(sorted(artifacts, key=lambda artifact: artifact.path))


def _publication_changes(
    source: Path, spec: PublishSpec, artifacts: tuple[Artifact, ...]
) -> tuple[tuple[str, str], ...]:
    """Describe the exact add/modify/delete set approved for publication."""

    source_by_path = {artifact.path: artifact for artifact in artifacts}
    destination = spec.destination
    destination_by_path: dict[str, Artifact] = {}
    if destination.is_file() and not destination.is_symlink():
        destination_by_path[source.name] = digest_file(
            destination, relative_to=destination.parent
        )
    elif destination.is_dir() and not destination.is_symlink():
        destination_by_path = {
            artifact.path: artifact
            for artifact in (
                digest_file(path, relative_to=destination)
                for path in _regular_tree_files(destination, "publication destination")
            )
            if PurePosixPath(artifact.path).parts[0] not in spec.preserve
        }
    changes: list[tuple[str, str]] = []
    for path, artifact in sorted(source_by_path.items()):
        prior = destination_by_path.get(path)
        status = (
            "added"
            if prior is None
            else "unchanged"
            if prior.sha256 == artifact.sha256 and prior.size == artifact.size
            else "modified"
        )
        changes.append((path, status))
    changes.extend(
        (path, "deleted")
        for path in sorted(destination_by_path.keys() - source_by_path.keys())
    )
    return tuple(changes)


def _plan_digest(payload: dict[str, object]) -> str:
    encoded = json.dumps(
        payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _regular_tree_files(root: Path, label: str) -> list[Path]:
    files: list[Path] = []
    for current, directories, names in os.walk(root, topdown=True, followlinks=False):
        current_path = Path(current)
        kept: list[str] = []
        for name in sorted(directories):
            path = current_path / name
            mode = path.lstat().st_mode
            if stat.S_ISLNK(mode):
                raise CampaignRunError(f"{label} contains a symlink: {path}")
            if not stat.S_ISDIR(mode):
                raise CampaignRunError(f"{label} contains a special entry: {path}")
            kept.append(name)
        directories[:] = kept
        for name in sorted(names):
            path = current_path / name
            mode = path.lstat().st_mode
            if not stat.S_ISREG(mode):
                kind = "symlink" if stat.S_ISLNK(mode) else "special entry"
                raise CampaignRunError(f"{label} contains a {kind}: {path}")
            files.append(path)
    return files


def _publish_locked(plan: PublicationPlan) -> None:
    destination = plan.destination
    destination.parent.mkdir(parents=True, exist_ok=True)
    _validate_preservation_matches_plan(plan)
    token = secrets.token_hex(6)
    staging = destination.parent / f".{destination.name}.publish-{token}"
    backup = destination.parent / f".{destination.name}.previous-{token}"
    failed = destination.parent / f".{destination.name}.failed-{token}"
    recovery_path = plan.run_dir / "publication.pending.json"
    swap_started = False
    swapped = False
    had_destination = destination.exists() or destination.is_symlink()
    commit_durable = False
    primary_error: BaseException | None = None
    try:
        _verify_source_matches_plan(plan)
        _copy_exact_plan(plan, staging)
        _verify_staging_matches_plan(plan, staging)
        _ensure_preserve_disjoint(plan, staging)
        _fsync_staging(plan, staging)
        recovery = _receipt(plan, phase="prepared")
        recovery.update(
            {
                "staging": str(staging),
                "backup": str(backup),
                "failed_destination": str(failed),
                "had_destination": had_destination,
            }
        )
        atomic_write_json(recovery_path, recovery)
        swap_started = True
        _validate_preservation_matches_plan(plan)
        _swap_prepared(plan, staging, backup, had_destination)
        swapped = True
        recovery["phase"] = "swapped"
        atomic_write_json(recovery_path, recovery)
        atomic_write_json(
            plan.run_dir / "publication.json", _receipt(plan, phase="committed")
        )
        recovery["phase"] = "committed"
        atomic_write_json(recovery_path, recovery)
        commit_durable = True
        refresh_campaign_evidence(plan.run_dir)
        if backup.exists() or backup.is_symlink():
            try:
                _remove_path(backup)
                _fsync_directory(backup.parent)
            except OSError:
                # The committed recovery receipt makes a retained backup harmless.
                pass
    except BaseException as exc:
        primary_error = exc
        try:
            if (
                not commit_durable
                and swap_started
                and (
                    swapped
                    or backup.exists()
                    or backup.is_symlink()
                    or (
                        not had_destination
                        and (destination.exists() or destination.is_symlink())
                    )
                )
            ):
                _rollback_swap(plan, staging, backup, failed, had_destination)
                recovery = _receipt(plan, phase="rolled_back")
                recovery.update(
                    {
                        "staging": str(staging),
                        "backup": str(backup),
                        "failed_destination": str(failed),
                        "had_destination": had_destination,
                    }
                )
                atomic_write_json(
                    plan.run_dir / "publication.json",
                    _receipt(plan, phase="rolled_back"),
                )
                atomic_write_json(recovery_path, recovery)
        except Exception as recovery_exc:  # noqa: BLE001
            exc.add_note(f"publication rollback also failed: {recovery_exc}")
        raise
    finally:
        try:
            if staging.exists() or staging.is_symlink():
                _remove_path(staging)
        except BaseException as cleanup_exc:
            if primary_error is not None:
                primary_error.add_note(
                    f"publication staging cleanup also failed: {cleanup_exc}"
                )
            else:
                raise


def _receipt(plan: PublicationPlan, *, phase: str) -> dict[str, object]:
    return {
        **plan.to_dict(),
        "sha256": plan.digest,
        "phase": phase,
        "recorded_at": utc_now(),
    }


def _verify_source_matches_plan(plan: PublicationPlan) -> None:
    observed = _source_artifacts(plan.source)
    if observed != plan.artifacts:
        raise CampaignRunError("publication source changed after planning")


def _source_artifacts(source: Path) -> tuple[Artifact, ...]:
    files: tuple[Path, ...]
    if source.is_file():
        files = (source,)
        relative_to = source.parent
    elif source.is_dir():
        files = tuple(_regular_tree_files(source, "publication source"))
        relative_to = source
    else:
        raise CampaignRunError("publication source changed after planning")
    return tuple(
        sorted(
            (digest_file(path, relative_to=relative_to) for path in files),
            key=lambda artifact: artifact.path,
        )
    )


def _copy_exact_plan(plan: PublicationPlan, staging: Path) -> None:
    if plan.source_kind == "file":
        if len(plan.artifacts) != 1:
            raise CampaignRunError("file publication plan has invalid artifacts")
        _copy_regular_file(plan.source, staging)
        return
    staging.mkdir()
    for artifact in plan.artifacts:
        source = plan.source / artifact.path
        target = staging / artifact.path
        target.parent.mkdir(parents=True, exist_ok=True)
        _copy_regular_file(source, target)


def _copy_regular_file(source: Path, target: Path) -> None:
    mode = source.lstat().st_mode
    if not stat.S_ISREG(mode):
        raise CampaignRunError(
            f"publication source entry is no longer regular: {source}"
        )
    shutil.copyfile(source, target, follow_symlinks=False)


def _fsync_staging(plan: PublicationPlan, staging: Path) -> None:
    if plan.source_kind == "file":
        _fsync_regular_file(staging)
        _fsync_directory(staging.parent)
        return
    directories = {staging}
    for artifact in plan.artifacts:
        staged_file = staging / artifact.path
        _fsync_regular_file(staged_file)
        parent = staged_file.parent
        while parent != staging:
            directories.add(parent)
            parent = parent.parent
    for directory in sorted(
        directories, key=lambda path: len(path.relative_to(staging).parts), reverse=True
    ):
        _fsync_directory(directory)
    _fsync_directory(staging.parent)


def _fsync_regular_file(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        mode = os.fstat(descriptor).st_mode
        if not stat.S_ISREG(mode):
            raise CampaignRunError(f"staged publication entry is not regular: {path}")
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _verify_staging_matches_plan(plan: PublicationPlan, staging: Path) -> None:
    artifacts: tuple[Artifact, ...]
    if plan.source_kind == "file":
        if not staging.is_file() or staging.is_symlink():
            raise CampaignRunError("staged publication is not a regular file")
        expected = plan.artifacts[0]
        actual = digest_file(staging, relative_to=staging.parent)
        observed = Artifact(expected.path, actual.sha256, actual.size)
        artifacts = (observed,)
    else:
        artifacts = tuple(
            sorted(
                (
                    digest_file(path, relative_to=staging)
                    for path in _regular_tree_files(staging, "staged publication")
                ),
                key=lambda artifact: artifact.path,
            )
        )
    if artifacts != plan.artifacts:
        raise CampaignRunError("staged publication bytes do not match approved plan")


def _validate_destination_entries(
    destination: Path, preserve: tuple[str, ...]
) -> tuple[tuple[str, str], ...]:
    try:
        destination_mode = destination.lstat().st_mode
    except FileNotFoundError:
        return tuple((name, "missing") for name in preserve)
    if stat.S_ISLNK(destination_mode):
        raise CampaignRunError(f"publication destination is a symlink: {destination}")
    if stat.S_ISREG(destination_mode):
        if preserve:
            raise CampaignRunError("publish.preserve requires a directory destination")
        return ()
    if not stat.S_ISDIR(destination_mode):
        raise CampaignRunError(f"publication destination is unsupported: {destination}")
    for current, directories, names in os.walk(
        destination, topdown=True, followlinks=False
    ):
        current_path = Path(current)
        kept: list[str] = []
        for name in sorted(directories):
            child = current_path / name
            mode = child.lstat().st_mode
            if stat.S_ISLNK(mode):
                raise CampaignRunError(
                    f"publication destination contains a symlink: {child}"
                )
            if not stat.S_ISDIR(mode):
                raise CampaignRunError(
                    f"publication destination contains a special entry: {child}"
                )
            kept.append(name)
        directories[:] = kept
        for name in sorted(names):
            child = current_path / name
            mode = child.lstat().st_mode
            if not stat.S_ISREG(mode):
                kind = "symlink" if stat.S_ISLNK(mode) else "special entry"
                raise CampaignRunError(
                    f"publication destination contains a {kind}: {child}"
                )
    entries: list[tuple[str, str]] = []
    for name in preserve:
        path = destination / name
        try:
            mode = path.lstat().st_mode
        except FileNotFoundError:
            entry_type = "missing"
        else:
            entry_type = "file" if stat.S_ISREG(mode) else "directory"
        entries.append((name, entry_type))
    return tuple(entries)


def _validate_preservation_matches_plan(plan: PublicationPlan) -> None:
    observed = _validate_publication_paths(
        plan.run_dir,
        plan.source,
        PublishSpec(plan.source_relative, plan.root, plan.destination, plan.preserve),
    )
    if observed != plan.preserved_entries:
        raise CampaignRunError(
            "preserved destination entry type changed after planning"
        )


def _ensure_preserve_disjoint(plan: PublicationPlan, staging: Path) -> None:
    if plan.source_kind != "directory":
        return
    for name in plan.preserve:
        target = staging / name
        if target.exists() or target.is_symlink():
            raise CampaignRunError(
                f"publication source conflicts with preserved destination entry: {name}"
            )


def _swap_prepared(
    plan: PublicationPlan, staging: Path, backup: Path, had_destination: bool
) -> None:
    destination = plan.destination
    if had_destination:
        os.replace(destination, backup)
        _fsync_directory(destination.parent)
        if plan.source_kind == "directory":
            _move_preserved(backup, staging, plan.preserve)
    os.replace(staging, destination)
    _fsync_directory(destination.parent)


def _move_preserved(
    source_root: Path, target_root: Path, names: tuple[str, ...]
) -> None:
    for name in names:
        source = source_root / name
        if not source.exists() and not source.is_symlink():
            continue
        target = target_root / name
        if target.exists() or target.is_symlink():
            raise CampaignRunError(
                f"publication source conflicts with preserved destination entry: {name}"
            )
        os.replace(source, target)
    _fsync_directory(source_root)
    _fsync_directory(target_root)


def _rollback_swap(
    plan: PublicationPlan,
    staging: Path,
    backup: Path,
    failed: Path,
    had_destination: bool,
) -> None:
    destination = plan.destination
    preserved_source = staging
    if destination.exists() or destination.is_symlink():
        os.replace(destination, failed)
        preserved_source = failed
    if had_destination:
        if not (backup.exists() or backup.is_symlink()):
            raise CampaignRunError(
                f"publication rollback requires retained backup: {backup}"
            )
        if plan.source_kind == "directory":
            _move_preserved(preserved_source, backup, plan.preserve)
        os.replace(backup, destination)
    _fsync_directory(destination.parent)


def _remove_path(path: Path) -> None:
    if path.is_symlink() or path.is_file():
        path.unlink(missing_ok=True)
    elif path.is_dir():
        shutil.rmtree(path)


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
