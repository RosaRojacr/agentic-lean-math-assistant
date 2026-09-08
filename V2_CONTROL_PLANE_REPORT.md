# Agentic Lean Math Assistant v2 — control-plane research and implementation decision

**Date:** 2026-08-26  
**Scope:** native v2 control state, durable artifact authority, crash recovery, and Linux execution isolation  
**Relationship to the main report:** this is the implementation-level addendum to `V2_RESEARCH_REPORT.md`. It narrows Sections 5.3–5.6, 10, 11, and migration Phases 1–4. Where it differs, this report is the pre-implementation decision.

---

## 1. Executive decision

Build one deterministic controller around four explicit boundaries:

1. **Pure control:** Python immutable contracts and a pure reducer. Model the critical protocols in TLA+/PlusCal. Require exhaustive TLC runs on small finite configurations. Use Apalache as a secondary bounded/symbolic checker, not the sole gate. Use Hypothesis state machines to check the implementation against the abstract actions.
2. **Durable authority:** a small Rust platform helper implementing an immutable SHA-256 object store and one atomically replaced `HEAD` pointer per run. Events and referenced artifacts are durable before `HEAD` moves. Human JSON, JSONL, SQLite indexes, dashboards, and workspace paths are projections.
3. **Artifact identity:** make the required `{mediaType, digest, size}` portion of `ArtifactRefV2` structurally compatible with an OCI content descriptor. Keep v2 provenance, schema, contract, input-root, execution-attestation, and assurance bindings in the enclosing typed record. Move the locator out of durable identity.
4. **Execution isolation:** use a root-owned, narrowly scoped sandbox broker that starts transient systemd services. Each untrusted attempt gets a dynamic UID, private namespaces, cgroup-v2 limits, no capabilities, `NoNewPrivileges`, a release seccomp allowlist, read-only materialized inputs, one bounded writable attempt root, no network, and no inherited secrets. Landlock is defense in depth. A rootless systemd/bubblewrap profile is a developer backend, not an automatic equivalent.

The first native slice is deliberately narrow:

```text
immutable import
→ deterministic command
→ Lean verification
→ continuation gate
→ evidence commit
→ injected crash
→ recovery and replay
```

It has **no model-provider network, no API secret, no Herdr dependency, and no concurrent scheduler**. This is not a shortcut. It isolates the control-plane claims before adding the two hardest trust problems: secret-bearing model clients and concurrent side effects.

### 1.1 Decisions that should be frozen now

| Question | Decision | Reason |
|---|---|---|
| Formal verification or implementation tests only? | TLA+/TLC **and** model-based implementation tests | The former checks the protocol design; the latter checks whether code implements it. Neither subsumes the other. |
| TLC or Apalache? | TLC is the required finite-state gate; Apalache is a secondary bounded/symbolic check | TLC is mature and checks finite safety and liveness; Apalache documents bounded finite executions and describes itself as experimental.[R1][R2] |
| Mutable JSONL as authority? | No | An interrupted append, duplicate line, or projection corruption must not alter run authority. |
| SQLite as primary authority? | No for the first release | SQLite is robust, but it does not remove external-blob ordering or safe-path requirements. The workload needs one serialized mutable pointer per run, not relational transactions. Use SQLite only as a rebuildable query index if later measurements justify it. |
| Pure Python filesystem implementation? | No for the authority path | Python does not expose the complete `openat2`/`renameat2` protocol cleanly. A small typed helper makes the syscall and failpoint boundary inspectable. |
| OCI image semantics internally? | No | Reuse OCI descriptor and blob-layout concepts, not image layers, mutable tags, or container-image meaning.[R4][R5] |
| `chroot` as a sandbox? | Never | The Linux manual explicitly says it changes pathname resolution only and is not intended as a security sandbox.[R15] |
| Custom namespace/seccomp runtime? | Not initially | Reimplementing a container supervisor is larger and riskier than using systemd/cgroup primitives through a constrained broker. |
| Silent sandbox fallback? | Never | Every launch must satisfy a named capability profile or fail before side effects. |
| Networked agent in the first slice? | No | Provider credentials and untrusted tool execution need a brokered split; they must not be smuggled into the deterministic slice. |

---

## 2. Observed workstation baseline

The following facts were measured during this research session:

- authority candidate filesystem: `ext4`, mounted `rw,relatime,seclabel`;
- systemd: `259`, built with `+SECCOMP`;
- cgroup v2 controllers visible: `cpuset cpu io memory hugetlb pids rdma misc dmem`;
- unprivileged user namespaces: a root-mapped `unshare` probe succeeded;
- installed isolation runtimes: `bwrap`, `crun`, `podman`, and `systemd-run`; `runc` was not found;
- a transient user service with `MemoryMax`/`TasksMax` succeeded;
- a transient user service combining `PrivateUsers`, `PrivateNetwork`, `PrivateDevices`, `ProtectSystem=strict`, `NoNewPrivileges`, `MemoryMax`, and `TasksMax` also succeeded.

These probes establish availability, not security equivalence. systemd documents that some sandbox settings are gracefully disabled when kernel or manager support is unavailable.[R13] The production launcher must inspect and test the **effective** isolation inside the launched unit.

### 2.1 Initial support declaration

The first authority store should support only:

```text
OS:             Linux
filesystem:     local ext4 on the observed mount
writer scope:   one local trusted principal; cooperating controller processes
lock scope:     local kernel OFD locks
sandbox:        systemd system manager through the installed broker
network policy: none
```

NFS, FUSE, overlay-backed authority roots, cross-host writers, remote object stores, and other local filesystems remain unsupported until their crash and lock matrices pass. Do not infer support because their APIs look POSIX-like.

---

## 3. Trust and failure model

### 3.1 Trusted components

The first release trusts:

- the Linux kernel, systemd system manager, selected local filesystem, storage device flush behavior, and the machine administrator;
- the native v2 controller and pure reducer;
- the Rust store/platform helper;
- the root-owned sandbox broker and fixed sandbox profiles;
- pinned executables/toolchains to behave according to their declared role, while still containing their process and resource effects;
- the local store owner not to rewrite the entire store maliciously.

Hashes establish consistency, immutable identity, lineage, and replay binding inside this scope. They do not establish authenticity against root or the store owner. That remains an explicit `authenticity_status = NOT_ESTABLISHED` condition.

### 3.2 Untrusted inputs

Treat all of these as untrusted:

- model output and model-proposed commands;
- playbook-supplied relative paths and filenames;
- imported source trees and archives;
- workspace contents created by a child process;
- stdout/stderr volume and encoding;
- child exit status and self-reported completion;
- stale PIDs, stale workspaces, and retained locator strings;
- any sandbox property that was requested but not observed effective.

### 3.3 Failures in scope

The design must recover or fail closed on:

- controller/helper death at every durable-write boundary;
- partial and short writes, `EINTR`, `ENOSPC`, and surfaced `EIO`;
- crash before or after file sync, object installation, directory sync, and `HEAD` replacement;
- two cooperating controllers attempting the same or different transition;
- repeated idempotency keys;
- stale expected heads;
- object/predecessor corruption;
- child fork bombs, resistant descendants, output floods, memory exhaustion, and wall timeout;
- traversal, symlink, magic-link, mount-crossing, special-file, and parent-swap attacks;
- unavailable sandbox capabilities;
- recovery after the caller cannot know whether a commit completed.

### 3.4 Failures outside the initial claim

The first release does not claim to survive:

- malicious kernel, root, firmware, or storage-controller behavior;
- a storage stack that reports successful `fsync` without satisfying its documented contract;
- undetected arbitrary bit corruption after successful writes;
- a malicious local principal able to rewrite all objects and all heads;
- remote multiwriter partitions or Byzantine storage;
- safe domain-allowlisted network egress;
- a kernel escape from the chosen namespace/seccomp/LSM stack.

The report must say this plainly in the product status. “Content addressed” and “sandboxed” are not synonyms for authenticity and VM-grade isolation.

---

## 4. Concrete implementation choices

### 4.1 Control language boundary

| Option | Advantages | Load-bearing weakness | Disposition |
|---|---|---|---|
| Pure Python | Reuses the project, quick schema/reducer work, good Hypothesis support | Exact Linux path/open/install primitives and syscall-level failpoints are awkward; accidental path-string APIs remain easy to call | Use for contracts, reducer, scheduler, assurance, and facade; not for authority filesystem primitives |
| Full Rust rewrite | Strong types and direct syscall control everywhere | Rewrites orchestration and research logic that Python already handles well; delays the vertical slice | Reject |
| Python controller + narrow Rust helper | Keeps pure policy readable; makes safe opens, durable writes, locks, and failpoints a small auditable surface | Adds a build and IPC/FFI boundary | **Selected** |

The helper API must be coarse grained. Do not expose a generic “open this path” syscall wrapper. Initial operations:

```text
create_run(run_id, genesis_event_bytes)
put_object(expected_media_type, bounded_input_fd)
read_verified_object(artifact_identity)
commit_event(run_id, expected_head, event_bytes, request_digest, idempotency_key)
recover_run(run_id)
materialize_snapshot(snapshot_ref, destination_capability)
```

A subprocess protocol is safer to bootstrap than a large native extension: helper crashes are contained, failpoints can terminate the helper, and request/response receipts are explicit. Use inherited file descriptors for byte streams; never send arbitrary authority-root paths over the protocol. If process-launch overhead later matters, measure before replacing it with PyO3 or a daemon.

### 4.2 Metadata store

| Option | What it solves | What remains | Decision |
|---|---|---|---|
| Filesystem CAS + per-run `HEAD` | Natural immutable blobs; transparent recovery; one simple linearization point; easy offline inspection | Correct write/sync/install protocol must be implemented and tested | **Primary authority** |
| SQLite rollback/WAL metadata + external blobs | Mature transaction and locking implementation | External blobs still need safe paths and blob-before-row ordering; database becomes a second authority/recovery format | Do not use as primary in the first release |
| All bytes in SQLite | Single transactional file for head/events/blobs | Poor fit for very large streams/workspaces; database extraction becomes required for every tool input; still needs safe publication paths | Reject |
| LMDB/other embedded KV | Single writer and ordered KV semantics | New dependency and recovery model without removing external workspace/security work | Reject initially |

SQLite’s atomic-commit design is strong and explicitly reasons about flushes, journals, reordering, and power loss.[R9] It remains a valid future alternative if measurements show head contention or query/index cost. It is not selected merely because “databases are safer”: the v2 authority operation is intentionally one immutable-object graph plus one mutable pointer.

### 4.3 Sandbox backend

| Option | Strength | Weakness | Decision |
|---|---|---|---|
| systemd system transient service through constrained broker | Dynamic UID, cgroup lifecycle/resources, namespaces, capabilities, seccomp, credentials, unit identity, group kill; already installed | Requires root-owned broker and installation policy; some properties can degrade silently without verification | **Production backend** |
| Rootless systemd user service | Available now; cgroup limits and namespaces probed | User manager inherits its environment; same-host-UID boundary is weaker; manager delegation varies | Developer backend only; launch through `env -i`; never auto-promote |
| bubblewrap | Explicit empty mount namespace, user/PID/network/IPC namespaces, seccomp input; installed | It is a sandbox construction tool, not a complete policy or resource manager; policy quality is entirely in its arguments.[R16] | Optional rootless filesystem backend, paired with cgroups and the same capability contract |
| OCI runtime (`crun`) | Standard namespace/cgroup/capability/seccomp schema; installed; supports pinned rootfs | Rootfs/image lifecycle and runtime integration add substantial first-slice work | Strong candidate for later portable backend, not initial |
| Hand-built clone/unshare/mount/seccomp launcher | Exact control | Creates a new container runtime and a large privileged attack surface | Reject |
| VM/Firecracker | Separate kernel boundary | Heavy image, boot, toolchain, and device integration | Reserve for later high-risk profiles |

OCI runtime configuration usefully enumerates namespaces, cgroups, capabilities, LSMs, filesystems, and devices.[R17] It is a future backend contract, not proof that every runtime enforces an identical profile.

---

## 5. Formal control model

### 5.1 Decision: not model-based testing only

TLC explicitly checks safety and liveness properties of executable TLA+ specifications by state exploration.[R1] Apalache translates a TLA+ problem to SMT constraints, but its documentation limits analysis to fixed finite parameters/data and bounded finite executions and calls the tool experimental.[R2] Hypothesis stateful testing generates action sequences against real implementation state and shrinks failures.[R3]

Use all three at different boundaries:

| Layer | Required tool | Question answered |
|---|---|---|
| Protocol design | TLA+/PlusCal + TLC | Does any bounded interleaving/crash violate the invariant? |
| Additional symbolic exploration | Apalache | Can a deeper bounded trace or candidate inductive invariant be refuted efficiently? |
| Code conformance | Hypothesis rule-based state machine | Does the Python/Rust implementation match the abstract action/result model? |
| Kernel/filesystem behavior | process-kill and VM power-loss harness | Did the actual syscalls and target filesystem implement the assumed abstract primitives? |

A TLA+ success does not prove the Rust helper, Linux filesystem, or storage hardware. A property test does not prove the abstract protocol if its oracle repeats the implementation’s mistake. The release claim is the intersection.

### 5.2 Keep three small specifications

Do not build one giant campaign model.

```text
formal/RunCommit.tla
formal/AttemptLifecycle.tla
formal/Publication.tla            # Phase 6, not the initial slice
formal/MC_RunCommit.cfg
formal/MC_AttemptLifecycle.cfg
formal/README.txt                 # commands and abstraction mapping
```

`RunCommit.tla` models immutable objects, event predecessors, a volatile/stable namespace, file and directory sync, run lock, expected-head CAS, idempotency, crash, recovery, and projection rebuild.

`AttemptLifecycle.tla` models scheduler claims, launch intent, spawn, terminal receipt, timeout, cancellation, cleanup, output publication, invalidation, and evidence closure.

`Publication.tla` later models approval-bound immutable release roots and one atomic public ref. Do not mix publication into the initial store model.

### 5.3 `RunCommit` abstract state

Use finite tokens, not real hashes or bytes:

```text
VARIABLES
  durableObjects,       \* objects guaranteed stable
  volatileObjects,      \* namespace additions not yet directory-synced
  eventBody,            \* immutable event token -> predecessor/refs/request
  stableHead,           \* run -> event token persisted before crash
  visibleHead,          \* current namespace view
  pendingRename,        \* old/new whole-head alternatives
  lockOwner,            \* run -> controller or None
  committedRequest,     \* (run,idempotency_key) -> request/outcome
  acknowledged,         \* commits for which caller received success
  projection,           \* disposable derived cache
  controllerPhase       \* prepare/lock/swap/sync/ack/recover
```

Filesystem actions should be abstract but not falsely atomic:

```text
WriteObject
FileSync
InstallObject
ObjectDirSync
AcquireRunLock
ReadAndCompareHead
WriteHeadTemp
HeadFileSync
RenameHead
HeadDirSync
Acknowledge
Crash
Recover
RebuildProjection
```

Before `HeadDirSync`, `Crash` may choose the complete old or complete new head; it may not create a torn hybrid. Before `ObjectDirSync`, an installed object may disappear after crash. File sync stabilizes bytes; directory sync stabilizes the directory entry. This mirrors the documented distinction that `fsync(file)` does not necessarily persist the containing directory entry.[R8]

### 5.4 Required safety invariants

Write these as named TLA+ invariants, with a plain-language statement and an implementation assertion for each.

1. **`TypeOK`** — every variable stays in its declared finite domain.
2. **`HeadReferencesDurableEvent`** — every stable/acknowledgeable head resolves to one durable, digest-valid event.
3. **`CommittedRefsAreDurable`** — every artifact reference reachable from a committed event resolves to a durable object.
4. **`LinearHeadChain`** — a committed event’s predecessor is exactly the previous committed head; sequence increases by one.
5. **`OneCommitPerGeneration`** — one run generation never has two committed event identities.
6. **`LockExclusion`** — at most one cooperating controller owns a run’s commit lock.
7. **`CompareBeforeSwap`** — a head moves only from the expected predecessor observed while holding the lock.
8. **`IdempotencyConsistency`** — one `(run_id, idempotency_key)` binds one request digest and one terminal outcome; a different request conflicts.
9. **`AcknowledgedCommitNeverLost`** — an acknowledged event is the current head or an ancestor of it after every future recovery.
10. **`CrashHasWholeHead`** — recovery observes the old valid head or new valid head, never malformed mixed bytes.
11. **`ProjectionHasNoAuthority`** — changing/deleting/corrupting a projection cannot change the reducer result reconstructed from the head.
12. **`BranchIsNotCommit`** — an event object prepared from a stale head may exist as an orphan but is never treated as committed.
13. **`RunIsolation`** — committing run A cannot move run B’s head.
14. **`UnknownCommitOutcomeIsNotSuccess`** — if the final directory sync returns an error or the helper dies before acknowledgement, the caller receives unknown/recovery-required, never committed success.

### 5.5 Attempt lifecycle invariants

1. **`LaunchIntentBeforeSpawn`** — no process exists without a durable launch intent.
2. **`AtMostOneTerminalReceipt`** — an invocation has exactly zero or one terminal receipt.
3. **`TerminalAfterLaunch`** — terminal success/failure/timeout/cancel follows launch intent and, when spawn succeeded, process identity.
4. **`NoPublishBeforeReconcile`** — outputs become artifact refs only after child/cgroup/stream cleanup reconciliation.
5. **`NoChildAfterReturn`** — `ExecutionSupervisor.run` does not return while an owned process or pump remains live.
6. **`BudgetMonotone`** — consumed/reserved budget never becomes available without an explicit release event; hard limits cannot be exceeded by a transition.
7. **`InvalidationClosure`** — changing an upstream dependency marks every transitive dependent result stale before it may contribute evidence.
8. **`FreshEvidenceOnly`** — a committed evidence root contains only validated refs whose dependency fingerprints still match.
9. **`StatusOrthogonality`** — process success cannot imply artifact validity, formal verification, semantic fidelity, mathematical closure, assurance, or publication.
10. **`NoRetryWithoutDecision`** — another attempt requires a durable retry decision and a materially changed method/infrastructure signature.
11. **`NoCapabilityEscalationByWorker`** — a worker result cannot add capabilities to its own or a successor launch.
12. **`DeadlineIsExternal`** — a child cannot extend the supervisor’s monotonic deadline by writing output or changing its clock.

### 5.6 Liveness properties and assumptions

Check only bounded, clearly conditioned liveness:

- under weak fairness, available resources, a non-failing filesystem, and a live controller, a claimed invocation eventually reaches terminal or recovery-required;
- after a crash and restart, every run eventually reaches a valid recovered head or a typed unrecoverable-corruption state;
- cancellation eventually causes the owned cgroup to become empty if the kernel/system manager honors kill/reap operations.

Do not claim “the campaign eventually finishes.” Models and proof tools may legitimately run forever, external services may be unavailable, and mathematical obligations may remain open.

### 5.7 Model configurations

Required TLC configurations should include:

```text
Controllers       = {c1, c2}
Runs              = {r1, r2}
Objects           = {o1, o2, o3}
IdempotencyKeys   = {k1, k2}
MaxSequence       = 3
CrashEnabled      = TRUE
ProjectionFaults  = TRUE
```

Use symmetry sets where sound. Run a second configuration without symmetry for a smaller domain to catch a bad symmetry declaration. Record TLC version, config digest, state count, distinct-state count, depth, and result as an immutable verification receipt.

Apalache checks are secondary:

- bounded invariant checks at increasing lengths;
- candidate inductive invariant checks;
- counterexample comparison against TLC;
- never the only release result.

### 5.8 Refinement/conformance bridge

Every real helper receipt must include a stable `protocol_action` from the abstract action vocabulary. The Hypothesis model consumes the same action/result receipts and maintains the abstract state. Examples:

```text
STORE_OBJECT_WRITTEN       -> WriteObject
STORE_OBJECT_FILE_SYNCED   -> FileSync
STORE_OBJECT_INSTALLED     -> InstallObject
STORE_OBJECT_DIR_SYNCED    -> ObjectDirSync
RUN_LOCK_ACQUIRED          -> AcquireRunLock
RUN_HEAD_RENAMED           -> RenameHead
RUN_HEAD_DIR_SYNCED        -> HeadDirSync
RUN_COMMIT_ACKNOWLEDGED    -> Acknowledge
RUN_RECOVERED              -> Recover
```

These labels are a test/inspection bridge, not authority. Authority remains the verified object/head bytes.

---

## 6. `ArtifactRefV2` and OCI alignment

OCI content descriptors require a content digest, raw byte size, and media type, and are designed to securely reference external content in a Merkle DAG.[R4] OCI image layout places content-addressed blobs at `blobs/<algorithm>/<encoded>` and uses descriptors to reference them.[R5]

Reuse that narrow contract.

### 6.1 Revised durable schema

The earlier report placed `locator` inside `ArtifactRefV2`. Change this before schema freeze. A locator is transport state and cannot be part of durable identity without making relocation change the reference.

```json
{
  "artifact_type": "application/vnd.agentic-lean.artifact-ref.v2+json",
  "schema_version": "2.0.0",
  "namespace": "local.agentic-lean",
  "descriptor": {
    "mediaType": "application/vnd.agentic-lean.run-event.v2+json",
    "digest": "sha256:0123456789abcdef...",
    "size": 1234
  },
  "schema_ref": {
    "name": "RunEventV2",
    "version": "2.0.0",
    "digest": "sha256:..."
  },
  "producer": {
    "run_id": "...",
    "playbook_id": "...",
    "step_id": "...",
    "attempt_id": "...",
    "invocation_id": "..."
  },
  "input_root": "sha256:...",
  "contract_digest": "sha256:...",
  "execution_attestation_digest": "sha256:...",
  "assurance_class": "local_trusted_writer"
}
```

Define a separate ephemeral/projection type:

```text
ResolvedArtifactV2 {
  ref: ArtifactRefV2,
  locator: store capability + derived relative object key
}
```

Rules:

- `descriptor.digest` is always the digest of the exact raw payload bytes, not a digest of a normalized interpretation.
- `descriptor.size` is the exact raw byte count.
- `descriptor.mediaType` is validated at consumption; it is not inferred from a filename.
- `schema_ref.digest` identifies the exact schema bytes used to validate structured content.
- the enclosing ref binds provenance and contract context that OCI descriptors do not provide.
- mutable tags and `index.json` entries are never internal authority.
- OCI export may generate a conforming layout and index, but import/export does not replace the run head.
- do not use OCI image layers, diff IDs, or platform semantics for ordinary research artifacts.

### 6.2 Digest domains

Avoid a misleading “domain-separated blob digest” in the OCI-compatible descriptor. SHA-256 there hashes raw bytes exactly. Type-confusion resistance comes from validating the enclosing typed binding and media/schema fields.

If the system needs a semantic identifier, define a separate field:

```text
semantic_binding_digest = SHA256(
  canonical("agentic-lean/semantic-binding/v2", media_type, schema_ref, payload_digest)
)
```

Never put that value in `descriptor.digest`.

### 6.3 Blob layout

Internal layout:

```text
artifacts-v2/
  STORE-FORMAT                 # immutable format declaration
  blobs/
    sha256/
      <64 lowercase hex>       # exact raw bytes
      .tmp.<128-bit nonce>     # same-directory uncommitted temp
  quarantine/                  # store-level corruption evidence; never auto-reused
```

This is OCI-compatible at the blob-key level. It is not advertised as a full OCI image layout because the internal store has no authoritative OCI `index.json` and may contain crash temps. Exports materialize a clean OCI layout separately.

Object names are derived only from validated algorithm/digest bytes. Callers never supply a blob path.

---

## 7. Crash-safe object protocol

Linux `rename` atomically replaces an existing destination and `renameat2(RENAME_NOREPLACE)` refuses overwrite.[R7] `fsync` flushes file data/metadata but requires a separate directory `fsync` for the directory entry.[R8] Use both facts explicitly.

### 7.1 `put_object`

Preconditions:

- authority root and blob directory are already open as trusted directory file descriptors;
- the request supplies a bounded input FD and declared media type, not a path;
- the helper uses `umask 077`; blobs are created non-executable;
- the configured maximum is enforced while streaming, before any unbounded allocation.

Protocol:

```text
1. openat(blob_dir_fd, ".tmp.<nonce>",
          O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW, 0444)
2. stream with a short-write/EINTR-safe loop
   - hash SHA-256 while writing
   - count exact bytes
   - abort on size limit
3. fsync(temp_fd)
4. verify final byte count and digest; close temp_fd
5. install <digest> without replacement
   - primary: renameat2(..., RENAME_NOREPLACE)
   - compatible fallback: linkat(temp, destination), requiring same filesystem,
     then unlink temp
6. if destination exists:
   - open it through blob_dir_fd with O_NOFOLLOW
   - verify regular-file type, exact size, and full digest
   - identical => deduplicated success
   - mismatch => STORE_CORRUPTION_OR_DIGEST_COLLISION; quarantine/fence writes
7. fsync(blob_dir_fd)
8. return ArtifactRefV2 only after step 7 succeeds
```

Do not use plain `rename` for blob installation: it can overwrite an existing object. Do not use a check-then-create sequence: it races. Do not initially use `O_TMPFILE`; it saves a cleanup name but complicates install/link and recovery paths without changing the core guarantee.

If step 7 returns `EIO` or the helper dies before its durable receipt, the result is `STORE_OUTCOME_UNKNOWN`. Recovery opens and fully verifies the destination. It never guesses from the temp name.

### 7.2 Object reads

```text
1. validate descriptor algorithm, lowercase digest syntax, media type, and size bounds
2. derive the object key internally
3. open relative to blob_dir_fd with O_RDONLY|O_CLOEXEC|O_NOFOLLOW
4. fstat: require regular file and exact size
5. stream/hash exact bytes; reject growth, shrink, or trailing data
6. fstat again when importing from a mutable source
7. compare digest in constant time
8. return an FD/capability, not a trusted pathname
```

Inside the private immutable store, owner mutation is out of the first threat model, but every evidence/publication trust crossing still revalidates. File mode `0444` is operational hygiene, not tamper proof against the owner.

### 7.3 Run creation

Run IDs use one generated, strict identifier grammar and are never paths.

```text
1. mkdirat(runs_root_fd, run_id, 0700); reject collision
2. fsync(runs_root_fd)
3. open new run directory with O_DIRECTORY|O_NOFOLLOW
4. create stable `lock` inode; never rename or delete it
5. durably put the genesis event and all referenced objects
6. write/sync/install initial HEAD
7. fsync(run_dir_fd)
```

If creation crashes before the initial head becomes durable, recovery classifies the directory as `INCOMPLETE_RUN_CREATION`; it does not synthesize a genesis event.

---

## 8. Commit-head concurrency and atomicity

### 8.1 Head format

`HEAD` is a small canonical JSON pointer:

```json
{
  "artifact_type": "application/vnd.agentic-lean.run-head.v2+json",
  "schema_version": "2.0.0",
  "run_id": "...",
  "sequence": 17,
  "event": {
    "mediaType": "application/vnd.agentic-lean.run-event.v2+json",
    "digest": "sha256:...",
    "size": 2048
  }
}
```

The referenced event contains:

- exact predecessor event descriptor or explicit genesis;
- sequence;
- transition kind;
- actor/controller version;
- implementation/policy/playbook digests;
- request digest and idempotency key;
- all input/output refs;
- previous and next pure-state root digests;
- timestamp as evidence only, never for ordering.

Ordering is the predecessor chain and sequence, not wall clock.

### 8.2 Lock choice

Use an exclusive Linux open-file-description lock (`F_OFD_SETLKW`) on the stable `lock` inode. OFD locks attach to the open file description and are released on its final close; they avoid the process-associated lock hazard where closing an unrelated FD for the same file can drop locks.[R18]

Constraints:

- locks are advisory; all native writers must go through the helper;
- the v1 write fence and file permissions prevent bypass by normal production code;
- never acquire two run locks in one operation;
- never hold a run lock during model execution, Lean compilation, network I/O, or artifact streaming;
- diagnostic owner data may be written separately, but it never decides lock ownership;
- process death releases the kernel lock. There is no stale-lock deletion algorithm.

### 8.3 `commit_event`

```text
Inputs:
  run_id
  expected_head_event_digest
  event canonical bytes
  request_digest
  idempotency_key

Outside lock:
1. parse strictly; reject duplicate keys, unknown major versions, non-finite values
2. validate event.run_id and event.predecessor == expected_head
3. verify every referenced artifact and schema/contract binding
4. compute pure transition independently and compare old/new state roots
5. put event bytes durably in CAS

Inside exclusive run lock:
6. read and fully verify current HEAD and head event
7. if committed idempotency key exists:
   a. same request digest => return the existing outcome/ref
   b. different request digest => IDEMPOTENCY_CONFLICT
8. if current head != expected_head => HEAD_CONFLICT; do not rebase automatically
9. recheck freshness/dependency fingerprint against current head
10. write canonical new HEAD to same-directory `.HEAD.tmp.<nonce>` with O_EXCL
11. fsync(temp_head_fd)
12. renameat(temp, "HEAD") for atomic replacement
13. fsync(run_dir_fd)
14. reopen and verify HEAD resolves to the event
15. release lock
16. emit committed acknowledgement/receipt

After commit:
17. rebuild/write projection caches atomically; projection failure does not roll back HEAD
```

Step 13 is the commit durability barrier. If the helper dies or returns an error from steps 12–14, the caller receives `COMMIT_OUTCOME_UNKNOWN` and may not repeat the side effect. It calls recovery with the same idempotency key. Recovery returns committed-existing or safe-to-retry.

### 8.4 Why prepared branches are safe

Two controllers may both prepare event objects from head `H`. The first acquires the lock and commits `E1`. The second then observes `HEAD != H` and returns conflict. `E2` remains an unreferenced immutable object. It is not an event in the committed history and cannot affect replay.

The controller recomputes a new transition from `E1`; it never edits or silently “rebases” `E2`.

### 8.5 Idempotency lookup

Do not rely on a mutable projection for correctness. For the initial bounded slice, recover idempotency by walking the verified event chain to genesis. Later, if runs become large, include a content-addressed persistent map root in each event/state root. A SQLite or JSON index may accelerate lookup but must be checked against the chain and be deletable.

### 8.6 Crash matrix

| Last completed action | Allowed recovered authority | Required handling |
|---|---|---|
| temp created / partial write | old head; no new object | remove temp later; never publish |
| object file fsynced, not installed | old head; durable temp may remain | orphan cleanup |
| object installed, blob dir not synced | old head; object may exist or disappear | verify/re-put before reference |
| blob dir synced | old head; unreferenced object durable | safe orphan |
| event object synced | old head; uncommitted event durable | safe branch/orphan |
| head temp fsynced | old head | remove temp later |
| head renamed, run dir not synced | complete old or complete new valid head | recovery validates; caller outcome unknown |
| run dir synced, before acknowledgement | new head | idempotency recovery returns committed-existing |
| acknowledgement emitted | new head or descendant | `AcknowledgedCommitNeverLost` |
| projection write interrupted | unchanged authoritative head | delete/rebuild projection |

There is no valid state with a new head and missing referenced event/blob because those directory syncs complete before head replacement.

### 8.7 Recovery algorithm

Under the run lock:

1. safely open `HEAD`; reject symlink/special file;
2. strictly parse and validate run ID, sequence, descriptor, event digest/size;
3. walk predecessor descriptors to genesis with a configured maximum and cycle detection;
4. verify sequence continuity and every event digest;
5. verify all artifacts required by the requested recovery/idempotency decision;
6. derive state from genesis and compare each stored old/new state root;
7. classify head temps and branch objects as non-authoritative;
8. return one of:

```text
RECOVERED_VALID
COMMITTED_EXISTING
SAFE_TO_RETRY
INCOMPLETE_RUN_CREATION
HEAD_MISSING
HEAD_CORRUPT
EVENT_CHAIN_CORRUPT
REFERENCED_OBJECT_MISSING
STORE_OUTCOME_UNKNOWN
```

Do not “repair” a corrupt head by selecting the highest-sequence orphan event. Only a committed pointer establishes branch choice. Repair requires an operator-approved recovery plan referencing a previously retained verified head receipt.

### 8.8 Garbage collection

No online deletion in the first slice. Orphans and temps are bounded by run/storage budgets and retained for inspection.

Later GC is a separate offline protocol:

- stop native writers or acquire a global GC exclusion capability;
- mark from every verified run head, evidence root, publication root, migration root, and pinned reference;
- retain all reachable predecessor chains and schemas;
- emit a proposed deletion manifest and digest;
- require approval for destructive deletion;
- sweep only objects absent from the stable mark set;
- never use `st_nlink` or filenames as reachability authority.

---

## 9. Safe path and filesystem policy

`openat2` provides rooted resolution controls intended for trusted programs resolving untrusted paths. `RESOLVE_BENEATH` prevents escape from the supplied directory; `RESOLVE_NO_MAGICLINKS` blocks proc-style magic links; `RESOLVE_NO_SYMLINKS` blocks every path-component symlink; `RESOLVE_NO_XDEV` blocks mount crossing.[R6]

### 9.1 Internal authority paths

The helper opens the configured roots once, verifies directory type/mount identity, and retains directory FDs. Every later operation is FD-relative.

For internal store/run keys:

- generate names from validated IDs/digests;
- reject absolute paths, empty components, `.`, `..`, slash, NUL, noncanonical digest case, and unexpected Unicode;
- use `openat2` with `RESOLVE_BENEATH|RESOLVE_NO_MAGICLINKS|RESOLVE_NO_SYMLINKS|RESOLVE_NO_XDEV`;
- require same mount for each root whose protocol uses rename/link;
- never call `Path.resolve()` and then trust the resulting string;
- never accept a locator as an open target.

`RESOLVE_NO_XDEV` is appropriate for authority roots because their mount is fixed. The kernel documentation warns that indiscriminate use can reject ordinary bind-mount layouts.[R6] Therefore it is configurable only for explicitly non-authority import views, never silently relaxed for the store.

### 9.2 Imported trees and workspace outputs

For every imported entry:

- resolve beneath a capability root;
- reject symlinks, magic links, sockets, devices, FIFOs, and mount crossings unless the contract explicitly names and supports them;
- accept only regular files and directories in the first slice;
- enforce file count, depth, per-file size, and total byte bounds;
- open then `fstat`; stream exact bytes; `fstat` again;
- if size/identity changes during read, return `SOURCE_CHANGED_DURING_IMPORT`;
- copy into CAS; never retain a mutable source path as identity;
- detect normalized-name/case collisions before constructing a snapshot;
- do not follow hardlinks as paths. Multiple names with the same inode may be recorded, but imported content is copied and independently digest-bound.

Workspace output is untrusted until the process is stopped and reconciled. The sandbox broker walks only the attempt output root with the same rules and hands verified regular-file FDs to the store helper. No child ever receives the authority-store FD or path.

### 9.3 Filesystem assumptions and startup probe

At daemon startup, record:

- kernel boot ID/version;
- filesystem type and mount ID for each authority root;
- mount options relevant to read/write/suid/device/exec behavior;
- availability of `openat2`, `renameat2(RENAME_NOREPLACE)`, directory `fsync`, OFD locks, and hardlink fallback;
- free-space thresholds and configured reserve;
- helper binary digest/version.

The probe may establish API availability. Only the release crash matrix establishes a supported filesystem profile. On unsupported or changed mount identity, open the store read-only for inspection and return `AUTHORITY_FILESYSTEM_UNSUPPORTED` for writes.

### 9.4 Publication

Prefer immutable release directories and one atomic public ref:

```text
publish-root/releases/<publication-digest>/...
publish-root/CURRENT -> canonical pointer file, not a symlink
```

Materialize and verify the complete release directory, sync all files/directories bottom-up, then atomically replace and directory-sync `CURRENT` under a destination lock. Avoid file-by-file in-place publication. If an external destination cannot use one ref, Phase 6 needs its own journaled TLA+ model and crash matrix.

---

## 10. Linux sandbox architecture

Seccomp reduces exposed kernel surface but the kernel documentation explicitly says it is not a complete sandbox; combine it with namespaces, DAC/capability controls, cgroups, and an LSM.[R11] Landlock is a stackable LSM allowing even unprivileged processes to restrict their future children; its ABI must be probed and rules limited to supported rights.[R10] cgroup v2 hierarchically organizes processes and constrains resources; systemd exposes those controls as unit properties.[R12][R14]

### 10.1 Broker boundary

Install one root-owned service:

```text
campaign-v2-sandboxd.service
```

It listens on a root-owned Unix socket accessible only to the controller group. Its protocol accepts:

```text
SandboxLaunchV2 {
  request_id
  fixed_profile_id + profile_digest
  registered_toolchain_id + executable_digest
  argv (bounded strings; no shell)
  input_snapshot_ref
  output_contract
  resource_limits
  deadline
  environment allowlist values
  network capability = none       # first slice
}
```

It does **not** accept:

- arbitrary systemd property names;
- arbitrary bind-mount source/destination paths;
- shell command strings;
- host UID/GID choices;
- host network, D-Bus, or device requests;
- authority-store paths;
- caller-selected seccomp policy;
- caller-selected capabilities.

The broker resolves registered profiles/toolchains, materializes input artifacts into a broker-controlled attempt tree, starts the transient unit through the system manager, streams output, collects cgroup/unit results, validates output entries, transfers bounded output FDs/bytes to the controller, and destroys the attempt state.

This is the privileged surface. Keep policy selection in unprivileged pure code, but keep enforcement choices fixed and validated in the broker.

### 10.2 Release profile: `linux.systemd.no-network.v1`

Minimum transient-service properties:

```text
Type=exec
DynamicUser=yes
NoNewPrivileges=yes
CapabilityBoundingSet=
AmbientCapabilities=
PrivateUsers=yes
PrivatePIDs=yes
PrivateIPC=yes
PrivateNetwork=yes
PrivateDevices=yes
PrivateTmp=disconnected
ProtectSystem=strict
ProtectHome=yes
ProtectKernelTunables=yes
ProtectKernelModules=yes
ProtectKernelLogs=yes
ProtectControlGroups=private
ProtectClock=yes
RestrictSUIDSGID=yes
RestrictRealtime=yes
LockPersonality=yes
RemoveIPC=yes
UMask=0077
SystemCallArchitectures=native
SystemCallFilter=<resolved release allowlist>
RestrictAddressFamilies=AF_UNIX
MemoryAccounting=yes
MemoryHigh=<profile soft limit>
MemoryMax=<profile hard limit>
MemorySwapMax=<profile limit>
TasksAccounting=yes
TasksMax=<profile process/thread limit>
CPUAccounting=yes
CPUQuota=<profile limit>
IOAccounting=yes
RuntimeMaxSec=<hard wall ceiling>
KillMode=control-group
SendSIGKILL=yes
TimeoutStopSec=<short bounded cleanup>
```

Filesystem view:

- immutable pinned toolchain/root image read only;
- materialized input snapshot read only;
- one writable attempt directory;
- bounded tmpfs scratch/output, or another storage mechanism with a real hard byte limit;
- private minimal `/dev`;
- private `/tmp` and `/var/tmp`;
- no home, authority store, controller run root, SSH/GPG credentials, browser/session sockets, Docker/Podman socket, system/user bus, or host `/run/user`;
- no executable writable mount unless a particular compiler contract requires it and the seccomp/profile review accepts it.

Systemd supports read-only bind mounts, `ProtectSystem=strict`, private devices/network, capability bounding, no-new-privileges, address-family restrictions, and syscall filtering.[R13] Cgroup resource properties map to cgroup-v2 controls such as `cpu.max`, `memory.max`, and pids/task limits.[R14]

### 10.3 Same-namespace launcher probe

Requested properties are insufficient because some managers/kernels may degrade them. The first process inside the unit is a tiny pinned launcher that checks its effective state and only then `execve`s the target.

It records and enforces:

- `NoNewPrivs: 1` and seccomp filter mode from `/proc/self/status`;
- empty effective/permitted/ambient capability sets;
- expected UID/GID and user-namespace maps;
- distinct PID, mount, IPC, network, user, and cgroup namespace identities as required;
- expected cgroup path and effective memory/pids/CPU limits;
- only expected inherited FDs;
- expected mount table and read/write flags;
- absence of host session/bus/container sockets;
- failure to read a randomized forbidden canary outside the input view;
- failure to create an external network connection;
- bounded writable-root capacity;
- exact launcher, profile, rootfs/toolchain, and seccomp digests.

Any failed probe stops before target execution and returns `SANDBOX_ATTESTATION_FAILED`. The attestation is retained as an artifact even on failure.

### 10.4 Seccomp policy

Use a release allowlist, not an ad hoc denylist. The kernel warns that filters must check syscall architecture and that allowing `ptrace` with seccomp tracing can enable escapes.[R11]

Process:

1. trace each pinned toolchain profile in a disposable development environment;
2. resolve systemd syscall groups to exact syscall names for the installed version;
3. start from the minimal observed set plus required error paths;
4. explicitly exclude mount/namespace mutation, ptrace/process-memory access, BPF, perf, keyring, module, reboot, kexec, raw I/O, swap, and obsolete ABI entry points unless a reviewed profile proves need;
5. require native syscall architecture;
6. use diagnostic `EPERM` only during profile development;
7. use kill/fail-closed behavior in the release profile;
8. hash and retain the exact resolved list, not only a mutable group name.

A compiler/Lean profile and an agent runtime profile will not share one giant allowlist.

### 10.5 Landlock

After systemd constructs mounts and before executing the target, the launcher should apply an ABI-negotiated Landlock ruleset:

- read/execute: pinned toolchain and immutable input view;
- read/write/create/remove: attempt output/scratch only;
- no other filesystem rights;
- no network rights for the first slice;
- signal/abstract-Unix-socket scoping when supported by the detected ABI.

Landlock absence does not silently cancel the mount/DAC/seccomp profile. It is an optional defense-in-depth capability in `linux.systemd.no-network.v1`, recorded as unavailable when missing. A later higher assurance class may make a minimum ABI mandatory.

### 10.6 Network and secrets

`PrivateNetwork=yes` creates a network namespace with only loopback.[R13] Do not replace it with seccomp alone: seccomp cannot safely inspect pointed-to socket-address memory as a complete network policy, and Landlock’s port rules are not domain/DNS policy.[R10][R11]

First slice:

```text
network = none
secrets = none
```

Later model-backed agents require an architectural split:

```text
trusted model/provider client or narrow proxy
    owns provider credential and outbound network

untrusted reasoning/tool workspace
    owns bounded prompt/input artifacts
    has no provider credential and no general network

per-tool sandbox
    executes concrete commands with no network by default
```

Do not put an API token in the environment of a monolithic OMP process that can run model-proposed shell tools. Environment scrubbing in a child is too late if the same process owns both the secret and arbitrary tool execution. A future proxy protocol must bind provider/model, budget, request digest, allowed input refs, and response receipt; it must not be a generic HTTP proxy.

### 10.7 Output, disk, and process containment

Cgroup I/O throttling limits rate, not total bytes. A strong profile therefore needs a real attempt-storage bound:

- fixed-size tmpfs counted under the unit’s memory cgroup for the first slice; or
- broker-managed project quota/fixed-size filesystem after a separate implementation review.

The supervisor always drains stdout/stderr to avoid pipe deadlock. It tracks complete byte count and hash while retaining only bounded views. At the configured stream limit it terminates the unit; it does not merely truncate silently and report success.

The systemd unit/cgroup is the ownership set. pidfd/PID/start-time/session identity remains diagnostic and defense in depth. Termination targets the whole unit/cgroup; completion requires the cgroup empty, streams EOF, main process reaped, output scan complete, and broker resources released.

---

## 11. Capability negotiation and degradation policy

### 11.1 No boolean `sandboxed`

Represent sandbox state as:

```text
SandboxCapabilityReportV2 {
  requested_profile_digest
  backend + backend_version
  kernel + boot_id
  required_capabilities
  optional_capabilities
  effective_capabilities
  unavailable_capabilities {machine_code, evidence}
  self_probe_results
  namespace_ids
  cgroup_limits
  seccomp_digest
  mount_manifest_digest
  toolchain/rootfs_digest
  environment_name_digest
  inherited_fd_manifest
  assurance_disposition
}
```

Environment values that may be sensitive are never copied into the report; record names and value digests only when the contract requires binding.

### 11.2 Dispositions

```text
ENFORCED
  Every required capability is effective and every self-probe passed.

ENFORCED_WITH_OPTIONAL_GAPS
  Every required capability is effective; named optional defenses are absent.
  Generic claims are limited to the base profile, not the absent defenses.

TRUSTED_EXCEPTION
  The step was explicitly approved to run without the untrusted profile.
  assurance_status remains NOT_RUN/UNSUPPORTED for generic isolation.

UNAVAILABLE
  A required capability is missing. No process is spawned.

ATTESTATION_FAILED
  The backend claimed support but the in-unit probe disagreed. No target is executed.
```

There is no automatic transition from `UNAVAILABLE` to `TRUSTED_EXCEPTION`.

### 11.3 Required capability matrix

| Capability | `linux.systemd.no-network.v1` requirement | Acceptable implementation | Missing behavior |
|---|---|---|---|
| Filesystem view | Hard | private mount namespace, immutable read-only inputs/toolchain, one bounded writable root, authority root absent | `UNAVAILABLE` |
| Principal isolation | Hard | system service `DynamicUser`, empty capabilities, NNP; private user namespace when supported by profile | `UNAVAILABLE` |
| Process visibility/lifecycle | Hard | private PID namespace, systemd unit/cgroup, group kill, pidfd-aware receipts | `UNAVAILABLE` |
| Network denial | Hard | private network namespace, no mounted host sockets, address-family/seccomp restrictions | `UNAVAILABLE` |
| Syscall reduction | Hard | release seccomp allowlist, native architecture, attested filter digest | `UNAVAILABLE` |
| Resource limits | Hard | cgroup-v2 memory/CPU/pids plus supervisor wall/stream limits | `UNAVAILABLE` |
| Total writable bytes | Hard | fixed-size tmpfs or reviewed hard quota | `UNAVAILABLE` |
| Device isolation | Hard | private minimal `/dev`, no host physical devices | `UNAVAILABLE` |
| Environment/secrets | Hard | clean explicit environment; no ambient secrets; inherited-FD allowlist | `UNAVAILABLE` |
| Host path resolution | Hard for controller/broker | `openat2` rooted safe resolution for materialization/import | `UNAVAILABLE` |
| Landlock filesystem layer | Optional in v1 | ABI-negotiated launcher ruleset | `ENFORCED_WITH_OPTIONAL_GAPS` |
| SELinux confinement profile | Optional in v1 | dedicated tested type/domain | optional gap now; candidate hard requirement later |
| VM kernel boundary | Not part of profile | VM backend | no effect on v1 disposition |

### 11.4 Portability

“Portable degradation” means portable **capability negotiation**, not pretending unlike mechanisms are equivalent.

Backend contract:

```text
probe() -> capabilities + evidence
compile(profile, capabilities) -> exact launch plan or UNAVAILABLE
launch(plan) -> effective attestation + invocation identity
terminate(identity) -> reconciled result
```

- Linux systemd broker may satisfy the production profile.
- Rootless systemd/bubblewrap may satisfy a separately named developer profile.
- An OCI runtime may later satisfy the same semantic requirements after its own conformance suite.
- macOS/Windows have no native equivalent in this release. They return `UNAVAILABLE` for the Linux profile; a future VM backend gets a new profile.
- `chroot`, `ulimit`, cooperative timeout, or “no dangerous command in the prompt” are never fallback implementations.

---

## 12. First vertical slice

### 12.1 Components

Implement only:

```text
src/agentic_lean_math_assistant_v2/
  contracts.py              # immutable DTOs, canonical parser/encoder
  compat_v1.py              # read-only exact import boundary
  store.py                  # typed client for platform helper
  control.py                # pure reducer + serial application service
  execution.py              # broker client and supervisor result mapping
  assurance.py              # exact Lean/evidence receipts for this slice
  facade.py                 # inspect/import/run/resume CLI/API

native/platform-helper/     # Rust, unprivileged store operations
native/sandbox-broker/      # Rust, root-owned fixed-profile system service
formal/                     # TLA+/PlusCal specs/configs
```

Do not create generic plugin frameworks, distributed queues, model routing, dashboards, publication, remote storage, or arbitrary playbook catalogues before this slice closes.

### 12.2 Exact flow

1. Parse a strict `CampaignSourceManifestV2`; preserve raw import bytes.
2. Materialize every declared input as immutable CAS objects and a snapshot manifest.
3. Commit `RUN_CREATED` under the head protocol.
4. Compile `math.receipt_first_formal_audit@2.0.0` deterministically.
5. Commit durable launch intent with fixed toolchain/profile/input digests.
6. Ask the sandbox broker to run one deterministic command with no network/secrets.
7. Reconcile the transient unit, stream receipts, and output tree.
8. Import verified outputs to CAS; commit terminal receipt.
9. Launch pinned Lean through the same sandbox profile.
10. Import Lean stdout/stderr and exact environment/declaration/axiom receipt.
11. Run continuation gate in pure control code.
12. Commit evidence root and derived orthogonal statuses.
13. Delete projections; reconstruct state from `HEAD`.
14. Repeat with helper/broker kill at every failpoint.
15. Resume from the same idempotency keys and prove no side effect is duplicated.
16. Inspect/export without granting authority to the export.

### 12.3 Serial first

One controller schedules one side effect at a time. The object store remains concurrency-safe and the head protocol is multi-process safe, but the scheduler does not exploit parallelism yet.

Concurrency is enabled only after:

- `RunCommit` two-controller TLC configurations pass;
- Hypothesis concurrent traces pass;
- store kill/crash matrix passes;
- attempt claim/launch idempotency passes;
- resource isolation between two simultaneous units passes.

---

## 13. Verification and fault-injection plan

### 13.1 Formal gates

Required per candidate:

- SANY parse/type checks;
- TLC invariant checks for both core specs under pinned configurations;
- TLC deadlock check with intentional terminal states classified;
- at least one smaller unsymmetrized configuration;
- retained counterexample traces for negative/mutated specs proving each important invariant can fail;
- Apalache bounded checks as additional evidence, with tool limitation recorded;
- exact tool/config/spec digests in receipts.

A test that only sees a passing invariant is weak. Mutation cases should remove or reorder:

- object directory sync;
- expected-head comparison;
- lock exclusion;
- idempotency request binding;
- reconciliation-before-publication;
- invalidation closure.

Each mutation must produce a counterexample.

### 13.2 Hypothesis state-machine gates

Generate sequences of:

```text
create run
put same/different object
prepare two branches
acquire/interrupt lock
commit with current/stale head
repeat same/different idempotency request
crash at named failpoint
recover
corrupt projection
remove projection
resume attempt
invalidate upstream
commit/reject evidence
```

Check the abstract invariants after every rule. Run against:

1. an in-memory model;
2. the real Rust helper on a temporary ext4 test volume;
3. the helper with injected syscall errors/failpoints.

Hypothesis shrinking should leave a minimal action trace, which is retained with the seed and helper receipts.[R3]

### 13.3 Store process-kill failpoints

The helper must expose test-build failpoints after:

```text
temp create
first/middle/final write
file fsync
blob install
blob directory fsync
event file fsync
event directory fsync
run lock acquisition
head compare
head temp write
head temp fsync
head rename
run directory fsync
head re-read
before acknowledgement
```

At each point:

- send `SIGKILL` to the helper process;
- start a fresh helper process;
- recover using only durable bytes;
- assert old/new valid head according to the crash matrix;
- assert no head references missing bytes;
- assert idempotency returns committed-existing or safe-to-retry;
- assert projections do not affect the result;
- assert temp/orphan classification is stable.

Inject short writes, `EINTR`, `ENOSPC`, `EDQUOT`, permission failure, `EIO` on every sync, destination collision, corrupt existing object, and unexpected mount change.

### 13.4 Power-loss filesystem gate

Process death does not simulate loss of kernel page cache. Before release, run the same failpoint matrix in a disposable VM whose ext4 authority disk is abruptly powered off at the selected point. After reboot:

- mount and inspect the filesystem;
- run recovery before any cleanup;
- retain filesystem/kernel/mount versions and logs;
- require the same old/new/no-hybrid invariants;
- fence writes on any unsupported outcome.

The supported profile is the exact tested storage stack. Other filesystems need their own gate.

### 13.5 Sandbox adversarial gate

Inside the actual production unit, require tests that attempt to:

- read the authority store, home, SSH/GPG files, browser/session state, and randomized host canary;
- access system and user D-Bus/container sockets;
- connect via IPv4, IPv6, DNS, Unix path sockets outside the view, and abstract Unix sockets;
- create a raw socket;
- mount/unmount, create another namespace, `ptrace`, use process-memory APIs, BPF, perf, keyctl, module/kexec/reboot operations;
- open physical devices or create device nodes;
- signal a host process;
- fork beyond `TasksMax`;
- allocate beyond `MemoryMax` and observe a unit-local OOM receipt;
- fill scratch/output beyond the configured byte cap;
- exceed stdout/stderr cap;
- leave a daemon after leader exit;
- exploit inherited file descriptors;
- use symlinks/hardlinks/special files in output;
- discover a secret canary in environment, argv, FDs, mounts, or `/proc`.

Every attempt must produce a classified result. The unit must become empty after cleanup. A rootless backend running the same tests still receives only its separately named developer assurance class.

### 13.6 End-to-end acceptance

The first slice exits only when:

- canonical/schema negative vectors pass;
- TLA+/TLC invariants and mutation counterexamples pass;
- all helper kill points recover correctly;
- ext4 VM power-loss matrix passes;
- two-controller head/idempotency tests pass;
- sandbox capability probe and adversarial suite pass;
- deterministic command and Lean steps run through the production broker;
- no child/cgroup/pump survives return;
- deleting every projection reproduces byte-identical derived state;
- one injected crash resumes without duplicate command/Lean invocation when the prior invocation committed;
- one frozen evidence root contains exact input, toolchain, execution, Lean, and assurance refs;
- v1 source and retained history are byte-identical;
- no native writer emits a v1 record;
- no result field upgrades process success into mathematical or assurance closure.

---

## 14. Implementation order

### Stage 0 — Freeze contracts and assumptions

- revise `ArtifactRefV2` to separate locator;
- freeze canonical bytes, media types, event/head schemas, machine errors, ID grammar, and ext4 support profile;
- freeze abstract action names and invariants;
- pin TLC, Apalache, Rust, Python, Lean, systemd profile, and helper/broker build inputs.

**Gate:** strict schema vectors and TLA+ specs parse; every syscall/filesystem assumption is named.

### Stage 1 — Model before I/O

- implement `RunCommit.tla` and `AttemptLifecycle.tla`;
- check small TLC configurations;
- create intentional broken variants/mutations and retain counterexamples;
- implement pure Python reducer and in-memory Hypothesis state machine.

**Gate:** model and pure reducer agree on generated traces.

### Stage 2 — Store helper

- implement safe root opening, object put/read, OFD lock, head commit, recovery, and receipts;
- no GC, SQLite, remote store, compression, or optimization;
- add all syscall failpoints before integrating the controller.

**Gate:** process-kill and injected-error matrix passes on ext4.

### Stage 3 — Sandbox broker

- install root-owned fixed-profile broker;
- implement systemd transient-unit compiler, clean environment, dynamic user, materialization, output FD transfer, same-namespace launcher probe, resource reconciliation, and termination;
- build the Lean/command release seccomp profile and adversarial suite.

**Gate:** production profile is `ENFORCED`; every forbidden probe fails; unit/cgroup empties.

### Stage 4 — Native deterministic slice

- wire import, command, Lean, continuation, evidence, resume, inspect/export;
- keep scheduler serial and network/secrets absent;
- run helper and broker failpoints end to end.

**Gate:** all acceptance criteria in Section 13.6 pass.

### Stage 5 — Power-loss and candidate freeze

- run VM abrupt-power matrix on the target ext4 profile;
- freeze candidate digests and rerun full gates;
- document unsupported filesystems/backends and local trusted-writer authenticity limit.

**Gate:** one immutable candidate has implementation, formal, crash, sandbox, and evidence receipts.

### Stage 6 — Only then add model agents

- separate provider client from tool executor;
- design a non-generic model proxy and secret capability;
- add exact network/budget/request receipts;
- add Luna/Terra/Sol routing only after the deterministic substrate remains unchanged under the new tests.

No concurrency, publication, generic plugin system, or remote execution should preempt these stages.

---

## 15. Main risks and stop conditions

| Risk | Detection | Required response |
|---|---|---|
| systemd property accepted but ineffective | in-unit launcher probe disagrees | no target exec; `ATTESTATION_FAILED` |
| helper returns after failed directory sync | fault injection / unknown outcome | recovery-required; never success |
| authority root mount changes | startup/preoperation mount identity mismatch | write fence; inspection only |
| existing digest path has different bytes | full verify on dedup | store-wide corruption fence and quarantine |
| stale writer prepares branch | expected-head conflict | retain orphan; recompute from new head |
| idempotency key reused with different request | event-chain lookup | `IDEMPOTENCY_CONFLICT` |
| rootless backend appears to pass simple probe | full adversarial/capability suite | retain developer profile; no auto-promotion |
| monolithic model runner needs token and shell tools | architecture review | block generic sandbox claim; build provider/tool split |
| seccomp allowlist breaks Lean/compiler | deterministic profile tests | update exact profile with reviewed syscall need; do not disable seccomp globally |
| output cannot be hard byte-bounded | capability probe | `UNAVAILABLE` for untrusted profile |
| TLA+ state explosion hides coverage | recorded state/depth plus small unsymmetrized configs | reduce model, use symmetry carefully, add Apalache; never report unchecked invariant |
| actual power-loss outcome violates abstract primitive | VM crash matrix | unsupported filesystem/profile; redesign protocol or use a transactional backend |

### 15.1 Conditions that justify reconsidering SQLite

Reopen the metadata-store decision only if observed evidence shows one of:

- per-run head contention is operationally significant;
- chain-walk idempotency/recovery exceeds a measured bound and persistent content-addressed maps are inadequate;
- queries require transactional secondary indexes rather than disposable projections;
- the ext4 flat-head crash matrix cannot satisfy the specified invariants;
- multi-record atomic control transitions become unavoidable.

If selected later, external blobs are still written and directory-synced before a SQLite transaction references them; orphan blobs remain acceptable. SQLite does not make blob and workspace path handling disappear.

### 15.2 Conditions that justify OCI runtime/VM isolation

Promote `crun`/OCI or a VM backend when:

- pinned root images become necessary for reproducibility;
- systemd property portability becomes a maintenance burden;
- remote execution requires a standard bundle;
- an agent needs a stronger cross-UID/rootfs boundary than the current broker profile;
- hostile native code or kernel-attack exposure warrants a separate kernel.

Promotion requires the same semantic capability and adversarial suite; backend name recognition is not conformance.

---

## 16. Final architecture

```text
                              trusted authority plane

  v2.facade
      │ strict request
      ▼
  CampaignApplicationService ───────────────┐
      │                                     │
      │ pure transition                     │ fixed launch request
      ▼                                     ▼
  StateMachine / Scheduler             Sandbox broker (root-owned)
      │                                     │
      │ event bytes                         │ systemd transient unit
      ▼                                     │ DynamicUser + namespaces
  Store client ──FD/request──► Rust helper  │ cgroup + seccomp + NNP
      │                         │            │ bounded mounts/output
      │                         ├─ CAS blobs │
      │                         ├─ OFD lock  ▼
      │                         ├─ HEAD CAS  command / Lean process
      │                         └─ recovery       │
      │                                          │ reconciled FDs/receipts
      └──────────────────────────────────────────┘
                         │
                         ▼
                 immutable evidence root
                         │
                         ├─ projection: state.json
                         ├─ projection: events.jsonl
                         └─ export: OCI/RO-Crate later

  Formal sidecar (release gate, not runtime authority):
      TLA+/TLC + Apalache + Hypothesis refinement traces + crash harness
```

The control plane is intentionally boring:

- one pure state transition;
- one immutable object graph;
- one serialized head move;
- one fixed-profile execution broker;
- one explicit capability report;
- one evidence commit that binds all of it.

That is enough to support the later model-routing and mathematical system without asking model prose, mutable paths, process exit codes, or sandbox labels to carry authority they do not have.

---

## References

- **[R1]** Leslie Lamport, **TLA+ Tools — TLC Model Checker**. TLC is an explicit-state checker for executable TLA+ specifications and checks safety and liveness. <https://lamport.azurewebsites.net/tla/tools.html>
- **[R2]** Apalache documentation, **Getting Started — Apalache vs. TLC / Assumptions**. Symbolic SMT checking; fixed finite data; bounded finite executions; experimental status. <https://apalache-mc.org/docs/apalache/index.html>
- **[R3]** Hypothesis documentation, **Stateful tests**. Rule-based state machines generate and shrink sequences of actions while checking invariants. <https://hypothesis.readthedocs.io/en/latest/stateful.html>
- **[R4]** Open Container Initiative, **Content Descriptors**. Descriptor media type, digest, size, and Merkle-DAG references. <https://github.com/opencontainers/image-spec/blob/main/descriptor.md>
- **[R5]** Open Container Initiative, **Image Layout**. `blobs/<algorithm>/<encoded>` content-addressed layout and descriptor references. <https://github.com/opencontainers/image-spec/blob/main/image-layout.md>
- **[R6]** Linux man-pages, **openat2(2)**. `RESOLVE_BENEATH`, `RESOLVE_IN_ROOT`, magic-link, symlink, and mount-crossing controls. <https://man7.org/linux/man-pages/man2/openat2.2.html>
- **[R7]** Linux man-pages, **rename(2)/renameat2(2)**. Atomic destination replacement and `RENAME_NOREPLACE`. <https://man7.org/linux/man-pages/man2/renameat2.2.html>
- **[R8]** Linux man-pages, **fsync(2)**. File data/metadata synchronization and the need to sync the containing directory entry separately. <https://man7.org/linux/man-pages/man2/fsync.2.html>
- **[R9]** SQLite, **Atomic Commit In SQLite**. Flush, ordering, journal, rollback, and power-loss assumptions in a mature transactional implementation. <https://www.sqlite.org/atomiccommit.html>
- **[R10]** Linux kernel documentation, **Landlock: unprivileged access control**. Stackable restrictions, filesystem/network rules, ABI negotiation, and child inheritance. <https://docs.kernel.org/userspace-api/landlock.html>
- **[R11]** Linux kernel documentation, **Seccomp BPF**. Kernel-surface reduction, architecture checks, filter inheritance, and explicit statement that seccomp alone is not a sandbox. <https://docs.kernel.org/userspace-api/seccomp_filter.html>
- **[R12]** Linux kernel documentation, **Control Group v2**. Hierarchical process organization and resource controllers. <https://docs.kernel.org/admin-guide/cgroup-v2.html>
- **[R13]** systemd, **systemd.exec**. Dynamic users, no-new-privileges, capabilities, private namespaces/devices/network, filesystem protection, address-family and syscall filtering, and degradation caveats. <https://www.freedesktop.org/software/systemd/man/latest/systemd.exec.html>
- **[R14]** systemd, **systemd.resource-control**. cgroup-backed CPU, memory, task, and I/O accounting/limits. <https://www.freedesktop.org/software/systemd/man/latest/systemd.resource-control.html>
- **[R15]** Linux man-pages, **chroot(2)**. `chroot` changes pathname resolution only and is not intended as a security sandbox. <https://man7.org/linux/man-pages/man2/chroot.2.html>
- **[R16]** containers/bubblewrap, **README — Sandbox security and limitations**. Bubblewrap constructs namespaces but leaves complete security policy to its caller. <https://github.com/containers/bubblewrap>
- **[R17]** Open Container Initiative, **Linux Runtime Configuration**. Namespace, cgroup, capability, LSM, filesystem, and device configuration model. <https://github.com/opencontainers/runtime-spec/blob/main/config-linux.md>
- **[R18]** Linux man-pages, **fcntl locking**. OFD-lock ownership and release semantics versus traditional process-associated locks. <https://man7.org/linux/man-pages/man2/fcntl_locking.2.html>
