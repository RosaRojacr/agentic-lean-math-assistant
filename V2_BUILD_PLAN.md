# Agentic Lean Math Assistant v2 — build plan

**Status:** post-1.0 native architecture roadmap; implementation has not started
**Date:** 2026-08-26
**Inputs:** `V2_RESEARCH_REPORT.md`, `V2_CONTROL_PLANE_REPORT.md`, the 1.0 source/tests, and the retained 1.0 support corpus
**Primary goal:** produce one native-v2 deterministic vertical slice whose contracts, durable state, execution isolation, crash recovery, Lean receipt, and evidence root all pass their release gates without modifying retained 1.0 authority.

---

## 1. Build outcome

The first build is complete only when a clean workstation can:

```text
bootstrap pinned tools
→ build Python and Rust components
→ install the fixed-profile sandbox broker through an explicit operator step
→ import immutable inputs
→ run one deterministic command in the production sandbox
→ run pinned Lean in the same sandbox
→ commit exact receipts and an evidence root
→ survive an injected crash
→ resume without repeating a committed invocation
→ delete projections and reconstruct identical state from HEAD
→ inspect/export the result
```

The candidate consists of:

- a Python wheel containing `agentic_lean_math_assistant_v2` beside untouched v1 code;
- unprivileged Rust `platform-helper` binary;
- root-owned Rust `sandbox-broker` and same-namespace `sandbox-launcher` binaries;
- systemd service/socket units and one fixed no-network sandbox profile;
- strict v2 schemas, media-type registry, and machine-error catalogue;
- TLA+/PlusCal specifications, model-checker configurations, and receipts;
- deterministic command/Lean playbook resources;
- schema, unit, property, fault, sandbox, integration, incident, and power-loss receipts;
- one canonical candidate manifest binding every delivered byte by digest.

No v2 model-agent routing, publication transaction, remote execution, distributed scheduling, generic plugin system, or general network capability is part of this candidate.

---

## 2. Fixed design constraints

These are not reopened during implementation without a recorded architecture change:

1. v1 is an immutable compatibility/input corpus. Native code never writes a v1 record.
2. `agentic_lean_math_assistant_v2` is a separate package, not an in-place v1 refactor.
3. Python owns immutable contracts, pure control, assurance, and the facade.
4. Rust owns authority filesystem primitives and the privileged sandbox boundary.
5. Durable authority is immutable CAS objects plus one atomically replaced run `HEAD`.
6. `ArtifactRefV2` contains an OCI-compatible `{mediaType, digest, size}` descriptor; a locator is not durable identity.
7. TLA+/TLC and implementation-level state-machine tests are both required.
8. SQLite, remote stores, compression, and garbage collection are excluded from the initial authority path.
9. The production sandbox is a root-owned broker launching fixed-profile systemd transient services.
10. Missing hard sandbox capabilities stop before process spawn. There is no silent fallback.
11. The first slice has no network, API secret, provider client, OMP agent, or Herdr dependency.
12. Scheduling remains serial until the concurrency enablement gate passes.
13. A process exit code never implies artifact validity, formal verification, mathematical closure, assurance, or publication.

---

## 3. Repository and build layout

Target layout:

```text
pyproject.toml
uv.lock

src/
  agentic_lean_math_assistant/                 # frozen v1 production package
  agentic_lean_math_assistant_v2/
    __init__.py
    contracts.py
    compat_v1.py
    store.py
    control.py
    execution.py
    assurance.py
    facade.py
    resources/
      schemas/
      media-types.json
      errors.json
      playbooks/
        math.receipt_first_formal_audit/

native/
  Cargo.toml                        # locked Rust workspace
  Cargo.lock
  platform-helper/
  sandbox-broker/
  sandbox-launcher/
  protocol/                         # shared request/receipt DTO crate only

formal/
  RunCommit.tla
  AttemptLifecycle.tla
  MC_RunCommit.cfg
  MC_AttemptLifecycle.cfg
  mutations/
  README.txt

tests/
  v2/
    contracts/
    compat/
    control/
    store/
    execution/
    assurance/
    e2e/
    incidents/
    fixtures/

packaging/
  systemd/
    campaign-v2-sandboxd.service
    campaign-v2-sandboxd.socket
  sandbox-profiles/
    linux.systemd.no-network.v1.json
    seccomp/

scripts/
  v2_build.py                       # deterministic argv-based build driver

configuration/
  v2/
    toolchains.lock.json
    schemas.lock.json
    support-profile.json

build-v2/                           # ignored disposable build products
  tools/
  native/
  python/
  receipts/
  sandbox/
  candidates/
```

### 3.1 `pyproject.toml` changes

When the v2 package first exists:

- include both `src/agentic_lean_math_assistant` and `src/agentic_lean_math_assistant_v2` in the Hatch wheel target;
- retain `agentic-lean-math-assistant` as the v1 command;
- add `agentic-lean-math-assistant-v2 = "agentic_lean_math_assistant_v2.facade:main"`;
- keep Python `>=3.12,<3.15` unless a contract test proves a narrower requirement;
- reuse installed Hypothesis, mypy, pytest, and Ruff;
- add dependencies only when production code actually imports them.

Do not rename the v1 package or command. Cutover happens in a later explicit facade change, not by aliasing v2 under a v1 identity.

### 3.2 Build driver

`scripts/v2_build.py` is a small deterministic orchestrator, not another control plane. It:

- invokes tools with explicit argv arrays and controlled environment;
- never evaluates shell strings;
- validates pinned tool versions and downloaded-tool digests;
- writes command, environment-name, timing, exit, stdout/stderr hash, and artifact receipts;
- fails on the first failed gate;
- never installs root-owned files automatically;
- prints the exact operator command for the privileged install step;
- supports one subcommand per gate rather than one opaque “build everything” action.

Planned subcommands:

```text
bootstrap
contracts
formal
python-check
native-check
store-test
sandbox-package
sandbox-test
slice-test
powerloss-test
candidate
verify-candidate
```

---

## 4. Dependency order

Build dependency graph:

```text
B0 Baseline freeze and build harness
  ↓
B1 Contract/schema freeze + formal model
  ├──────────────┬─────────────────┐
  ↓              ↓                 ↓
B2 Store helper  B3 Pure control   B4 Sandbox broker/profile
  └──────────────┴─────────────────┘
                 ↓
B5 Deterministic command/Lean slice
                 ↓
B6 Crash, concurrency, incident, and power-loss qualification
                 ↓
B7 Candidate assembly, clean rebuild, and release review
                 ↓
B8 Model agents and broader v2 work — separate approved program
```

Rules:

- B1 blocks all load-bearing implementation. Schemas and state actions must stop moving first.
- B2, B3, and the unprivileged portion of B4 may proceed independently after B1.
- B4’s root installation waits until its protocol/profile tests pass unprivileged validation.
- B5 starts only after B2, B3, and B4 individually pass.
- B6 tests the integrated slice; it does not add features.
- B7 packages only a frozen candidate that has already passed B6.
- B8 cannot weaken or bypass any B7 gate.

---

## 5. Build phases

## B0 — Baseline freeze and build harness

### Purpose

Make every later result attributable to a pinned input and keep v1 reproducible and unchanged.

### Work

1. Inventory the current v1 package, public CLI/API, tests, project manifests, Lean projects/toolchains, retained runs, incident bundles, and known good/bad fixtures.
2. Record byte digests for:
   - v1 source and tests;
   - `pyproject.toml` and `uv.lock`;
   - relevant project manifests and Lean files;
   - `V1_SUPPORT.md/.json` and both v2 reports.
3. Define the native-v2 ID grammar, root directories, and local ext4 support profile.
4. Create `configuration/v2/toolchains.lock.json` containing exact Python, uv, Rust, Cargo, Lean, Java/TLC, Apalache, systemd-profile, and OS support identities/digests.
5. Create the Python/Rust/formal/test directory skeleton without placeholder implementations.
6. Implement only the build-driver version/probe/receipt functions.
7. Update `.gitignore` for `build-v2/` and tool caches; never ignore retained candidate receipts.
8. Produce a baseline manifest and rerun the current v1 verification command unchanged.

### Deliverables

- baseline manifest with all input digests;
- pinned toolchain manifest;
- empty package/workspace structure that imports/builds without stubs;
- working `bootstrap` and version-probe commands;
- v1 verification receipt.

### Exit gate `G0`

- v1 source/test/retained corpus digest inventory is complete;
- current v1 tests still produce the baseline result;
- `uv sync --frozen --group dev` succeeds;
- Rust workspace resolves with `cargo --locked` and contains no unpinned registry update;
- TLC and Apalache binaries/jars match pinned digests;
- no v2 module imports v1 except the empty `compat_v1` boundary;
- no retained v1 byte changed.

### Stop conditions

- unknown v1 consumer or mutable retained root;
- unavailable pinned Lean/TLC toolchain;
- authority filesystem differs from the declared local ext4 profile;
- build bootstrap requires ambient credentials or unrecorded network access.

---

## B1 — Contracts, canonical encoding, and formal model

### Purpose

Freeze the language the Python controller, Rust helpers, TLA+ models, tests, and retained artifacts all share.

### Workstream B1-A — Canonical contracts

Implement in `contracts.py` and resource schemas:

- strict duplicate-key-rejecting bounded JSON parser;
- canonical UTF-8/I-JSON encoder with sorted keys and final-newline rule;
- non-boolean integer and finite-number validation;
- SemVer major/minor compatibility rules;
- strict identifier/digest/media-type types;
- `ArtifactRefV2` and separate `ResolvedArtifactV2`;
- `RunEventV2`, `RunHeadV2`, state-root and predecessor bindings;
- source/effective/run snapshots;
- launch, terminal, execution-attestation, Lean, evidence, and recovery receipts;
- orthogonal status enums;
- complete machine-error catalogue with stable JSON paths;
- schema registry and exact schema digests.

No I/O enters `contracts.py`.

### Workstream B1-B — State machine

Define the pure actions and transition inputs/outputs before implementing the reducer:

```text
CREATE_RUN
REGISTER_INPUT_SNAPSHOT
CLAIM_INVOCATION
RECORD_LAUNCH_INTENT
ATTACH_PROCESS_IDENTITY
RECORD_TERMINAL_RESULT
RECONCILE_RESOURCES
PUBLISH_ATTEMPT_OUTPUTS
INVALIDATE_DEPENDENTS
COMMIT_LEAN_RECEIPT
COMMIT_EVIDENCE_ROOT
RECORD_RECOVERY_DECISION
REBUILD_PROJECTION
```

Freeze the invariants and exact status derivation rules from the control-plane report.

### Workstream B1-C — Formal specification

Implement:

- `RunCommit.tla` for object durability, head CAS, idempotency, crash, and recovery;
- `AttemptLifecycle.tla` for launch intent, process lifecycle, reconciliation, invalidation, and evidence closure;
- small TLC configurations with two controllers/runs and bounded objects/sequences;
- smaller unsymmetrized configurations;
- intentional mutations removing object-directory sync, head comparison, lock exclusion, idempotency binding, reconciliation ordering, and invalidation.

Apalache remains a secondary bounded check.

### Tests

- canonical byte goldens and round trips;
- duplicate/unknown/malformed/oversized inputs;
- media-type/schema mismatches;
- ID/path-confusion vectors;
- unknown major and allowed extension vectors;
- TLA+ positive configurations;
- each broken formal mutation produces a counterexample.

### Deliverables

- frozen schema/media/error registry;
- canonical encoding library;
- action/invariant registry;
- TLA+ specs/configs and checker receipts;
- cross-language golden vectors consumed later by Rust.

### Exit gate `G1`

- all schema negative/golden vectors pass;
- Python canonical bytes match checked-in golden bytes;
- SANY/TLC checks pass for required configurations;
- every intentional mutation yields a counterexample;
- Apalache bounded checks complete or record a tool limitation without replacing TLC;
- `ArtifactRefV2` has no authoritative locator;
- contracts import no v1 or I/O implementation;
- schemas are frozen for B2–B5; any later breaking change returns to G1 and invalidates downstream receipts.

---

## B2 — Rust platform/store helper

### Purpose

Implement the smallest syscall-level authority boundary needed by the deterministic slice.

### Workstream B2-A — Protocol and roots

- define a bounded versioned request/response protocol shared with Python;
- accept data through inherited FDs, not arbitrary authority paths;
- open authority roots once and retain directory FDs;
- verify kernel, mount ID/type, ext4 support profile, and helper version;
- return typed machine errors and protocol-action receipts.

### Workstream B2-B — Object store

Implement:

- safe `openat2`-rooted operations;
- streaming SHA-256/size calculation;
- short-write and `EINTR` loops;
- same-directory temp creation;
- file `fsync`;
- no-replace installation through `renameat2(RENAME_NOREPLACE)` with reviewed same-filesystem `linkat` fallback;
- blob-directory `fsync`;
- deduplication by complete size/digest verification;
- corruption fence/quarantine classification;
- verified object reads returning FDs/capabilities.

### Workstream B2-C — Run head and recovery

Implement:

- run directory creation and parent-directory sync;
- stable lock inode;
- exclusive OFD lock;
- strict current-head read and expected-head comparison;
- idempotency lookup against the committed event chain;
- same-directory head temp, file sync, atomic rename, directory sync, and re-read;
- typed unknown-commit outcomes;
- chain walk, cycle/sequence/state-root validation, and recovery classification;
- projection write/rebuild as non-authoritative operations.

### Workstream B2-D — Fault surface

Add test-build failpoints before integration:

```text
temp create
first/middle/final object write
object file sync
object install
object directory sync
event file/directory sync
run lock
head compare
head temp write/sync
head rename
run directory sync
head re-read
before acknowledgement
```

Inject short writes, `EINTR`, `ENOSPC`, `EDQUOT`, permission errors, sync `EIO`, destination collisions, corrupt existing objects, and mount-identity changes.

### Tests

- Rust unit tests for validators and syscall wrappers;
- Python/Rust canonical-vector parity;
- Hypothesis-driven protocol tests through the real binary;
- two-process same-object puts;
- two-process same/stale-head commits;
- same/different idempotency-key requests;
- process kill at every failpoint followed by a fresh-process recovery;
- projection deletion/corruption;
- special-file/symlink/path/mount attack vectors.

### Deliverables

- `platform-helper` release/test binaries;
- Python `store.py` typed client;
- ext4 process-kill and injected-error receipts;
- stable helper protocol/version.

### Exit gate `G2`

- object/head protocols match TLA+ actions and invariants;
- every failpoint recovers to an allowed old/new state;
- no committed head references missing bytes;
- acknowledged commits remain current or ancestral;
- stale branches never become committed;
- idempotency distinguishes identical retry from conflicting request;
- failed/unknown directory sync never returns committed success;
- arbitrary caller paths cannot reach authority operations;
- the helper passes Rust formatting, lint, unit, integration, and sanitizer/fuzz checks selected for the crate;
- no SQLite, GC, remote store, compression, or optimization entered scope.

---

## B3 — Pure controller and compatibility boundary

### Purpose

Implement deterministic policy without side effects and prove it agrees with the abstract model.

### Workstream B3-A — Pure reducer

Implement in `control.py`:

- immutable `RunStateV2`;
- one reducer from `(state, event) -> state`;
- exact state-root derivation;
- serial scheduler and invocation claiming;
- budget monotonicity;
- retry legality;
- transitive invalidation;
- evidence freshness;
- orthogonal status derivation;
- recovery decision mapping.

No subprocess, filesystem, clock, random, network, or model call enters the reducer.

### Workstream B3-B — Application service

Implement orchestration around abstract ports:

- resolve current verified head/state;
- compute proposed transition;
- call store/execution/assurance ports;
- commit event with expected head and idempotency key;
- return typed conflict/unknown/recovery results;
- rebuild projections only after commit.

Start with fake ports.

### Workstream B3-C — v1 import

Implement only read-only `compat_v1`:

- exact accepted/rejected behavior for inventoried v1 schemas;
- raw-byte preservation before parsing;
- classified `MigrationReportV2`;
- one-way creation of fresh v2 lineage;
- no v1 writer, mutation, alias, or downgrade.

### Tests

- reducer transition table and invariant tests;
- Hypothesis `RuleBasedStateMachine` against the in-memory abstract model;
- generated crashes, retries, invalidations, stale heads, projection loss, and evidence decisions;
- v1 accepted/rejected golden corpus;
- source tree byte comparison before/after import;
- fake-port launch/terminal/recovery scenarios.

### Deliverables

- `control.py`, `compat_v1.py`, and application service;
- model-conformance receipts;
- v1 migration/golden receipts;
- fake-side-effect deterministic scenario.

### Exit gate `G3`

- generated traces agree with `RunCommit`/`AttemptLifecycle` abstractions;
- replay from genesis is deterministic and matches stored state roots;
- projection contents cannot affect results;
- invalidation is transitively complete;
- retry cannot occur without a durable legal decision;
- process success does not upgrade any assurance/mathematical field;
- every inventoried v1 reader has golden behavior;
- v1 corpus remains byte-identical.

---

## B4 — Sandbox broker, launcher, and production profile

### Purpose

Create one enforceable no-network/no-secret execution boundary before integrating real commands.

### Workstream B4-A — Broker protocol

The root-owned broker accepts only:

- fixed profile ID/digest;
- registered toolchain/executable ID/digest;
- bounded argv array;
- immutable input snapshot ref;
- output contract;
- resource limits within profile ceilings;
- external monotonic deadline;
- explicit nonsecret environment values.

It rejects arbitrary systemd properties, bind paths, UIDs, capabilities, network requests, host paths, shell strings, seccomp policies, and authority-store access.

### Workstream B4-B — Transient unit compiler

Compile the fixed `linux.systemd.no-network.v1` profile:

- system-service `DynamicUser`;
- no capabilities or ambient capabilities;
- `NoNewPrivileges`;
- private user/PID/IPC/network/device/tmp namespaces;
- strict system/home/kernel/control-group protection;
- native-architecture release seccomp allowlist;
- restricted address families;
- cgroup-v2 CPU/memory/swap/pids/I/O accounting and limits;
- fixed-size tmpfs writable root;
- control-group kill and bounded stop;
- no ambient inherited environment or file descriptors.

Root installation is a distinct operator step. The build driver packages and validates files but never calls `sudo`.

### Workstream B4-C — Same-namespace launcher

Before `execve`, the launcher verifies:

- NNP and seccomp active;
- empty capability sets;
- expected UID/GID mappings;
- namespace identities;
- cgroup path and effective limits;
- exact inherited FD set;
- expected mount manifest and writable capacity;
- host canary unavailable;
- external network unavailable;
- host D-Bus/container/session sockets unavailable;
- launcher/profile/toolchain/seccomp digests.

Apply ABI-negotiated Landlock after the systemd mount view exists. Landlock remains an explicit optional gap in profile v1.

### Workstream B4-D — Output and cleanup

- drain stdout/stderr continuously;
- compute total byte counts and complete hashes;
- retain bounded views only;
- terminate on stream limit rather than silently succeeding;
- reconcile the entire unit/cgroup, not only the leader;
- validate only regular-file outputs beneath the attempt root;
- transfer vetted output FDs/bytes to the unprivileged controller;
- delete broker attempt state after import/reconciliation;
- retain failure attestations.

### Tests

Run the complete adversarial suite from `V2_CONTROL_PLANE_REPORT.md` Section 13.5, including host-file/secret access, network and bus access, mount/namespace/ptrace/BPF/keyring/device attempts, fork/memory/output/disk exhaustion, resistant descendants, inherited-FD abuse, host signalling, and malicious output trees.

Also run positive command and Lean smoke probes using the pinned toolchain.

### Deliverables

- broker/launcher binaries;
- service/socket unit package;
- exact systemd profile and resolved seccomp manifest;
- Python `execution.py` client;
- capability and adversarial receipts;
- explicit installation/uninstallation procedure.

### Exit gate `G4`

- in-unit attestation disposition is `ENFORCED`;
- every hard capability is observed effective;
- every forbidden adversarial operation fails with a classified result;
- positive command and Lean probes work without broadening the whole profile;
- no secret canary appears in environment, argv, FDs, mounts, output, or `/proc`;
- resource attacks remain inside the unit and produce exact receipts;
- leader-first exit/resistant descendants leave the unit empty;
- no child, pump, lease, or attempt directory survives supervisor return;
- rootless backends, if tested, remain separately classified and cannot satisfy G4.

---

## B5 — Deterministic native vertical slice

### Purpose

Join the individually verified boundaries into one useful end-to-end v2 workflow.

### Workstream B5-A — Playbook

Implement only `math.receipt_first_formal_audit@2.0.0`:

```text
immutable input import
→ deterministic command
→ output validator
→ pinned Lean invocation
→ exact Lean receipt validator
→ continuation gate
→ evidence commit
```

The playbook is data/resources; execution remains in the fixed modules.

### Workstream B5-B — Assurance

Implement in `assurance.py` only what the slice needs:

- exact executable/toolchain/source/declaration binding;
- Lean exit/stdout/stderr/environment/import/axiom receipt;
- output schema/digest/cardinality validation;
- evidence root completeness/freshness;
- orthogonal implementation/formal/semantic/mathematical/assurance statuses;
- no theorem closure without its separately declared semantic requirements.

### Workstream B5-C — Facade

Add `agentic-lean-math-assistant-v2` commands:

```text
validate
import-v1
run
resume
inspect
verify-bundle
export
```

All commands return one stable result envelope and documented exit mapping. `inspect` and `export` are read-only projections.

### End-to-end scenario

1. Validate strict source/effective/playbook manifests.
2. Import and content-address all inputs.
3. Commit genesis and `RUN_CREATED`.
4. Commit durable launch intent.
5. Run deterministic command through the broker.
6. Reconcile/import output and commit terminal receipt.
7. Run pinned Lean through the broker.
8. Reconcile/import Lean evidence and commit receipt.
9. Apply continuation gate.
10. Commit evidence root and statuses.
11. Remove all projections and reconstruct state.
12. Inject crash at each helper/broker boundary.
13. Resume with the same idempotency keys.
14. Inspect and export; reverify every exported reference.

### Deliverables

- playbook package;
- `assurance.py` and `facade.py`;
- one frozen end-to-end fixture;
- successful and injected-failure bundles;
- full replay/resume receipt set.

### Exit gate `G5`

- the deterministic command and Lean invocations use the production broker/profile;
- launch intent precedes every spawn;
- output publication follows process/resource reconciliation;
- no committed invocation repeats after crash/resume;
- projection deletion reproduces byte-identical derived state;
- evidence root binds exact inputs, contract, playbook, toolchain, execution attestation, outputs, Lean receipt, and status derivation;
- all known stale-output, false-closure, process, secret, replay, and publication-relevant v1 incidents represented in the slice fail closed;
- no network or secret capability was used;
- scheduler stayed serial;
- no retained v1 byte changed.

---

## B6 — Qualification and destructive verification

### Purpose

Prove the integrated candidate under concurrency, process death, and actual power loss without adding features.

### Workstream B6-A — Concurrency qualification

- two controllers put the same/different objects;
- two controllers prepare branches from one head;
- current/stale expected-head commits;
- identical/conflicting idempotency keys;
- two simultaneous sandbox units with isolated cgroup/resource state;
- claim/launch race and cancellation/timeout race;
- process identity reuse/stale registration scenarios.

Concurrency remains disabled in production config until this gate finishes.

### Workstream B6-B — Integrated kill matrix

Kill the helper, broker, controller, and supervised process at every named phase. After a fresh process starts:

- recover from durable bytes only;
- classify committed-existing versus safe-to-retry;
- assert no duplicate external invocation;
- assert old/new whole head only;
- assert no missing committed object;
- assert unit/cgroup and stream reconciliation.

### Workstream B6-C — VM power-loss matrix

On a disposable VM with the declared ext4 profile:

- place the authority root on a dedicated virtual disk;
- power off abruptly at each durability failpoint;
- reboot and recover before cleanup;
- retain kernel/filesystem/mount/tool/helper identities and logs;
- assert the same old/new/no-hybrid invariants;
- fence the profile if any unsupported outcome occurs.

### Workstream B6-D — Full regression and incident replay

Run:

- complete v1 test suite;
- all v2 Python/Rust/formal tests;
- v1 import golden corpus;
- retained incident scenarios;
- sandbox adversarial suite;
- end-to-end crash/resume slice;
- bundle verification from a fresh process.

### Exit gate `G6`

- all two-controller invariants pass;
- no child/pump/resource lease survives any path;
- every process-kill point recovers correctly;
- every abrupt ext4 power-loss point recovers correctly;
- full v1 baseline is unchanged;
- all v2 gates pass from clean state;
- concurrency may be enabled only for the exact tested cases; the public slice may remain serial;
- no unsupported filesystem/backend is described as supported.

---

## B7 — Candidate assembly and release review

### Purpose

Turn a passing tree into one immutable, inspectable candidate without changing behavior.

### Workstream B7-A — Build outputs

From a clean checkout/worktree and empty `build-v2/`:

1. bootstrap pinned cached tools with digest verification;
2. build Python wheel/sdist with fixed source-date metadata;
3. build Rust release binaries with `--locked` and recorded target/features;
4. package systemd units and sandbox/seccomp manifests;
5. package schemas/playbook/formal specs;
6. collect all gate receipts;
7. compute every digest and write canonical `candidate.json`;
8. verify the candidate in a second fresh process/environment.

Candidate manifest includes:

```text
source/baseline digest
v1 corpus digest
Python wheel/sdist refs
Rust binary refs
systemd unit/profile refs
schema/media/error registry refs
playbook ref
formal spec/config/tool/result refs
all test/fault/power-loss receipt roots
supported OS/filesystem/sandbox profile
unsupported capabilities
local trusted-writer authenticity limitation
installation/uninstallation instructions digest
```

### Workstream B7-B — Reproducibility check

Run two clean builds with the same pinned inputs and compare:

- canonical source/resource outputs must match byte for byte;
- candidate manifests must differ only in fields explicitly classified non-reproducible;
- binary/wheel differences are investigated, not waved away;
- any unavoidable nondeterminism is named and excluded from semantic identity with justification.

### Workstream B7-C — Independent release review

Review:

- all G0–G6 receipts and exceptions;
- root broker protocol and installation boundary;
- formal counterexamples and coverage;
- crash/power-loss evidence;
- v1 immutability evidence;
- status and authenticity limitations;
- absence of network/secrets/model routing;
- candidate install, smoke, verify, uninstall, and recovery procedures.

### Exit gate `G7`

- one immutable candidate manifest resolves and verifies every artifact;
- installation does not mutate retained v1 or grant the controller generic root/systemd authority;
- installed production sandbox self-attests `ENFORCED`;
- clean install → run → crash/resume → verify → uninstall scenario passes;
- implementation, formal, crash, sandbox, evidence, and compatibility statuses are separately passed;
- unsupported capabilities and authenticity limits are visible;
- no post-qualification behavior change entered candidate assembly.

---

## B8 — Deferred expansion after the deterministic candidate

This is a new approved program, not part of G7:

1. split provider/model client from untrusted tool execution;
2. build a non-generic provider proxy and secret capability;
3. add exact request/budget/provider receipts;
4. add Luna/Terra/Sol routing and calibration;
5. enable tested scheduler parallelism;
6. add additional mathematical playbooks;
7. add publication transaction and `Publication.tla`;
8. evaluate OCI runtime/VM and remote backends;
9. add approved garbage collection;
10. perform cutover only after new gates pass without weakening G7.

---

## 6. Build and verification commands

The build driver should make these logical commands stable. Exact underlying tool arguments are retained in receipts.

### 6.1 Bootstrap

```bash
uv sync --frozen --group dev
uv run python scripts/v2_build.py bootstrap
```

Bootstrap may populate a digest-checked local tool cache. Candidate/test commands run offline or fail if a pinned input is missing.

### 6.2 Developer checks

```bash
uv run ruff check src/agentic_lean_math_assistant_v2 tests/v2 scripts/v2_build.py
uv run mypy src/agentic_lean_math_assistant_v2 scripts/v2_build.py
uv run pytest tests/v2/contracts tests/v2/control tests/v2/compat
cargo fmt --manifest-path native/Cargo.toml --check
cargo clippy --manifest-path native/Cargo.toml --workspace --all-targets -- -D warnings
cargo test --manifest-path native/Cargo.toml --workspace --locked
uv run python scripts/v2_build.py formal
```

These are prospective commands. The build driver records the resolved command/version rather than relying on this prose as authority.

### 6.3 Store qualification

```bash
uv run python scripts/v2_build.py store-test
```

Runs canonical parity, two-process cases, fault injection, kill/recovery, and security vectors on the declared local ext4 test root.

### 6.4 Sandbox package/install/test

```bash
uv run python scripts/v2_build.py sandbox-package
# build driver prints exact privileged install command; operator executes it separately
uv run python scripts/v2_build.py sandbox-test
```

No developer test may substitute a rootless backend for the production G4 receipt.

### 6.5 Slice and candidate

```bash
uv run python scripts/v2_build.py slice-test
uv run python scripts/v2_build.py powerloss-test
uv run python scripts/v2_build.py candidate
uv run python scripts/v2_build.py verify-candidate <candidate.json>
```

`candidate` refuses to run unless every required upstream receipt is present, digest-valid, from the frozen source/toolchain inputs, and passed.

---

## 7. Test ownership and locations

| Contract | Primary test location | Release evidence |
|---|---|---|
| Canonical bytes/schemas | `tests/v2/contracts/` | golden/negative vector receipt |
| v1 compatibility | `tests/v2/compat/` | accepted/rejected corpus and byte-identity receipt |
| Pure reducer/state | `tests/v2/control/` | transition and Hypothesis trace roots |
| Formal invariants | `formal/` | TLC/Apalache configurations and results |
| Rust store primitives | `native/platform-helper/` tests + `tests/v2/store/` | unit/fault/kill/recovery receipt |
| Broker/launcher/profile | native tests + `tests/v2/execution/` | capability/adversarial/unit-empty receipt |
| Lean/evidence | `tests/v2/assurance/` | exact Lean and evidence-root receipt |
| Vertical slice | `tests/v2/e2e/` | clean and crash/resume bundle |
| Historical failures | `tests/v2/incidents/` | incident replay matrix |
| Power loss | VM harness invoked by build driver | ext4 old/new/no-hybrid receipt |
| Candidate | build driver | canonical candidate manifest and verification receipt |

A test must defend an observable contract and fail under a plausible mutation. Source-text assertions and tests of incidental implementation shape do not count as release gates.

---

## 8. Change and review discipline

### 8.1 Contract changes

After G1:

- additive changes require schema/version and compatibility review;
- breaking changes increment the major identity;
- any change to event/head bytes, actions, status rules, idempotency, or capability semantics invalidates G1 and all downstream receipts;
- models and golden vectors change before implementations.

### 8.2 Privileged boundary changes

Any broker/launcher/systemd/seccomp change invalidates G4–G7. Review must verify:

- protocol remains fixed-profile rather than generic privileged execution;
- no new host path/property/capability selection entered caller control;
- effective in-unit probe covers the change;
- adversarial tests include its failure mode;
- uninstall/recovery remains bounded.

### 8.3 Store changes

Any order, flag, sync, lock, path, or recovery change invalidates G2 and G5–G7. Update the TLA+ abstraction first if semantics change.

### 8.4 Scope control

Reject during B0–B7:

- convenience aliases between v1 and v2;
- automatic repair of corrupt authority;
- mutable JSONL authority;
- generic shell execution in build or broker protocols;
- model-selected capabilities/models/tools;
- hidden retries;
- network exceptions;
- background services not owned by the sandbox unit;
- performance optimization before its correctness gate;
- dashboards or projections that become required for recovery.

---

## 9. Build receipts and status

Every build-driver invocation emits a canonical receipt:

```text
BuildStepReceiptV2 {
  step_id
  source_root_digest
  configuration_digest
  toolchain_manifest_digest
  executable + version + digest
  argv
  controlled_environment_names
  start/end/duration
  exit/signal
  stdout/stderr byte_count + digest + bounded_view
  produced_artifact_refs
  validation_results
  status = passed | failed | unsupported | skipped_by_capability
}
```

Rules:

- `skipped_by_capability` cannot satisfy a required gate;
- a process exit of zero is not a passing receipt until expected artifacts and validators pass;
- missing tool usage/cost data is `unknown`, not zero;
- privileged install/probe receipts name the effective systemd/kernel/boot identity;
- candidate assembly accepts only passed receipts bound to the frozen source/configuration root;
- all receipt projections can be regenerated from their immutable records.

---

## 10. Gate matrix

| Gate | Blocks | Required proof |
|---|---|---|
| `G0` Baseline | all native work | pinned tools; v1 inventory and unchanged baseline |
| `G1` Contracts/formal | store/control/broker implementation | strict vectors; TLC invariants; mutation counterexamples |
| `G2` Store | integrated slice | real helper fault/kill/concurrency recovery on ext4 |
| `G3` Pure control | integrated slice | reducer/model agreement; v1 golden import; status/invalidation invariants |
| `G4` Sandbox | real execution | production effective attestation and adversarial suite |
| `G5` Vertical slice | qualification | command+Lean+evidence crash/resume end to end |
| `G6` Qualification | candidate assembly | integrated concurrency, kill, incident, full regression, VM power loss |
| `G7` Candidate | release/use as v2 base | immutable manifest, clean install/run/recover/verify/uninstall, independent review |

No gate may be waived by model judgment or prose approval. A reduced-scope candidate requires a new named profile and explicit revision of this plan.

---

## 11. Definition of done

The v2 build process is done—not merely scaffolded—when:

- all G0–G7 gates pass on one frozen source/configuration root;
- every delivered file is reachable from and verified by `candidate.json`;
- v1 source, tests, retained runs, and behavior baseline remain unchanged;
- native v2 imports v1 only through `compat_v1`;
- CAS/head recovery reconstructs authority without projections;
- helper crashes and ext4 power loss yield only allowed whole states;
- production sandbox has no network/secrets, enforces all hard capabilities, and leaves no process/resource behind;
- deterministic command and pinned Lean run through that production sandbox;
- crash/resume does not duplicate a committed invocation;
- evidence root binds exact source, contracts, toolchain, execution, Lean, and assurance artifacts;
- status fields remain orthogonal and no theorem/campaign closure is inferred;
- unsupported filesystems, platforms, backends, authenticity, and optional defenses are explicit;
- candidate install and uninstall do not grant generic privilege or mutate v1;
- model-agent work remains deferred until separately approved.
