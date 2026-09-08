# Agentic Lean Math Assistant v2 — research and rebuild report

**Date:** 2026-08-26  
**Scope:** research, architecture, model routing, executable playbooks, migration, and acceptance plan  
**Repository baseline:** the frozen v1 corpus and `V1_SUPPORT.md` / `V1_SUPPORT.json`  
**Current mathematical truth:** CMV remains unresolved; this report does not upgrade any mathematical claim

---

## 1. Executive decision

Build v2 as a **clean native system beside v1**, then cut over through a strangler migration. Do not refactor the v1 controller into v2 and do not discard the v1 corpus.

The design has five defining choices:

1. **Code-owned orchestration.** A deterministic controller owns schemas, routing, capabilities, budgets, scheduling, retries, gates, invalidation, status, and closure. Models produce bounded artifacts; they do not control the workflow.
2. **Executable playbooks.** Replace campaign-specific prompt DAGs with immutable, semantically versioned mathematical SOPs. A playbook has typed inputs, a compiled step DAG, registered executors, validators, mandatory gates, receipts, invalidation rules, and a deterministic terminal result. Prompt files may be resources inside a playbook, but prompt text is not the protocol.
3. **Tiered model policy.** Luna executes known bounded language steps, Terra implements and reasons under known methods, and Sol is reserved for admitted frontier planning/invention or critical mathematical adjudication. Deterministic and formal/exact tools remain a separate authority lane.
4. **Artifact and event authority.** Immutable content-addressed artifacts and a hash-chained event head are authoritative. Human-readable projections, dashboards, filenames, process exit zero, and model prose are not.
5. **Orthogonal assurance.** Execution success, artifact validity, formal verification, semantic fidelity, mathematical closure, assurance, and publication are independent fields. A Lean proof proves the exact formal statement relative to its imports and axioms; it does not by itself prove faithful formalization of the source problem.

**Recommended initial routing envelope:** at least 60% Luna, at most 30% Terra, at most 10% Sol by model invocation, with Sol defaulting to zero unless an eligibility receipt exists. After calibration, target 70% Luna / 25% Terra / 5% Sol. Use actual token and provider-usage receipts for accounting; call shares are only a planning constraint.

**Recommended first vertical slice:** immutable input import → one command step → one Lean verification step → one explicit continuation gate → state/evidence commit → injected-crash resume → read-only inspection/export. It must use native v2 records only.

---

## 2. Evidence base and limits

### 2.1 Local evidence

This report treats the following as primary local evidence:

- `V1_SUPPORT.md`: the dense v1 audit, architecture reconstruction, incident ledger, model-routing policy, playbook contracts, minimal v2 architecture, migration sequence, and acceptance gates.
- `V1_SUPPORT.json`: the normative machine companion containing the per-file audits, run summaries, history audits, manifests, and structured v2 requirements.
- `src/agentic_lean_math_assistant/`: the maintained v1 package audited in the support record.
- `tests/`, `benchmarks/autonomy-calibration/`, `projects/cmv-strip-density/`, and retained campaign runs: behavioral and incident evidence catalogued by the support record.
- The current OMP model catalogue queried on 2026-08-26.

The support record reports a maintained v1 package of 18,764 Python lines, 301 passing tests and one skip in retained historical output, and an 8,707-job retained Lean build. Those are **historical v1 results**, not current v2 evidence and not rerun by this research-only task.

### 2.2 External research method

External sources were selected in this order:

1. primary standards and official documentation;
2. primary papers and official project repositories;
3. implementation documentation only where it exposes a reusable design constraint.

The external research does not replace local incident evidence. It is used to decide which v1 lessons generalize and which implementation patterns should be adopted, adapted, or rejected.

### 2.3 What this report establishes

This report establishes:

- a defensible v2 architecture;
- explicit controller/model boundaries;
- a versioned playbook contract;
- model eligibility and escalation rules;
- a migration and evaluation plan;
- concrete implementation order and acceptance criteria.

It does **not** establish:

- that v2 has been implemented;
- that a current frozen v2 commit passes any gate;
- that the CMV theorem is solved;
- that catalogue cost weights equal subscription billing;
- that hashes produced by one trusted writer prove cross-owner authenticity.

---

## 3. Research findings that matter for v2

### 3.1 Orchestration should be mixed, but authority should remain in code

OpenAI's Agents SDK documentation distinguishes LLM-led orchestration from orchestration via code and explicitly identifies speed, cost, and predictability as reasons to use code for flow control [S1]. It also recommends parallel execution only for genuinely independent work. That matches the strongest local finding: models are useful for mathematical content and local repair, but model-owned scheduling, retry, acceptance, and publication created ambiguity and waste.

**V2 consequence:** use models inside a deterministic state machine, not as the state machine. The controller compiles an approved plan or playbook into executable steps. Model output may propose mathematical content or capability needs; operational fields are overwritten or rejected.

### 3.2 Skills and SOPs are useful packaging conventions, not sufficient execution contracts

The Agent Skills specification defines a portable directory with a required `SKILL.md` and optional scripts, references, and assets; it recommends progressive disclosure and keeping the main file concise [S2]. OpenAI's skill-creation guidance similarly treats a skill as an onboarding guide containing workflow instructions and reusable resources [S3]. The Agent SOP specification adds parameters, ordered instructions, constraints, examples, and troubleshooting [S4].

These formats are good for human/model discoverability, but none by itself supplies the authority needed here: immutable input binding, output schemas, event ordering, capability grants, formal gates, receipts, invalidation, crash recovery, and deterministic closure.

**V2 consequence:** adopt the **package shape**, not the authority model. Each playbook package may contain Markdown guidance, prompts, scripts, schemas, fixtures, and references, but an authoritative machine manifest controls execution. Markdown cannot authorize a step, weaken a gate, or mark a result solved.

### 3.3 Durable workflow systems validate event-first state and replay discipline

Temporal defines workflow history as the complete ordered source of truth and reconstructs state by deterministic replay; external I/O, LLM calls, database access, and file operations occur as recorded activities rather than during replay [S5]. Temporal also warns that reordering command-producing workflow operations breaks deterministic replay and therefore requires explicit versioning [S6].

The project does not need Temporal as a dependency for the first local v2. It does need the same separation:

- pure reducer and scheduler decisions;
- side effects behind durable launch intents;
- event history as authority;
- versioned transition semantics;
- idempotent recovery rather than inferred recovery from files.

**V2 consequence:** every invocation has a durable intent before side effects and a terminal receipt after reconciliation. Replay consumes stored results; it never repeats external effects implicitly.

### 3.4 Formal theorem proving benefits from search interfaces and compiler-guided repair

Pantograph explicitly separates presentation, search, and kernel views and is designed to expose the search view for agents [S7]. Its rationale also states that tactic timeouts depend on cooperative cancellation and recommends controlled environments for memory leaks or non-cooperative tactics. LeanDojo-v2 combines repository tracing, structured theorem data, retrieval, Pantograph-based proof search, and external inference adapters [S8].

APOLLO reports that targeted Lean-compiler-guided decomposition and repair can improve proof success at much lower sampling budgets than broad repeated generation [S9]. LEAP similarly combines informal blueprints, decomposition, iterative Lean interaction, and agentic repair [S10]. Aristotle combines Lean proof search, informal lemma generation/formalization, and a dedicated geometry solver [S11]. DeepSeek-Prover shows the value of large-scale formal data but also illustrates the high sampling counts commonly used for whole-proof generation [S12]. LeanAgent adds a dynamic theorem database, curricula, and stability/backward-transfer concerns for lifelong learning [S13].

**V2 consequence:**

- treat Lean as a verifier and structured diagnostic source, not merely a terminal build command;
- preserve proof-state and repair artifacts between attempts;
- isolate failing sublemmas and retry only the affected proof cone;
- route known syntax/type/lemma repairs to Terra, not Sol;
- cap broad resampling and require a materially different method signature for a retry;
- sandbox proof search because a cooperative timeout is not process containment.

### 3.5 Discovery systems work when generators are coupled to objective evaluators

AlphaEvolve combines generation/mutation with automated evaluators and an evolutionary archive [S14]. Google's AI co-scientist uses generation, critique, ranking, evolution, and meta-review with asynchronous execution and test-time compute scaling [S15]. These systems support iterative invention, but their reusable lesson is not “add more agents.” It is “bind iteration to explicit evaluators, selection, and retained state.”

**V2 consequence:** Sol may propose distinct frontier methods, but a controller-selected falsification pilot and verifier determine whether a method survives. Failed methods remain in the archive with a stable method signature so the system does not pay to rediscover them.

### 3.6 Kernel acceptance is necessary but does not establish benchmark or source fidelity

A 2026 audit of five Lean theorem-proving benchmark families reports thousands of findings, including mechanically certified counterexamples, vacuous theorems, unsound axioms, missing hypotheses, simplified translations, and evaluation-harness failures [S16]. The core point matches the CMV incident record: the kernel checks whether a term proves a formal statement, not whether that statement faithfully represents the intended informal theorem.

**V2 consequence:** a theorem-claiming workflow requires two independent gates:

1. formal/exact verification of the declaration, build, dependencies, and axioms;
2. semantic/source review binding the same source digest, target, declaration type, and toolchain.

For high-impact informal-to-formal equivalence, a human remains authoritative. A model may produce a structured review but cannot close the semantic gate.

### 3.7 Cost-aware routing is useful only when calibrated against task outcomes

RouteLLM demonstrates that routing between weaker and stronger models can reduce cost while preserving benchmark quality, but it learns from preference data and evaluates the router empirically [S17]. The local system currently has policy rules but no v2 routing calibration corpus.

**V2 consequence:** start with deterministic eligibility rules, then calibrate on frozen incidents. Do not infer model capability from price or names. Measure false closure, verifier yield, repair cost, latency, and final obligation closure for every route.

### 3.8 Trace evaluation should precede aggregate benchmark claims

OpenAI's agent-evaluation guide recommends using complete traces to debug tool selection, handoffs, instruction violations, and routing changes, then moving to repeatable datasets and eval runs [S18]. OpenTelemetry's GenAI conventions define spans for agent invocation, workflow invocation, planning, and tool execution, plus model and token attributes, but the conventions are still marked development [S19].

**V2 consequence:** preserve a richer internal receipt schema than OpenTelemetry, then export a lossless subset to OpenTelemetry. Internal authority must not depend on a development telemetry convention. Every routing evaluation should retain the full decision trace and exact artifacts before aggregating metrics.

### 3.9 Provenance standards support export, but do not replace internal commit authority

W3C PROV-O provides an interoperable provenance model [S20]. RO-Crate defines a file-oriented JSON-LD research object containing data and contextual entities [S21]. Workflow Run RO-Crate extends RO-Crate to represent workflow executions, inputs, outputs, code, and step-level provenance [S22]. SLSA defines provenance as verifiable information about where, when, and how an artifact was produced [S23]. in-toto emphasizes transparency about which steps ran, by whom, and in what order [S24]. Reproducible Builds documents environmental variance, stable inputs/outputs, timestamps, randomness, build paths, and checksums [S25].

**V2 consequence:**

- model the internal run as typed events, artifacts, agents/principals, activities, and derivations;
- export verified runs as Workflow Run RO-Crate and optionally PROV-compatible graphs;
- emit in-toto-style attestations for build and publication steps where appropriate;
- record environment/toolchain digests and separate reproducibility from mere successful execution;
- never claim authenticity solely because a bundle's internal hashes agree. A writer able to replace the bundle can replace hashes too.

### 3.10 Process identity must not be a bare PID

Linux `pidfd_open` returns a file descriptor referring to a task, can be polled for exit, waited on for child processes, and signalled through pidfd APIs; the documentation explains why `/proc/<pid>` handles and bare PIDs are weaker [S26].

**V2 consequence:** on supported Linux systems, bind process ownership to pidfd plus PID, start time, process group, session, and boot/generation identity. A process-group signal requires reauthentication. On unsupported platforms, report reduced capability and fail closed for support statements that require strong descendant containment.

---

## 4. Current-state diagnosis

### 4.1 What should be preserved

Preserve these v1 lessons as contracts, not copied architecture:

- strict parsing and exact-key validation;
- append-only evidence and incident retention;
- immutable input snapshots;
- claim IDs separate from claim content;
- explicit producer/verifier relationships;
- Lean declaration, source, toolchain, and axiom binding;
- targeted downstream invalidation;
- deterministic publication approval binding;
- retained stdout, stderr, commands, timing, and outputs;
- negative tests for stale artifacts, false closure, tampering, process leaks, and publication crashes.

### 4.2 What should not be carried into native v2

Do not carry forward:

- the `CampaignBuilder` controller monolith;
- format dispatch by filename, basename, path layout, or field presence;
- generic `complete`, `success`, or `PASS` fields crossing dimensions;
- prompt text as the executable protocol;
- independent registry families without one schema registry;
- model-proposed tools, retries, statuses, failure policy, or continuation;
- inferred success from process exit or output-file existence;
- shared mutable Lean/build workspaces;
- automatic whole-plan regeneration for a local schema defect;
- unbounded no-output tasks;
- publication from live workspace paths;
- v1 readers or writers in native v2 modules.

### 4.3 Why a clean rebuild is lower risk than refactoring

The v1 audit found authority, execution, storage, assurance, publication, outer lifecycle, and compatibility concerns braided through large modules. Refactoring those modules while preserving every historical behavior would keep ambiguous authority boundaries alive and make it difficult to know whether a change is a v1 compatibility fix or a v2 semantic change.

A clean parallel implementation provides three explicit boundaries:

- **v1 executable specification:** immutable corpus and golden behavior;
- **one-way compatibility importer:** the only code allowed to interpret v1;
- **native v2 authority:** records and behavior that never serialize as v1.

This keeps the valuable failure corpus without treating accidental v1 behavior as the new design.

---

## 5. Native v2 architecture

### 5.1 Module map

The initial native package should contain exactly these responsibility modules:

| Module | Sole responsibility | Key interfaces |
|---|---|---|
| `v2.contracts` | Immutable value types, canonical encoding, schemas, identifiers, DAGs, status enums, source/effective/run snapshots, playbook definitions, registration metadata | `SchemaRegistry`, `ArtifactRefV2`, `PlaybookDefinitionV2`, `CampaignSourceManifestV2`, `EffectiveCampaignConfigV2` |
| `v2.compat_v1` | Quarantined exact-behavior v1 readers and one-way import | `v1_import`, `import_bundle_v1` |
| `v2.store` | Safe filesystem, content-addressed artifacts, immutable snapshots, typed event chain, commit head, projection cache, evidence commits, workspace transactions | `ArtifactStore`, `CampaignStateStore`, `WorkspaceTransaction`, `EvidenceCommitV2` |
| `v2.control` | Pure reducer, serial scheduler, budgets, routing, retry/invalidation closure, approvals, playbook compilation, deterministic result derivation | `StateMachine`, `Scheduler`, `BudgetGovernor`, `PlaybookCompiler`, `CampaignApplicationService` |
| `v2.execution` | Unified command/agent/Lean/Herdr supervision, sandbox abstraction, resource ledger, shutdown/recovery | `ExecutionSupervisor`, `SandboxBackend`, `ResourceLedger`, `ShutdownCoordinator` |
| `v2.assurance` | Handoffs, typed claim DAG, verifier verdicts, Lean receipts, semantic review, obligation closure, provenance joins, inspection, outcome derivation | `ClaimLedgerV3`, `LeanVerificationReceiptV2`, `SemanticReviewV2`, `CampaignOutcomeV3` |
| `v2.publication` | Approval-bound destructive publication and crash recovery | `PublicationPlanV2`, `PublicationApprovalV2`, `PublicationTransactionV2` |
| `v2.facade` | Thin API/CLI composition, explicit schema negotiation, rendering, compatibility command names | `CommandResultEnvelope`, CLI entry points |

Playbook packages live under a data/resource tree, for example `src/agentic_lean_math_assistant_v2/playbooks/`, but execution remains in `contracts`, `control`, `execution`, and `assurance`; do not create a ninth authority module solely to hold prompts.

### 5.2 Dependency rules

- `contracts` imports no v1 code and performs no I/O.
- `compat_v1` is the only native module allowed to import v1 schema implementations.
- `store` depends only on `contracts`.
- `control` depends on contracts and abstract store/execution/assurance/publication ports.
- `execution` depends on contracts and store.
- `assurance` consumes verified immutable store snapshots.
- `publication` consumes verified immutable artifact references, never live workspace paths.
- `facade` composes modules but contains no durable-state logic.
- No dependency points from a lower authority layer to a higher convenience layer.

### 5.3 Authoritative state model

Use immutable event objects rather than an append-in-place JSONL file as the primary local authority:

1. encode a `RunEventV2` canonically;
2. store it as a content-addressed object;
3. include predecessor hash, sequence, transition, actor, implementation digest, idempotency key, and subject digests;
4. fsync the event object and directory;
5. atomically compare-and-swap the run's commit head under the run lock;
6. derive `state.json` only as a digest-bound cache.

`events.jsonl` may be exported for humans and external tools, but deletion or corruption of the projection cannot alter authority. Rebuilding from the validated head must reproduce the same `RunStateV2`.

### 5.4 Canonical encoding

Every durable native record must have:

- `artifact_type`;
- `schema_version` as SemVer;
- `producer_version` and minimum reader version;
- strict required and allowed fields;
- stable machine error code and JSON path;
- explicit compatibility and migration policy;
- canonical UTF-8 I-JSON representation;
- sorted keys and a fixed final-newline rule;
- finite numbers only;
- non-boolean integer enforcement;
- duplicate-key rejection before object construction;
- a declared digest domain.

Unknown major versions fail closed. Minor-version extensions are allowed only inside a declared `extensions` object. The parser and hasher must consume the same bounded immutable bytes.

### 5.5 Artifact references

`ArtifactRefV2` is the only durable artifact identity:

```text
namespace
digest
size
kind / media_type
schema_ref
producer {run_id, playbook_id, step_id, attempt_id, invocation_id}
input_root
contract_digest
execution_attestation_digest
assurance_class
locator
```

The locator is retrieval/display metadata. A path string, basename, or existing file cannot satisfy an artifact binding. Opening a retained object resolves through the store and revalidates the digest/size under the applicable capability.

### 5.6 Trust scope

The first release may declare a **local trusted-writer** scope. Within that scope, hashes and commit heads establish consistency, lineage, and replay binding. They do not establish authenticity against a principal that can rewrite the complete store.

Expose at least:

- `integrity_status`;
- `authenticity_status`;
- `reproducibility_status`;
- `support_scope`;
- `unsupported_capabilities`.

Cross-owner export or remote execution should remain unsupported until the ownership model and signing/MAC policy are approved and tested.

---

## 6. Executable playbooks

### 6.1 Definition

A `PlaybookV2` is an immutable, semantically versioned, evidence-gated program over typed artifacts. The controller resolves and compiles it; executors run its steps; validators and gates decide step admissibility; the controller derives the result.

A playbook is successful only when every mandatory step, output, receipt, validator, audit, and gate passes. Playbook success means the SOP executed correctly. It does **not** mean the campaign or theorem is solved.

### 6.2 Package layout

Recommended package layout:

```text
playbooks/<namespace>/<name>/
  playbook.toml             # authoritative manifest
  SKILL.md                  # concise model/human guidance; non-authoritative
  schemas/                  # exact input/output/decision schemas
  prompts/                  # versioned prompt resources
  scripts/                  # deterministic generators/checkers/adapters
  references/               # bounded supporting material
  fixtures/                 # positive, negative, mutation, recovery cases
  migrations/               # declared definition/schema migrations
```

`playbook.toml`, referenced schemas, scripts, prompts, and fixtures are all hashed into the definition digest. Editing a prompt changes the implementation digest even when the public playbook revision remains compatible. A semantic, gate, output-schema, invalidation, diversity, or executor-policy change requires a new playbook revision.

### 6.3 `PlaybookDefinitionV2`

Required fields:

```text
playbook_id, revision, title, purpose, risk_class
capability_ids
input_schema_refs, parameter_schema_ref
preconditions
steps
outputs
gates
invalidation
audit
budget
failure_policy
receipt_profile
compatibility
implementation_digest
status, approved_by, approval_receipt
```

Compile-time checks:

- unique step, output, predicate, and gate IDs;
- acyclic known step DAG;
- every binding resolves exactly once;
- every mandatory output is reachable;
- every capability, schema, tool, verifier, handoff, and timeout/retry policy is registered;
- every required evidence class has an authority-producing step;
- exactly one terminal derivation path for each allowed outcome;
- mandatory budgets are finite;
- mandatory gates are fail-closed;
- mutation and retention policies are explicit.

### 6.4 Step contract

`StepSpecV2` contains:

```text
step_id
kind
depends_on
mandatory
executor_role
capability_ids
input_bindings
output_bindings
command_or_protocol_ref
timeout_policy_id
retry_policy_id
checkpoint_policy_id
mutation_policy
evidence_class
falsifies
on_success
on_failure
```

The manifest names abstract executor roles. The controller resolves concrete models and tools from the effective policy at run compilation and records that resolution. A model cannot select its own tier, tool, timeout, retry count, workspace, or transition.

### 6.5 Registered step kinds

Initial step kinds:

- `controller.bind`
- `controller.preflight`
- `controller.route`
- `luna.execute_known`
- `luna.render_extract`
- `terra.maintain`
- `terra.reason`
- `terra.audit`
- `sol.plan_frontier`
- `sol.revise_frontier_plan`
- `formal.verify`
- `controller.checkpoint`
- `controller.gate`
- `controller.invalidate`
- `controller.reconcile`
- `human.approve`
- `controller.publish_artifact`
- `controller.derive_result`

Sol is intentionally absent as an ordinary executor. Sol emits a frontier plan or a validator-directed revision; the controller validates and compiles it into Luna/Terra/formal/deterministic steps.

### 6.6 Universal gates

Every playbook receives these non-removable gates:

| Gate | Required decision |
|---|---|
| `U0_definition_and_binding` | Approved definition, exact revision/digest, resolved schemas/registries, immutable inputs, contract/policy/toolchain bindings, acyclic DAG |
| `U1_preflight_and_budget` | Capability, path, toolchain, source, sandbox, falsification, and budget checks pass before side effects |
| `U2_receipt_completeness` | One durable launch and terminal receipt per invocation; process/resource reconciliation complete |
| `U3_output_schema_and_hash` | Exact schemas, cardinality, bindings, hashes, sizes, mutation policy, and atomic publication pass |
| `U4_invalidation_freshness` | Dependency fingerprint unchanged; transitive stale closure empty for required evidence |
| `U5_independent_audit` | Required producer/verifier independence and formal/exact authority satisfied |
| `U6_terminal_derivation` | Result derived from mandatory step/gate/output state, never prose or generic process success |

### 6.7 Continuation gates

An expensive descendant cannot start unless a `GateDecisionV2` contains:

- exact subject and pilot artifact digests;
- accepted, rejected, and unresolved claim IDs;
- falsification and validation results;
- budget remaining;
- `decision=continue`;
- controller or authorized human decider;
- policy digest and event sequence.

Missing output, malformed JSON, timeout, process exit zero, `failure_policy=continue`, or model prose never imply continuation.

### 6.8 Invalidation

Any change to these fields invalidates affected descendants transitively:

- target or success contract;
- source/input root;
- playbook revision or implementation digest;
- schema/feature/tool registry digest;
- effective routing/security/budget policy;
- executable or toolchain identity;
- allowed axioms;
- producer output digest;
- verifier rubric;
- semantic declaration binding;
- approval subject.

Invalidated artifacts remain retained as `STALE`; they are never rewritten or deleted. Re-execution creates new descendants.

### 6.9 Failure classes

Use exact failure classes:

```text
CONTRACT
SCHEMA
INFRASTRUCTURE
RESOURCE
EVIDENCE_INTEGRITY
FORMAL_REJECTION
MATHEMATICAL_REFUTATION
UNRESOLVED_MATH
SEMANTIC_UNCLEAR
POLICY_DENIAL
APPROVAL_REQUIRED
BUDGET_EXHAUSTED
RECOVERY_FAILED
```

Retryability and escalation are registered per machine code. Malformed output, timeout, missing dependency, sandbox failure, tampering, formal rejection, and deterministic refutation do not escalate to a more expensive model.

---

## 7. Initial mathematical playbook catalogue

The first catalogue should be small and derived from repeated CMV failure modes. Do not create a generic “research mathematician” playbook.

### 7.1 `math.source_contract_audit@2.0.0`

**Purpose:** turn primary-source statements into a frozen, locator-complete formalization contract.

**Inputs:** source artifact digests, target statement, candidate formal declarations, terminology/domain schema.  
**Core steps:** deterministic source inventory → Luna structured extraction → Terra reconstruction/audit → independent Terra audit → human semantic approval for authoritative equivalence.  
**Outputs:** source ledger, exact quotations/locators, formula/domain/branch table, ambiguity ledger, formalization contract, semantic decision.  
**Required evidence:** `source_derived`; `semantic_human_approved` for theorem closure.  
**Failure conditions:** missing source bytes, unresolved locator, target-changing interpretation, formula repaired without explicit hypothesis, or reviewer coverage gap.

This playbook directly addresses the missing CMV source audit and prevents a source-to-Lean claim from being inferred from downstream compilation.

### 7.2 `math.receipt_first_formal_audit@2.0.0`

**Purpose:** authenticate reported Lean claims before assigning `formal_audited`.

**Inputs:** immutable Lean project snapshot, exact target declaration/type, toolchain/dependency roots, allowed-axiom policy.  
**Core steps:** root-import generation → clean isolated build → exact declaration query → structured axiom collection → `sorry`/`admit`/unsafe/custom-axiom scans → mutation controls → replay.  
**Outputs:** declaration/type hash, import root, build receipt, axiom receipt, source/toolchain hashes, replay recipe, limitations.  
**Required evidence:** `formal_audited`.  
**Does not prove:** source fidelity, non-vacuity, candidate completeness, theorem novelty, or informal equivalence.

### 7.3 `math.typed_claim_dag_reconciliation@2.0.0`

**Purpose:** reconcile claims, corrections, formal receipts, numerical results, source evidence, and reviews without laundering scope.

**Inputs:** claim proposals, verifier verdicts, promotion records, correction records, evidence refs, obligation registry.  
**Core steps:** canonical content hashing → dependency validation → exact verdict coverage → disagreement preservation → authority join → invalidation closure → terminal claim projection.  
**Outputs:** `ClaimLedgerV3`, unresolved obligations, rejected claims, stale evidence, promotion decisions.  
**Required evidence:** `deterministically_verified`; stronger labels remain attached only to their originating receipts.

### 7.4 `math.proof_producing_certificate_generation@2.0.0`

**Purpose:** convert exact-decimal, rational interval, or bounded numerical reasoning into replayable proof objects or Lean-checkable certificates.

**Inputs:** scalar contract, complete domain partition, exact formulas, branch policy, precision policy, checker/toolchain identities.  
**Core steps:** domain normalization → deterministic box generation → Terra implementation/repair → exact checker → mutation suite → optional Lean import → independent audit.  
**Outputs:** box ledger, generated checker/proof source, coverage proof, endpoint/join receipts, mutation receipts, replay manifest.  
**Required evidence:** `proof_object_checked` or `interval_certified`; numeric telemetry is separate.  
**Failure conditions:** uncovered region, overlap/gap ambiguity, non-directed rounding, unbound precision, missing endpoint, or a mutation that should fail but passes.

### 7.5 `math.equal_area_fold_root_topology@2.0.0`

**Purpose:** prove complete equal-area root topology, fold behavior, least-perimeter root selection, and endpoint cases.

**Inputs:** exact area map, domain and branch specification, derivative/monotonicity data, candidate perimeter function.  
**Outputs:** complete root-set theorem/certificate, fold points, branch coverage, root-selection theorem, endpoint cases, limitations.  
**Required evidence:** formal or proof-object evidence.  
**Rejected substitute:** a numerical continuation path or one discovered root.

### 7.6 `math.frontier_to_reduced_boundary@2.0.0`

**Purpose:** bridge modeled topological-frontier Hausdorff-measure perimeter to source finite-perimeter/BV reduced-boundary semantics.

**Inputs:** explicit carriers and interfaces, source perimeter definition, regularity assumptions, null-set convention.  
**Outputs:** bridge theorem, interface/join/crack ledger, trace conditions, excluded singular cases.  
**Required evidence:** source contract plus formal/exact bridge.  
**Human gate:** any target-changing interpretation of source perimeter semantics.

### 7.7 `math.full_domain_gamma_certificate@2.0.0`

**Purpose:** prove a gap-free sign result over the full declared parameter domain by joining low, compact, and asymptotic regimes.

**Inputs:** exact Γ contract, domain partition, low-density proof, compact certificate, large-density tail, uniform boundary rules.  
**Outputs:** complete interval ledger, join receipts, endpoint coverage, formal sign theorem or proof object.  
**Required evidence:** `formal_audited`, `proof_object_checked`, or `interval_certified` with no gaps.  
**Rejected substitute:** MPFR telemetry without a proof-producing enclosure or a human synthesis across unverified joins.

### 7.8 Operational recovery playbooks

Implement after the mathematical vertical slice is stable:

- `ops.no_output_process_recovery@2.0.0`;
- `ops.authoritative_state_and_stale_artifact_recovery@2.0.0`;
- `ops.publication_transaction_recovery@2.0.0`.

These are deterministic operational playbooks. They never route to Sol.

---

## 8. Model allocation and escalation

### 8.1 Current catalogue facts

The OMP catalogue on 2026-08-26 reports:

| Tier | Selector | Context | Max output | Input / output / cache-read / cache-write weights |
|---|---|---:|---:|---|
| Luna | `openai-codex/gpt-5.6-luna` | 272k | 128k | 0.2 / 1.2 / 0.02 / 0.25 |
| Terra | `openai-codex/gpt-5.6-terra` | 272k | 128k | 2 / 12 / 0.2 / 2.5 |
| Sol | `openai-codex/gpt-5.6-sol` | 272k | 128k | 5 / 30 / 0.5 / 6.25 |

Across the catalogue dimensions, Luna is 0.04× and Terra 0.4× the Sol weight. These are catalogue weights, not dollar prices or subscription quota rules.

### 8.2 Route matrix

| Lane | Eligibility | Work | Prohibited authority |
|---|---|---|---|
| Deterministic | Known algorithm/policy or machine oracle; any identity/security/state/budget/closure decision | parsing, hashes, paths, DAGs, scheduling, budgets, exact arithmetic, Lean invocation, replay, benchmark checking, status derivation | prose inference when a machine field exists; model fallback for malformed or unsafe state |
| Luna | Exactly one approved playbook; bounded extraction/rendering/normalization; exact schema and validator; no truth/security/continuation field | source extraction, report rendering, known command/protocol execution, schema migration proposal with deterministic validation | unresolved mathematics, tool choice, retries, status, claims, gates, publication |
| Terra | Known method requires substantive code, cross-artifact reasoning, routine mathematics, formal repair, or independent audit | execution-kernel implementation, routine Lean repair, checker implementation, source/formula reconstruction, clean-room review | controller redesign, target changes, self-approval, closure |
| Sol | Valid frontier or critical-adjudication eligibility receipt | frontier decomposition, mathematically distinct invention, one field-level plan revision, high-impact mathematical adjudication as a third identity | routine coding, parsing, process recovery, scheduler design, ordinary Lean repair, execution, continuation, solved status |
| Human | Nondelegable semantic, security, publication, corruption, contract, or source/license authority | freeze/approve contracts, authoritative informal-to-formal equivalence, destructive publication, exceptions | waiver of kernel failure, deterministic refutation, missing evidence, or fabricated receipts |
| Formal/exact verifier | Registered oracle exists | Lean kernel/build/axiom audit, exact arithmetic, certificate replay, deterministic counterexample | replacement by model consensus |

### 8.3 Deterministic routing algorithm

For every task or unresolved obligation:

1. Freeze task, target, source, contract, policy, allowed-axiom, artifact, and output-schema identities.
2. Reject malformed, stale, unsafe, unauthorized, incompatible, tampered, or over-budget inputs.
3. Match playbooks by typed capability/precondition registry, never prompt keywords.
4. Run cheap falsification and prior-success replay.
5. Execute deterministic work wherever a machine implementation and oracle exist.
6. Route bounded language work to Luna only if every Luna predicate passes.
7. Route ordinary substantive work under a known method to Terra.
8. Classify failures before considering a retry.
9. Emit frontier eligibility only for a mandatory unresolved mathematical obligation after cheaper paths are exhausted.
10. Admit Sol only with the eligibility receipt and finite Sol budget.
11. Validate/compile Sol's plan deterministically.
12. Require explicit continuation before expensive descendants.
13. Compute claim and obligation closure deterministically.

### 8.4 Retry and escalation rules

**Luna limit:** one initial call plus one syntax/omission repair. A second invalid result is `MODEL_CONTRACT_FAILED`. Blank output, malformed JSON, timeout, missing dependency, and sandbox failure route to deterministic recovery, not Terra.

**Luna → Terra:** only when a schema-valid Luna artifact is substantively insufficient or fails a substantive deterministic verifier requiring cross-artifact/code/mathematical reasoning.

**Terra limit:** at most two materially distinct producer methods plus one clean-room Terra audit per obligation. A retry requires a typed limitation, a new method signature, an expected machine-checkable artifact, and remaining budget.

**Terra → Sol:** all conditions are mandatory:

- a primary mandatory obligation remains `UNRESOLVED_MATH`;
- deterministic falsification and every applicable playbook are exhausted;
- two materially distinct Terra methods have evidence, unless the frozen contract preclassifies the obligation as frontier;
- an independent Terra auditor confirms a mathematical rather than infrastructure/schema/resource/source/integrity gap;
- no exact counterexample, checker, or kernel rejection settles it;
- Sol and aggregate budgets remain;
- closure impact is material.

**Sol limits:** one initial plan plus one field-level validator-directed revision; at most two admitted invention attempts; one critical adjudication, with a second independent Sol only under an explicit critical-impact policy.

**Sol → human:** required for unresolved informal-to-formal correspondence, target-changing source interpretation, contract amendment, destructive publication, security exception, source/license exception, authenticity dispute, or irreconcilable independent adjudications.

### 8.5 Cost envelope

Because all four catalogue weight dimensions have the same tier ratios, an equal-token-profile approximation relative to all-Sol is:

\[
C_{\mathrm{relative}} = 0.04p_L + 0.4p_T + p_S,
\qquad p_L+p_T+p_S=1.
\]

- 60% Luna / 30% Terra / 10% Sol gives 0.244 of all-Sol catalogue weight: a 75.6% reduction under the equal-token-profile assumption.
- 70% Luna / 25% Terra / 5% Sol gives 0.178: an 82.2% reduction under the same assumption.

Actual reports must use input, output, cache-read, cache-write, and provider usage separately. Model tiers will have different prompt lengths and retry rates, so invocation share is not a billing estimate.

### 8.6 Subscription concurrency

Four subscriptions increase quota headroom and concurrent capacity. They do not automatically create reviewer independence. Independence is computed from provider, model family, checkpoint/version, organization, principal, and context lineage. Multiple accounts using the same provider/model/prompt lineage do not count as independent organizations or model families.

Use capacity lanes:

- Lane A: Terra implementation/coding;
- Lane B: Luna playbook execution and evidence extraction;
- Lane C: clean-room Terra or Sol review, never sharing producer context;
- Lane D: reserved Sol frontier/adjudication capacity.

Build directories, writable workspaces, evidence destinations, and process registries must be isolated before increasing parallelism.

---

## 9. Evidence and status model

### 9.1 Nonfungible evidence classes

At minimum:

```text
formal_audited
exact_checked
proof_object_checked
interval_certified
deterministically_verified
source_derived
semantic_human_approved
independent_model_review
model_proposal
numeric_telemetry
operational_receipt
```

No averaging or rhetorical promotion is allowed. Numeric telemetry cannot become an interval certificate. Model agreement cannot become kernel evidence. Compilation cannot become source fidelity.

### 9.2 Claim records

Separate stable mathematical content from campaign-local identity:

- `claim_content_hash`: canonical statement, assumptions, domain, quantifiers, and scope;
- `claim_id`: campaign/run-local handle;
- dependency claim hashes;
- target/obligation mapping;
- evidence refs by class;
- producer identity;
- one verifier verdict per proposal claim;
- disagreements and adjudication;
- semantic relation/issues;
- limitations;
- current closure and invalidation head.

A verifier cannot repair a claim while judging it. Any statement, scope, hypothesis, quantifier, candidate universe, perimeter semantic, declaration, or endpoint change creates a new content hash and new review.

### 9.3 Orthogonal public status

Do not expose a generic `complete` field. Expose independent dimensions:

- implementation status;
- focused-test status;
- full-gate status;
- controller status;
- attempt lifecycle;
- process status;
- artifact validation status;
- formal verification status;
- semantic status;
- campaign status;
- mathematical status;
- assurance status;
- publication status;
- audit process status and audit verdict;
- incident status.

`CampaignOutcomeV3.derive` may return mathematically solved only when every required target and obligation closes on one frozen evidence commit, exact declaration/axiom contracts match, semantic review binds the same source/target/declaration/toolchain, required provenance and approvals validate, and every declared authenticity requirement is met.

### 9.4 Receipt fields

Every invocation must retain:

- envelope and event identity;
- routing predicates, selected/rejected routes, playbook and policy digests;
- exact model/provider/checkpoint/reasoning/decoding identity when applicable;
- exact executable/toolchain and wrapper hashes;
- prompt-template and rendered-input hashes;
- input artifact inventory and workspace root;
- capabilities, sandbox, environment, and network policy;
- launch intent, process/pidfd/group/session/resource identity;
- monotonic deadlines, heartbeats, checkpoints, terminal cause, exit/signal;
- stdout/stderr byte counts, complete hashes, bounded views, truncation flags;
- output refs and mutation manifest;
- validation codes, replay commands, formal/certificate receipts;
- token/resource/cost fields marked measured, estimated, or unknown;
- cleanup/reaping and recovery result;
- every orthogonal status field.

Timeout ceilings and catalogue weights are not consumption. Missing provider usage remains `unknown` with a reason.

---

## 10. Execution, sandbox, and recovery

### 10.1 One supervisor lifecycle

All command, agent, Lean, and Herdr adapters use one lifecycle:

```text
capability validation
→ durable launch intent
→ sandbox preparation and attestation
→ spawn
→ process identity attachment
→ bounded byte-stream drain and hash
→ deadline/quota decision
→ termination and reaping
→ cleanup reconciliation
→ atomic attempt publication
```

No pump thread, child, or resource lease may outlive `ExecutionSupervisor.run`. Output publication occurs only after process/resource reconciliation.

### 10.2 Process identity

On this Linux workstation, prefer pidfd creation/attachment plus:

- PID;
- process start time;
- process-group ID;
- session ID;
- boot ID or controller generation;
- cgroup/systemd unit identity when used.

Before signalling any member or group, reauthenticate identity. If ownership is ambiguous, do not signal and return a typed containment failure. `stop_run` and `stop_all` are idempotent and resume from durable phase receipts.

### 10.3 Sandbox policy

Default untrusted execution:

- minimal allowlisted environment;
- no inherited subscription/API secrets unless explicitly required;
- read-only immutable inputs;
- attempt-scoped writable output;
- no network or user bus unless capability-authorized;
- isolated build/cache roots;
- disk, memory, CPU, process, output, and time limits;
- retained sandbox attestation.

The generic sandbox should default to enabled once the native vertical slice proves the full workflow through it. CMV may use an explicit local-trusted exception during bootstrap, but the exception must be visible in assurance status and cannot support a generic sandbox claim.

### 10.4 No-output watchdog

Require a checkpoint or health event by the earlier of 10 minutes or 25% of the task deadline. Without progress, stop or checkpoint by the earlier of 20 minutes or 50% of the deadline. A retry requires a successful health probe or material configuration correction.

A checkpoint must contain changed artifacts, exact progress measures, unresolved regions, logs, resumability metadata, and the method signature. Prose such as “still working” is not progress.

---

## 11. Evaluation plan

### 11.1 Evaluation layers

1. **Schema/property layer:** canonical encoding, duplicate keys, unknown versions, bounded values, DAGs, status transitions, invalidation.
2. **Store/crash layer:** fault injection at object write, file fsync, directory fsync, rename/head CAS, event, projection, evidence commit, and recovery.
3. **Filesystem/security layer:** traversal, absolute paths, symlinks, hardlinks, special files, parent swaps, concurrent writers, read-growth races, case collisions.
4. **Execution layer:** launch failure, normal exit, timeout, interruption, output truncation, leader-first exit, resistant descendants, PID reuse, stale registrations, cleanup failure.
5. **Playbook layer:** definition compilation, gate reachability, output cardinality, receipt completeness, invalidation, recovery, Luna/Terra/Sol legality.
6. **Assurance layer:** claim coverage, disagreements, semantic binding, Lean receipts, exact certificates, false-closure veto.
7. **Migration layer:** v1 accepted/rejected goldens, raw-byte preservation, classified defects, no mixed-version writes.
8. **End-to-end layer:** one native vertical slice and one injected-crash resume.
9. **External export layer:** Workflow Run RO-Crate/provenance export validates without becoming internal authority.

### 11.2 Routing calibration corpus

Build a frozen content-addressed corpus containing:

- known deterministic cases;
- bounded extraction/rendering cases;
- routine code and Lean repair cases;
- repeated v1 no-output, stale-artifact, false-closure, process, and publication incidents;
- at least 20 mathematical obligations split among known-playbook hard work, genuine frontier gaps, and high-impact conflicting evidence;
- corrected or independently audited formal benchmark slices, not raw benchmark scores assumed valid.

Ground-truth labels must include route, allowed escalation, expected evidence, expected failure class, and closure permission.

### 11.3 Hard routing invariants

Release requires:

- 100% deterministic routing for safety-critical schema/config/path/DAG/journal/metrics/exact/formal cases;
- no Sol call without a passing eligibility receipt;
- no model execution from a null adopted plan;
- no fail-open continuation;
- no false mathematical closure when external verification fails;
- no producer-as-reviewer or planner-as-adjudicator;
- no unreceipted invocation;
- no retry without a material method or infrastructure change;
- no generic `complete` state substituting for mathematical or assurance status.

### 11.4 Quality and cost metrics

Report per task class and tier:

- route confusion matrix;
- escalation precision and recall;
- first-pass schema validity;
- verifier pass rate;
- false-closure rate;
- obligation closure yield;
- retained novel artifact yield;
- retry count and method novelty;
- queue, setup, model, tool, verification, cleanup, and wall time;
- tokens and cache usage;
- measured cost or unknown reason;
- catalogue-weight estimate, clearly labeled;
- no-output and timeout incidence;
- artifact bytes retained;
- telemetry completeness;
- reviewer independence status.

Primary optimization order:

1. zero false closure and zero unauthorized Sol calls;
2. preserve or improve verified obligation closure;
3. reduce Sol usage;
4. reduce total normalized compute/cost;
5. reduce latency and retained waste.

### 11.5 Model-allocation experiment

Run the same frozen corpus under:

- all-Sol baseline;
- Terra planner + Terra workers;
- deterministic router with 60/30/10 cap;
- deterministic router with 70/25/5 target;
- one intentionally under-routed Luna-heavy condition to measure repair loops.

Each condition must use the same contract, source/artifact roots, playbook definitions, toolchains, and aggregate limits. Repeat enough times to expose stochastic variance. Any condition that introduces a false closure fails regardless of cost.

### 11.6 Trace review

Before trusting aggregate results, inspect representative complete traces for:

- wrong playbook selection;
- invalid handoffs;
- unauthorized capabilities;
- hidden retries;
- stale artifact reuse;
- output truncation;
- target or hypothesis drift;
- reviewer context leakage;
- verifier mismatch;
- gate bypass;
- incorrect failure classification.

Trace graders may assist triage, but deterministic invariants and formal checks remain authoritative.

---

## 12. Migration and coexistence

### 12.1 Physical separation

Use distinct roots:

```text
runs-v1/          # frozen read-only history
runs-v2/          # native v2 run heads and projections
artifacts-v2/     # immutable content-addressed objects
build-v2/         # attempt-scoped disposable build roots
tmp/v1-parity/    # disposable v1 compatibility execution only
```

Use separate lock roots, schema registries, runtime registries, caches, build roots, and pinned environments. A write fence rejects mutation targeting retained v1 history.

### 12.2 One-way import

For each v1 bundle:

1. acquire a stable read-only snapshot;
2. hash raw files and the raw root before interpretation;
3. parse only through `v2.compat_v1.v1_import`;
4. preserve observed accepted/rejected behavior and DTO values;
5. reject ambiguous or mixed-version objects;
6. create a fresh v2 lineage/run identity;
7. emit only native v2 records;
8. produce a `MigrationReportV2` listing defaults, normalizations, aliases, omissions, defects, unsupported assumptions, and blockers;
9. verify that the v1 source tree is byte-identical.

There is no v2-to-v1 downgrade and no native v2 writer with a v1 schema identity.

### 12.3 Implementation sequence

#### Phase 0 — Freeze and fence

- Pin the v1 source commit, environments, CLIs/APIs, schemas, good/bad/incident bundles, tests, and exit mappings.
- Make retained v1 history read-only.
- Record a consumer inventory.

**Exit:** byte-preserving corpus snapshot and enforced write fence.

#### Phase 1 — Contracts and compatibility

- Implement strict canonical encoding and base value types.
- Implement the schema registry and playbook definition parser/compiler checks.
- Implement `v2.compat_v1` golden readers and migration reports.

**Exit:** every inventoried v1 reader has accepted/rejected golden vectors; native v2 records have distinct identities.

#### Phase 2 — Store and pure control

- Implement content-addressed objects, commit heads, event reducer, projection cache, evidence commits, run lock, serial scheduler, budget governor, routing, and invalidation.
- Use fake side-effect ports and model-based crash/state tests.

**Exit:** deleting projections and injecting store crashes reconstructs a unique valid prior or next state.

#### Phase 3 — Unified execution

- Implement the supervisor, sandbox abstraction, resource ledger, bounded streams, pidfd-aware process identity, watchdogs, shutdown, and reconciliation.
- Route command, agent, Lean, and Herdr adapters through it.

**Exit:** no child/pump survives return; all failure paths have launch and terminal receipts; ambiguous process ownership fails closed.

#### Phase 4 — First native playbook slice

- Implement `math.receipt_first_formal_audit@2.0.0` and the minimal playbook runtime.
- Execute immutable import → command → Lean verify → continuation gate → evidence commit → crash resume → inspect/export.

**Exit:** the slice uses only v2 authority records and reproduces exactly after crash recovery.

#### Phase 5 — Assurance and mathematical playbooks

- Implement typed claims/verdicts, semantic review, obligation closure, and outcome derivation.
- Add source-contract, certificate, and claim-reconciliation playbooks.
- Replay v1 false-closure incidents.

**Exit:** all known false closures remain unsolved/blocked; evidence classes and statuses remain orthogonal.

#### Phase 6 — Publication

- Implement plan digest, approval binding, destination locking, same-parent/same-filesystem staging, swap/backup/fsync, reduction, and idempotent recovery.

**Exit:** the full publication crash matrix passes; committed state never regresses.

#### Phase 7 — Routing calibration and cutover

- Run the model-allocation matrix and incident corpus.
- Select effective tier limits from observed verified outcomes, not catalogue names.
- Route native v2 inputs through `v2.facade`; permit v1 only for inspect/import/parity.

**Exit:** clean cutover gates pass on one frozen candidate and no production native module imports v1 outside `compat_v1`.

### 12.4 Cutover criteria

Cut over only when:

- the API/CLI/consumer inventory is complete or unresolved consumers are blocked;
- only `v2.compat_v1` imports v1 parsers;
- no native writer emits a v1 identity;
- every migration preserves source bytes and emits a classified report;
- the vertical slice passes schema, durability, execution, evidence, replay, sandbox, and crash gates;
- known v1 false-closure, stale-output, process, secret, replay, and publication incidents fail closed;
- implementation, full-gate, and assurance statuses all pass on one immutable candidate;
- v1 write-fence tests pass and production credentials cannot mutate retained v1 storage.

If a v2 release is withdrawn, stop new dispatch and append a withdrawal/recovery event to a new monotonic commit head. Never rewind authority and never resume v1 writing.

---

## 13. Prioritized mathematical use of v2

The infrastructure exists to support mathematics; it must not become another substitute for it. The CMV closure order remains:

1. freeze exact sources, toolchains, manifests, and retained evidence;
2. run the receipt-first Lean audit on the actual target declarations;
3. complete the source contract audit;
4. establish semantic equivalence of source, modeled carrier, and formal target;
5. close the exact scalar/formula layer and inverse-area map;
6. prove complete equal-area root/fold topology;
7. construct the genuine type-(iii) Lean carrier;
8. prove the full-domain Γ certificate with gap-free joins and endpoints;
9. prove frontier-to-reduced-boundary and source normalization/minimality transfer;
10. state the exact final theorem with dependency-ordered obligations;
11. run clean build, declaration check, axiom audit, source semantic review, and independent replay.

Sol should be used only where this chain contains a genuinely unresolved method gap after registered playbooks and Terra methods fail. It should not write the v2 controller or routine Lean scaffolding.

---

## 14. Risk register

| Risk | Why it matters | Control | Release evidence |
|---|---|---|---|
| Rebuilding v1 accidentally | Preserves coupling and ambiguous authority | hard module/import boundaries; one-way importer | import graph and writer-schema tests |
| Playbooks become renamed prompts | Recreates ad hoc execution | machine manifest, compiled DAG, validators, receipts, gates | compiler rejection fixtures |
| Cheap routing increases repair loops | Apparent savings can raise total cost | outcome-based calibration and actual usage receipts | routing matrix and closure/cost curves |
| Sol remains default planner/coder | Wastes scarce compute and hides known methods | eligibility receipts and default Sol budget zero | 100% Sol legality |
| Lean success is promoted to source truth | Formalization may be vacuous or mistranslated | separate formal and semantic gates | benchmark-defect and CMV semantic fixtures |
| Hashes are called signatures | Same writer can replace content and hashes | separate integrity/authenticity fields | trust-scope assertions and negative tests |
| Event projection regains authority | Reintroduces stale/forged status | validated commit head and replay | delete/forge/reorder tests |
| PIDs are reused or descendants survive | May kill unrelated work or leak compute | pidfd/process identity/resource reconciliation | process adversarial suite |
| Shared build roots race | Corrupts Lean evidence and recovery | attempt-scoped roots and atomic promotion | concurrent build isolation tests |
| Reviewer independence is asserted, not computed | Same lineage can rubber-stamp work | identity/context-lineage calculation | diversity attack corpus |
| Benchmarks reward defective statements | Inflates formal capability | corrected/audited benchmark slices and semantic gates | dataset issue report per case |
| Telemetry becomes authority | Development schemas or missing fields can distort status | internal receipt schema; OTel export only | round-trip and loss-report tests |
| Storage grows without bound | v1 already showed high retained-data cost | immutable shared cache, deduplication, retention classes | byte accounting and GC reachability proof |
| Parallelism precedes isolation | Recreates workspace and process races | serial scheduler first; parallelism deferred | isolation and scheduler acceptance |

---

## 15. Concrete recommendations

1. **Freeze v1 now.** No more native feature work in v1. Permit only critical containment fixes required to safely preserve or inspect it.
2. **Implement contracts before executors.** The playbook compiler, artifact envelope, event model, failure/status vocabulary, and schema registry are the foundation.
3. **Use a serial scheduler for the first release.** Parallelism is not required to prove the authority model and would multiply crash and workspace states.
4. **Start with three playbooks:** source contract audit, receipt-first formal audit, and proof-producing certificate generation. They address the main evidence gaps and repeated expensive work.
5. **Make Luna the default bounded executor and Terra the default engineering/reasoning tier.** Set Sol allowance to zero unless a controller-generated eligibility receipt exists.
6. **Adopt the 60/30/10 call cap during calibration.** Move toward 70/25/5 only after verified closure and repair-cost data support it.
7. **Store abstract tiers in playbooks, concrete model selectors in effective run policy.** Pin the exact resolved selector/checkpoint and catalogue digest in every invocation receipt.
8. **Do not treat four subscriptions as four independent reviewers.** Use clean-room contexts and distinct model families/providers where available; record degraded independence otherwise.
9. **Use external standards at export boundaries.** Workflow Run RO-Crate/PROV for research interoperability, in-toto/SLSA-style attestations for build/publication provenance, OpenTelemetry for observability. Keep the internal event/artifact model stricter.
10. **Gate theorem claims on both formal and semantic evidence.** Formal checks are machine authority; source equivalence remains separately reviewed.
11. **Measure useful work, not agent activity.** The primary productivity metric is verified obligation closure per total normalized compute, with false closure fixed at zero.
12. **Pilot v2 on one CMV obligation, not another full campaign.** The first proof of architecture is a fail-closed, replayable, crash-recoverable vertical slice with exact evidence.

---

## 16. Source index

### Agent orchestration and playbooks

- **[S1]** OpenAI Agents SDK, [Agent orchestration](https://openai.github.io/openai-agents-python/multi_agent/).
- **[S2]** Agent Skills, [Specification](https://agentskills.io/specification).
- **[S3]** OpenAI Skills, [Skill Creator guidance](https://github.com/openai/skills/blob/main/skills/.system/skill-creator/SKILL.md).
- **[S4]** Strands Agents, [Agent SOPs Specification](https://github.com/strands-agents/agent-sop/blob/main/spec/agent-sops-specification.md).
- **[S5]** Temporal, [Workflow overview and replay](https://docs.temporal.io/workflows).
- **[S6]** Temporal, [Workflow definitions, determinism, and versioning](https://docs.temporal.io/workflow-definition).

### Formal mathematics and scientific agents

- **[S7]** LeanProver/Pantograph, [Design rationale](https://github.com/leanprover/Pantograph/blob/dev/doc/rationale.md).
- **[S8]** LeanDojo, [LeanDojo-v2 repository](https://github.com/lean-dojo/LeanDojo-v2).
- **[S9]** Ospanov, Farnia, Yousefzadeh, [APOLLO: Automated LLM and Lean Collaboration for Advanced Formal Reasoning](https://arxiv.org/abs/2505.05758).
- **[S10]** Kung et al., [LEAP: Supercharging LLMs for Formal Mathematics with Agentic Frameworks](https://arxiv.org/abs/2606.03303).
- **[S11]** Achim et al., [Aristotle: IMO-level Automated Theorem Proving](https://arxiv.org/abs/2510.01346).
- **[S12]** Xin et al., [DeepSeek-Prover](https://arxiv.org/abs/2405.14333).
- **[S13]** Kumarappan et al., [LeanAgent: Lifelong Learning for Formal Theorem Proving](https://arxiv.org/abs/2410.06209).
- **[S14]** Novikov et al., [AlphaEvolve](https://arxiv.org/abs/2506.13131).
- **[S15]** Gottweis et al., [Accelerating scientific discovery with Co-Scientist](https://arxiv.org/abs/2502.18864).
- **[S16]** Ammanamanchi, Bhat, Biderman, [Faults in Our Formal Benchmarking](https://arxiv.org/abs/2606.29493).

### Routing, evaluation, and telemetry

- **[S17]** Ong et al., [RouteLLM: Learning to Route LLMs with Preference Data](https://arxiv.org/abs/2406.18665).
- **[S18]** OpenAI, [Evaluate agent workflows](https://developers.openai.com/api/docs/guides/agent-evals).
- **[S19]** OpenTelemetry, [Semantic conventions for GenAI agent and framework spans](https://github.com/open-telemetry/semantic-conventions-genai/blob/main/docs/gen-ai/gen-ai-agent-spans.md).

### Provenance, reproducibility, and process identity

- **[S20]** W3C, [PROV-O: The PROV Ontology](https://www.w3.org/TR/prov-o/).
- **[S21]** Research Object community, [RO-Crate Metadata Specification 1.1](https://www.researchobject.org/ro-crate/specification/1.1/index.html).
- **[S22]** Workflow Run RO-Crate, [profiles and implementations](https://www.researchobject.org/workflow-run-crate/).
- **[S23]** SLSA, [Provenance](https://slsa.dev/spec/v1.2/provenance).
- **[S24]** in-toto, [project overview](https://in-toto.io/about/).
- **[S25]** Reproducible Builds, [documentation index](https://reproducible-builds.org/docs/).
- **[S26]** Linux man-pages, [`pidfd_open(2)`](https://man7.org/linux/man-pages/man2/pidfd_open.2.html).

---

## 17. Final position

The project does not need another layer of prompts or another broad multi-agent campaign. It needs a small, typed, replayable execution kernel that converts accumulated mathematical procedures into versioned playbooks and makes evidence authority explicit.

V1's most valuable output is not its controller. It is the corpus of accepted behavior, failed runs, adversarial findings, mathematical partials, and exact evidence boundaries. Preserve that corpus unchanged. Build v2 beside it. Spend Luna on known execution, Terra on implementation and routine reasoning, and Sol only on admitted frontier work. Require formal/exact and semantic gates to agree before claiming theorem closure.
