# Agentic Lean Math Assistant

Agentic Lean Math Assistant is a Python 3.12–3.14 controller for evidence-retaining mathematical research, Lean 4 formalization, semantic review, and reproducible proof publication. It treats successful execution, mathematical evidence, and accepted truth as separate states. A process can produce evidence; only configured Lean, semantic, and publication gates can accept a claim.

<p align="center">
  <img src="docs/program-map.svg" width="100%" alt="Agentic Lean Math Assistant program map showing governed research, Lean verification, independent semantic review, and publication workflows.">
</p>

<p align="center"><a href="docs/program-map.html"><strong>Open the standalone HTML Program Map</strong></a></p>

## Proof Builder

`proof-builder` turns a completed Lean/Lake development into an immutable, professor-facing publication package. It is problem-agnostic: theorem names, source paths, informal claims, generated certificate families, references, model routes, and output versions come from a version-controlled `proof-package.toml` manifest.

An accepted package contains four reader-facing files:

```text
proof-package/
├── README.md
├── MainProof.pdf
├── LemmaSupplement.pdf
├── SemanticAudit.pdf
└── supporting-materials/
```

- **MainProof.pdf** explains the theorem, proof architecture, scope, and limitations for a mathematically expert reader who may not know Lean.
- **LemmaSupplement.pdf** maps the exposition to exact Lean declarations, reproduces conceptual declarations, and indexes repetitive generated families without dropping their executable source.
- **SemanticAudit.pdf** records an isolated adversarial review of hypotheses, quantifiers, domains, inequalities, boundary cases, symbols, generated families, and citations.
- **supporting-materials/** retains the executable Lean closure, pinned toolchain and dependencies, manifest, prompts, model requests, model handoffs, review records, command receipts, source provenance, references, and SHA-256 ledger.

### A complete example: the Lean-verified 51/50 proof

Version 2 of the CMV 51/50 publication is the repository’s end-to-end Proof Builder example:

| Output | Purpose |
|---|---|
| [Package README](projects/cmv-strip-density/reports/lean-verified-cmv-cutoff-51-50-v2/README.md) | Status, exact claim, trust boundary, and cross-platform reproduction instructions |
| [MainProof.pdf](projects/cmv-strip-density/reports/lean-verified-cmv-cutoff-51-50-v2/MainProof.pdf) | Professor-facing proof of the published 51/50 cutoff |
| [LemmaSupplement.pdf](projects/cmv-strip-density/reports/lean-verified-cmv-cutoff-51-50-v2/LemmaSupplement.pdf) | Declaration-level explanations and complete generated-family ledger |
| [SemanticAudit.pdf](projects/cmv-strip-density/reports/lean-verified-cmv-cutoff-51-50-v2/SemanticAudit.pdf) | Independent semantic-equivalence review and declaration-by-declaration findings |
| [proof-package.toml](projects/cmv-strip-density/reports/lean-verified-cmv-cutoff-proof-package.toml) | Reusable publication contract that produced the package |

The published root is:

```lean
CMVPublishedCutoff51_50.candidate_not_isWeightedPerimeterMinimizer_from_51_50
```

It states that for every real density $\lambda\ge 51/50$, every modeled regular type-(iv) four-arc candidate satisfying the formal CMV type-(iv) hypotheses is not a weighted-perimeter minimizer. The package retains the exact-rational 1,139-cell certificate across $[51/50,9/7]$, the formal cap replacement above $9/7$, the complete dependency-closed Lean source, and the allowed-axiom audit.

This is an independently useful certificate path. The living CMV proof tree now proves a stronger modeled result for every $\lambda>1$; the v2 package intentionally publishes the narrower frozen 51/50 claim and does not imply an unconditional proof of the full CMV conjecture.

## How Proof Builder works

A new build executes the following fail-closed pipeline:

1. **Manifest validation.** Parse a strict schema and resolve every project, Lean, reference, rendering, model, and output path.
2. **Preflight.** Check output collisions, executables, model routes, root discovery, import closure, and model-call budgets. By default, a temporary publication project also compiles the exact root contract before any model call.
3. **Source export.** Discover the project-local import closure and copy it into a minimal publication-scoped Lake project.
4. **Kernel and axiom gate.** Compile every configured root at its exact expected type, call `Lean.collectAxioms`, and reject unexpected axioms or forbidden declarations.
5. **Dependency closure.** Derive used declarations from elaborated Lean expressions. Generated families are retained behind explicit dependency boundaries rather than inferred from prose.
6. **Author pass.** A fresh model invocation classifies the mathematics and writes structured main-proof and lemma explanations against the frozen inventory.
7. **Semantic-review pass.** A separate fresh invocation adversarially compares the prose with every retained conceptual declaration and every configured generated family.
8. **Repair loop.** Supported findings return to the author within the selected profile and hard call budget. Unresolved findings produce a conditional or failed package, never an accepted proof claim.
9. **Rendering.** Render the main proof, lemma supplement, and semantic audit with separate publication styles. Rendering intermediates are discarded.
10. **Finalization.** Write immutable status, provenance, model settings, receipts, and a complete SHA-256 ledger. A configured canonical PDF is refreshed only from an accepted `MainProof.pdf`.

Lean compilation and semantic review answer different questions:

- **Kernel gate:** did Lean accept the exact declaration under the allowed axioms?
- **Semantic gate:** does the publication say exactly what that declaration establishes?

A model cannot substitute for the Lean gate. Lean compilation cannot establish that an informal explanation preserved hypotheses, domains, or quantifiers. An accepted package requires both.

## Proof Builder workflow

### Initialize a manifest

```bash
uv run agentic-lean-math-assistant proof-builder init \
  --manifest reports/proof-package.toml
```

The generated template documents roots, publication boundaries, model settings, rendering tools, and verification commands.

### Inspect the plan without doing work

```bash
uv run agentic-lean-math-assistant proof-builder build \
  --manifest reports/proof-package.toml \
  --dry-run
```

Use `--format json` for automation. The plan reports the output path, root contracts, import closure, source and declaration counts, generated-family count, effective models, review profile, maximum model calls, and stage order.

### Run preflight

```bash
uv run agentic-lean-math-assistant proof-builder preflight \
  --manifest reports/proof-package.toml
```

Preflight runs the temporary Lean contract and dependency-closure gate but makes no model calls and creates no package. Use `--no-lean` for a fast static tool, path, model, and closure check.

### Select author and semantic-review models

Models can be set independently in the manifest:

```toml
[models]
author = "openai-codex/gpt-6-astra"
reviewer = "openai-codex/gpt-6-astra"
profile = "strict"
thinking = "xhigh"
timeout_seconds = 21600
max_revisions = 3
max_model_calls = 8
```

Or overridden for one build:

```bash
uv run agentic-lean-math-assistant proof-builder build \
  --manifest reports/proof-package.toml \
  --author-model provider/author-model \
  --semantic-review-model provider/reviewer-model \
  --review-profile standard \
  --max-model-calls 6
```

Any OMP model route is allowed. Astra remains the recommended semantic reviewer for the strict profile, but economical routes are valid when the operator accepts the tradeoff. The effective route, provider, model revision string, thinking level, profile, revision ceiling, call ceiling, and disabled fallback policy are retained in `MANIFEST.lock.json` and per-call requests. Proof Builder never silently substitutes another model.

Author and reviewer passes always use fresh, isolated invocations, even when configured with the same route.

### Review profiles and budgets

| Profile | Thinking | Repair revisions | Default maximum calls | Intended use |
|---|---:|---:|---:|---|
| `strict` | `xhigh` | 3 | 8 | Final publication and highest-assurance review |
| `standard` | `high` | 2 | 6 | Routine reviewed packages |
| `economical` | `medium` | 1 | 4 | Lower-cost iteration and smaller proofs |

`--max-model-calls` is a hard lifecycle ceiling, including calls retained before resume. A build stops before starting an unbudgeted invocation.

### Build an immutable package

```bash
uv run agentic-lean-math-assistant proof-builder build \
  --manifest reports/proof-package.toml
```

The command exits successfully only for a semantically accepted package. Conditional and failed packages remain inspectable and resumable, with actionable findings printed at the end.

### Inspect and disposition semantic findings

Interactive review:

```bash
uv run agentic-lean-math-assistant proof-builder review \
  --package reports/example-proof-v1
```

Non-interactive review:

```bash
uv run agentic-lean-math-assistant proof-builder review \
  --package reports/example-proof-v1 \
  --decision 'F001=repair:Restore the omitted endpoint hypothesis.' \
  --decision 'F002=false-positive:The cited declaration already fixes this domain.'
```

Available dispositions are `repair`, `known-limitation`, `false-positive`, and `stop`. Decisions are written to a sidecar so they do not invalidate the failed package’s existing checksum ledger. Resume incorporates them into the repair prompt and then retains them inside the next finalized package.

### Resume from a selected stage

```bash
uv run agentic-lean-math-assistant proof-builder resume \
  --package reports/example-proof-v1 \
  --from semantic-review
```

Supported restart points:

- `lean-export`: discard a checksum-verified failed build and reconstruct it from the source manifest;
- `explanation`: rerun the author explanation and downstream review;
- `semantic-review`: reuse the latest valid author handoff for the first new reviewer pass;
- `pdf-render`: rebuild reader-facing PDFs from retained validated handoffs without model calls;
- `checksum-ledger`: finish a package interrupted after status and rendering.

Accepted packages are immutable and cannot be resumed. A revised accepted publication must use a new manifest version and output directory.

### Preview layout without model calls

```bash
uv run agentic-lean-math-assistant proof-builder preview \
  --manifest reports/proof-package.toml
```

Preview renders the three PDF positions from mechanically generated content. Every document is marked **UNVERIFIED PREVIEW**. Preview performs no kernel gate, authorship pass, semantic review, acceptance decision, canonical-PDF update, or checksum finalization.

### Discover Lean declarations

```bash
uv run agentic-lean-math-assistant proof-builder declarations \
  --manifest reports/proof-package.toml \
  --contains Cutoff
```

The command imports the configured roots through Lake and reports each matching declaration’s exact pretty-printed Lean type, source module and line, generated-family membership, and axioms collected by Lean. Use `--format json` for editor tooling.

### Inspect package health

```bash
uv run agentic-lean-math-assistant proof-builder status \
  --package reports/example-proof-v1
```

Status reports acceptance state, checksum health, retained-file count, revision attempts, model provenance, and toolchain identity. Building packages report a pending ledger rather than pretending to be finalized.

### Compare publication versions

```bash
uv run agentic-lean-math-assistant proof-builder diff \
  reports/example-proof-v1 \
  reports/example-proof-v2
```

The comparison distinguishes root-contract, allowed-axiom, model, declaration, semantic-status, and rendered-artifact changes. JSON output is available with `--format json`. Exit status is nonzero when packages differ, which makes the command useful as a release gate.

### Verify in CI or independently

Full ledger and pinned Lean rebuild:

```bash
uv run agentic-lean-math-assistant proof-builder verify \
  --package reports/example-proof-v2
```

Available verification modes:

```bash
# Complete byte ledger only
proof-builder verify --package reports/example-proof-v2 --checksums-only

# Independent Lean rebuild only
proof-builder verify --package reports/example-proof-v2 --lean-only

# Full verification in a network-isolated sandbox
proof-builder verify --package reports/example-proof-v2 --no-network

# Stable machine-readable CI result
proof-builder verify --package reports/example-proof-v2 --format json

# Exit status only
proof-builder verify --package reports/example-proof-v2 --quiet
```

`--no-network` requires the normal Linux containment dependencies and a locally available pinned Lake dependency closure.

## CMV case study

The canonical project studies the Cañete–Miranda–Vittone strip-density isoperimetry problem. The density is 1 on $|y|\le1$ and $\lambda>1$ outside.

The current proof has three scope levels:

| Level | Current result |
|---|---|
| Modeled candidate | Every `FourArcCandidate` satisfying the formal CMV type-(iv) hypotheses is excluded for every $\lambda>1$. |
| Literal source carrier | Every checked four-arc carrier is excluded for every $\lambda>1$, including the $h=1$ endpoint, horizontal translates, almost-everywhere representatives, and raw closed geometry with source radius $R\ge1$. |
| Arbitrary source minimizer | Open. The development does not derive the required carrier classification from every source-admissible minimizer. |

Principal modules:

- [`CMVModeledCutoff.lean`](projects/cmv-strip-density/proof/CMVModeledCutoff.lean) contains the modeled all-$\lambda>1$ exclusion.
- [`CMVTypeThreeSourceExclusion.lean`](projects/cmv-strip-density/proof/CMVTypeThreeSourceExclusion.lean) contains checked source-carrier exclusions.
- [`CMVSourceClassification.lean`](projects/cmv-strip-density/proof/CMVSourceClassification.lean) separates closed geometry from density and Snell-law data.
- [`CMVPublishedCutoff51_50.lean`](projects/cmv-strip-density/proof/CMVPublishedCutoff51_50.lean) is the frozen root for the independent v2 Proof Builder example.

The project does not claim an unconditional proof of CMV Conjecture 3.12. The remaining obligation is geometric and measure-theoretic classification: bilateral symmetry, common-circle geometry, configuration enumeration, and exact or almost-everywhere carrier identification must still be derived for arbitrary relevant source minimizers.

Run the full living Lean project and axiom ledger:

```bash
cd projects/cmv-strip-density/proof
lake build
lake env lean _Assumptions.lean
```

The broader frontier paper is available as [PDF](projects/cmv-strip-density/reports/lean-verified-cmv-frontier.pdf), [Markdown](projects/cmv-strip-density/reports/lean-verified-cmv-frontier.md), and [HTML](projects/cmv-strip-density/reports/lean-verified-cmv-frontier.html). Those explanatory formats are not themselves part of the mathematical trust boundary.

## Research controller

Proof Builder is one publication surface of a larger problem-agnostic controller. A project manifest supplies frozen inputs, model routes, budgets, source policy, containment policy, exact targets, and success contracts.

The controller maintains three distinct records:

1. **Execution state:** stages that ran, failed, retried, resumed, or were invalidated.
2. **Evidence state:** inputs, prompts, commands, outputs, receipts, digests, reports, and limitations.
3. **Truth state:** claims, dependencies, verifier decisions, Lean declarations, semantic findings, and target closure.

A successful process can add evidence. It cannot change truth state by itself.

### Fixed research regime

`regime-run` performs bounded research, planning, execution, and assessment. It validates a strategy DAG before execution, records inaccessible-source decisions, runs capped pilots before expensive descendants, requires complete obligation disposition, and retains compute use and successor choices.

```bash
uv run agentic-lean-math-assistant regime-run \
  --project projects/cmv-strip-density/project.toml
```

Headless operation must state its missing-source policy:

```bash
uv run agentic-lean-math-assistant regime-run \
  --project projects/cmv-strip-density/project.toml \
  --missing-source-policy checkpoint \
  --headless
```

### Persistent autorun

`autorun` is an unattended project conductor. It reloads `MASTER_PROMPT.md` every round and retains prompts, outputs, receipts, trusted metrics, strategy contracts, independent progress adjudication, and controller events. The controller—not a model—is the only component that changes strategy and progress state.

```bash
uv run agentic-lean-math-assistant autorun \
  --project projects/cmv-strip-density/project.toml
```

### Bounded campaign autonomy

`autonomy-run` executes successive fixed-regime campaigns under a project-specific success contract. Campaign count, elapsed time, failures, and analysis time are capped. A model’s `solved` report remains a claim until the controller rechecks required artifacts, exact theorem types, allowed axioms, evidence indexes, and verification commands.

```bash
uv run agentic-lean-math-assistant autonomy-run \
  --project projects/cmv-strip-density/project.toml \
  --headless
```

## Installation

Requirements:

- Linux with `os.pidfd_open`, a working `systemd --user` manager, and Bubblewrap for contained execution;
- Python 3.12, 3.13, or 3.14;
- [`uv`](https://docs.astral.sh/uv/);
- OMP on `PATH`, or an explicit `--omp` path;
- Lean and Lake for formal-proof stages;
- Pandoc and Chromium for Proof Builder PDF rendering;
- Herdr only for the optional live workspace surface.

Install the locked base environment:

```bash
uv sync --locked
uv run agentic-lean-math-assistant --version
```

Optional scientific and notebook dependencies:

```bash
uv sync --locked --extra research
```

Optional regression backend:

```bash
uv sync --locked --extra ml
```

The package version is `1.3.0`. Release changes are recorded in [`CHANGELOG.md`](CHANGELOG.md).

## Execution containment

Generic campaigns default to a fail-closed Linux sandbox. Bubblewrap supplies private mount, PID, and network namespaces. A transient user-systemd cgroup enforces elapsed time, memory, swap, CPU, task-count, and file-size limits. Sandbox creation has no automatic unsandboxed fallback.

Agent invocations are admitted through a crash-released host resource lease. Cgroup OOM, exit 137, abort, Bun panic, and segmentation-fault outcomes are terminal and bypass blank-output retries. Receipts retain the effective containment policy and admission wait.

A manifest can set `sandbox = false` only as an explicit trust decision. Namespace isolation then disappears, while configured cgroup limits and receipts remain. Never use a trusted unsandboxed project configuration for untrusted prompts or inputs.

## Development and release checks

Run the Python suite:

```bash
uv run pytest -q --ignore=tests/test_benchmark_calibration.py
```

Run formatting, lint, and static types:

```bash
uv run ruff format --check src tests scripts benchmarks/cmv-range-reduction/validation
uv run ruff check src tests scripts benchmarks/cmv-range-reduction/validation
uv run mypy src scripts benchmarks/cmv-range-reduction/validation/validate_result.py
```

Build distributions:

```bash
uv lock --check
uv build
```

## License

This repository is a proprietary portfolio release. Copyright © 2026 Rosa Pavlak. Viewing the repository and running the documented verification commands for personal evaluation, educational review, or employment assessment is permitted. No license is granted to use, copy, modify, distribute, sublicense, or sell the software, proofs, reports, or other materials. See [`LICENSE`](LICENSE) for the exact terms.
