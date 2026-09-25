# Agentic Lean Math Assistant

Agentic Lean Math Assistant is a Python 3.12–3.14 controller for evidence-retaining mathematical research, Lean 4 formalization, semantic review, and reproducible proof publication. It treats successful execution, mathematical evidence, and accepted truth as separate states. Agentic processes produce evidence; a claim is accepted only after the configured Lean, semantic, and publication gates pass.

<p align="center">
  <img src="docs/program-map.svg" width="100%" alt="Agentic Lean Math Assistant program map showing governed research, Lean verification, independent semantic review, and publication workflows.">
</p>

<p align="center"><a href="docs/program-map.html"><strong>Open the standalone HTML Program Map</strong></a></p>

## Solve

`solve` is the one-command path from informal materials to a Lean-verified,
researcher-facing proof package. Put the main question in `problem.md`; place
notes, papers, datasets, and an optional existing Lean/Lake project beside it.
The controller freezes those inputs, has independent agents agree on semantic
and formal contracts, generates an internal autonomous project, and works in
verifier-gated steps. Proof Builder runs only after solving stops.

```bash
uv run agentic-lean-math-assistant solve ./my-problem \
  --runtime-limit 24h \
  --predicted-runtime-limit 12h \
  --headless
```

At least one runtime limit is required. The hard limit covers contract
extraction, research, formalization, verification, forecasting, and every
nested OMP invocation; final publication time is excluded. `max_model_calls`
likewise counts every nested invocation and blank-output retry before it starts.
The predicted limit compares projected total runtime from the original start.
Work continues when either a complete solution or the next publication-worthy
verified improvement fits that limit.

Optional `solve.toml` settings make repeated or unattended runs reproducible:

```toml
schema_version = 1

[solve]
problem = "problem.md"
profile = "balanced"
allow_web = false

[resources]
runtime_limit = "24h"
max_model_calls = 64
approval_timeout = "15m"

[forecast]
predicted_runtime_limit = "12h"
initial_after = "1h"
interval = "2h"
minimum_interval = "30m"
percentile = 80
breach_confirmations = 2
minimum_confidence = "medium"

[models]
proof_author = "provider/author-model"
proof_reviewer = "provider/reviewer-model"

[execution]
sandbox = true
memory_max_mb = 8192
```

The independent evaluator runs after one active hour, at safe milestone or
termination boundaries, and at an adaptive interval no longer than two hours.
Its forecast covers both the next publication-worthy result and full completion.
Each accepted partial result becomes a content-addressed checkpoint while the
solver continues. If no result was judged publication-worthy but a weaker
Lean-verified result exists at termination, interactive runs ask before
packaging it; headless runs skip it after the approval timeout unless
`--publish-inconclusive` was supplied.

State is retained under `<folder>/.alma/`; the final package is written under
`<folder>/result/`.
Publication requires explicit author and semantic-review routes. Configure them
under `[models]`, or supply `--proof-author-model` and
`--proof-reviewer-model`; those overrides can also recover a retained
`publication_failed` solve without restarting its verified mathematics.


```bash
agentic-lean-math-assistant solve-status ./my-problem
agentic-lean-math-assistant solve-stop ./my-problem
agentic-lean-math-assistant solve-resume ./my-problem \
  --feedback "Interpret the endpoint as inclusive."
```

Five failed author/reviewer attempts to establish either contract pause in
`needs_input`. Resume with explicit `--feedback`; use `solve --restart` to
archive the prior lineage and freeze changed source materials.

## Proof Builder

`proof-builder` turns a completed Lean/Lake development into a researcher-facing publication package. Theorem names, source paths, informal claims, generated certificate families, references, model routes, and output versions come from a version-controlled `proof-package.toml` manifest.

An accepted package contains four researcher-facing files:

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

### A complete example: the elementary CMV strip-density comparison

The repository’s primary end-to-end Proof Builder example is
*An Elementary Comparison for Four-Arc Regions in a Planar Strip Density*.
It addresses Question 1 from Cañete, Miranda Jr., and Vittone’s 2010 paper
*Some Isoperimetric Problems in Planes with Density*, using the elementary
comparison in the note by Skilyn Leon, Rosa Pavlak, Evelyn Pulla, and Xi Sisi Shen.
The package is Lean-verified and semantically accepted.

| Output | Purpose |
|---|---|
| [Package README](projects/cmv-strip-density/reports/lean-verified-cmv-elementary-v1/README.md) | Verified status and standalone reproduction instructions |
| [MainProof.pdf](projects/cmv-strip-density/reports/lean-verified-cmv-elementary-v1/MainProof.pdf) | Researcher-facing proof in the original note’s mathematical-paper style |
| [LemmaSupplement.pdf](projects/cmv-strip-density/reports/lean-verified-cmv-elementary-v1/LemmaSupplement.pdf) | Mathematical explanations and frozen Lean source for all 506 retained declarations |
| [SemanticAudit.pdf](projects/cmv-strip-density/reports/lean-verified-cmv-elementary-v1/SemanticAudit.pdf) | Strict independent review with 506 equivalent declaration judgments and no remaining critical errors or citation issues |
| [Frozen publication manifest](projects/cmv-strip-density/reports/lean-verified-cmv-elementary-v1/supporting-materials/proof-package.toml) | Exact publication contract, model routes, and original build paths |
| [Canonical PDF](projects/cmv-strip-density/reports/lean-verified-cmv-elementary.pdf) | Stable copy of the accepted main proof |

The primary published root is:

```lean
CMVElementary.geometric_comparison
```

For every real density $\lambda>1$ and every $0<h\le1$, it supplies a
three-arc region $E_r$, with $0<r<h$, satisfying

$$
A_\lambda(E_r)=A_\lambda(C_h),\qquad
P_\lambda(C_h)-P_\lambda(E_r)>\frac{\gamma_\lambda}{h}>0,
$$

where

$$
\gamma_\lambda=\lambda\arccos(1/\lambda)-\sqrt{1-\lambda^{-2}}.
$$

Thus every explicitly defined symmetric four-arc region $C_h$ is excluded
as a weighted-perimeter minimizer, for every $\lambda>1$. The proof uses
the $J/H$ inequalities, the greatest equal-area root, and a strict $Q$
comparison—not the earlier stationary-envelope exclusion. The package also
verifies `CMVElementary.scalar_comparison`, `CMVElementary.elementary_route`,
and `CMVElementary.geometric_realization`. Its coordinate, integral, and
complete-frontier identities include $h=1$, major caps, and the
$r=1/2$ disk.

The mathematical corollary combines this comparison with CMV’s existing
classification to obtain the ball, stadium, and three-arc regimes of
Conjecture 3.12 for every $\lambda>1$. The external classification and the
reduced-boundary transfer are cited mathematics, not Lean-formalized results
or additional axioms. The package distinguishes this corollary from its
kernel-verified explicit-family theorem.

The [earlier all-density modeled package](projects/cmv-strip-density/reports/lean-verified-cmv-all-density-v1/README.md)
remains available as a historical development. The companion
[CMV ball-density package](projects/cmv-ball-density/reports/lean-verified-cmv-ball-single-transition-v1/README.md)
addresses Question 2 through the single-transition theorem for the faithful
type-(B)/(C) profiles.

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
- `pdf-render`: rebuild researcher-facing PDFs from retained validated handoffs without model calls;
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

## CMV case studies: two problems from one paper

This repository studies two problems posed by Cañete, Miranda Jr., and
Vittone in their 2010 paper *Some Isoperimetric Problems in Planes with
Density*. The strip- and ball-density projects have separate Lean
developments and independently reviewed proof packages, with the
formalized statements and external mathematical dependencies distinguished.

### CMV Question 1: strip density

The density is 1 on $|y|\le1$ and $\lambda>1$ outside. The current
researcher-facing example is the
[elementary comparison package](projects/cmv-strip-density/reports/lean-verified-cmv-elementary-v1/README.md),
whose primary root is `CMVElementary.geometric_comparison`.

| Scope | Result |
|---|---|
| Explicit geometric comparison | For every $\lambda>1$ and $0<h\le1$, the specified four-arc region has an equal-area three-arc competitor with perimeter improvement strictly greater than $\gamma_\lambda/h>0$. Lean-verified. |
| Proof route and realization | The scalar comparison, $J/H$ and greatest-root/$Q$ argument, and actual coordinate-carrier area/perimeter identities are proved. No global three-arc area monotonicity or root uniqueness is assumed. |
| Full-conjecture corollary | Combining the comparison with CMV’s classification gives the disk, stadium, and three-arc regimes. External classification and reduced-boundary transfer remain outside the Lean formalization. |

The package’s principal modules are:

- [`CMVElementary.lean`](projects/cmv-strip-density/reports/lean-verified-cmv-elementary-v1/supporting-materials/lean/CMVElementary.lean): auxiliary inequalities, calculus, and quantitative scalar comparison.
- [`GreatestLevelRoot.lean`](projects/cmv-strip-density/reports/lean-verified-cmv-elementary-v1/supporting-materials/lean/GreatestLevelRoot.lean): greatest-root existence and strict support comparison.
- [`CMVElementaryGeometry.lean`](projects/cmv-strip-density/reports/lean-verified-cmv-elementary-v1/supporting-materials/lean/CMVElementaryGeometry.lean): literal regions, area/frontier bridges, and the primary geometric theorem.

Recheck the accepted package’s checksums and pinned Lean sources:

```bash
cd projects/cmv-strip-density/reports/lean-verified-cmv-elementary-v1
python supporting-materials/verify.py
```

For each $\lambda>1$, three-arc minimizers occur in the large-area regime;
the result does not replace small-area disks or intermediate-area stadiums.
At the transition, stadium and three-arc minimizers coexist.

The [earlier modeled package](projects/cmv-strip-density/reports/lean-verified-cmv-all-density-v1/README.md)
and the broader frontier paper ([PDF](projects/cmv-strip-density/reports/lean-verified-cmv-frontier.pdf),
[Markdown](projects/cmv-strip-density/reports/lean-verified-cmv-frontier.md),
[HTML](projects/cmv-strip-density/reports/lean-verified-cmv-frontier.html))
remain available as historical research artifacts. The living development in
[`projects/cmv-strip-density/proof/`](projects/cmv-strip-density/proof/)
is separate from the immutable elementary publication.

### CMV Question 2

[`projects/cmv-ball-density/`](projects/cmv-ball-density/) addresses the same
paper’s separate ball-density question for $0<\lambda<1$. Its verified formal
contract proves the single-transition theorem left open after Theorem 3.23:
once the equal-area type-(C) orthogonal-ball profile is no worse than the
type-(B) two-arc profile, type (B) cannot become optimal again at a larger
weighted area.

Read the [ball-density package](projects/cmv-ball-density/reports/lean-verified-cmv-ball-single-transition-v1/README.md),
the researcher-facing [MainProof.pdf](projects/cmv-ball-density/reports/lean-verified-cmv-ball-single-transition-v1/MainProof.pdf),
or the stable [canonical PDF](projects/cmv-ball-density/reports/lean-verified-cmv-ball-single-transition.pdf).
The package starts from source-faithful definitions of both candidate profiles
and does not reuse the strip-density result. Its explicit trust boundary leaves
the paper’s finite-perimeter existence, regularity, connectedness, and
exhaustive candidate-classification premises outside the formalized analytic
theorem.


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

The package version is `1.4.3`. Release changes are recorded in [`CHANGELOG.md`](CHANGELOG.md).

## Execution containment

Generic campaigns default to a fail-closed Linux sandbox. Bubblewrap supplies private mount, PID, and network namespaces. A transient user-systemd cgroup enforces elapsed time, memory, swap, CPU, task-count, and file-size limits. Sandbox creation has no automatic unsandboxed fallback.

`autorun-report` validates its frozen invocation against the active session,
matching held controller lock, and fresh heartbeat. It does not probe the host
controller's PID from inside the reporter's private PID namespace. Stale,
foreign, modified, or unlocked invocations remain rejected.

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
