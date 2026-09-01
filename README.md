# Agentic Lean Math Assistant

Agentic Lean Math Assistant is a research controller for mathematical work that may involve computation, source analysis, and Lean. It can coordinate several agents, but it does not treat agreement between agents or confident prose as proof.

A campaign is complete only when its configured checks pass. Depending on the project, those checks may include reproducible commands, exact certificates, independent claim review, semantic comparison, and named Lean declarations with an allowed axiom set.

## Research status

The first major case study was a Lean-checked reduction for the CMV strip-density problem. In the modeled setting, Lean proves that a type-(iv) candidate cannot minimize weighted perimeter when

\[
\lambda \ge 1.2581840884.
\]

Equivalently, any modeled type-(iv) minimizer must lie in

\[
1 < \lambda < 1.2581840884.
\]

That result can now be rebuilt and checked through the retained one-shot campaign workflow.

A later exact-rational certificate compares the folded type-(iv) branch with its selected equal-area type-(iii) competitor. It proves the scalar perimeter inequality on

\[
\frac{51}{50} \le \lambda \le \frac97,
\]

which includes the full interval from \(51/50\) through \(4/\pi\). This second result is independently replayable, but it is not yet a Lean theorem.

The current formalization target is to move that scalar certificate into Lean. The interval \(1<\lambda<51/50\), the source-to-model transfer, and the full CMV conjecture remain open.

## What makes it different

Most agent workflows mix three separate questions:

1. Did the process run?
2. Was useful evidence produced?
3. Is the mathematical claim actually established?

This controller records those questions separately.

- **Execution state** records attempts, failures, retries, checkpoints, and invalidations.
- **Evidence state** records immutable inputs, commands, outputs, receipts, hashes, and limitations.
- **Mathematical state** records claims, dependencies, independent verdicts, required targets, and unresolved obligations.

An agent cannot approve its own claim. A successful campaign must satisfy the contracts declared before execution.

## Main safeguards

### Frozen inputs and retained evidence

Each run starts from an immutable input snapshot. Commands, prompts, outputs, handoffs, receipts, state transitions, and failures are retained with SHA-256 identities. Replay rejects changed inputs, executables, dependency manifests, environments, or sandbox policies.

### Verifier-gated claims

Claims have exact statements, scopes, dependencies, proof descriptions, and limitations. Independent verifier stages must decide every configured claim. The controller rejects malformed graphs, missing verdicts, stale evidence, unresolved critical errors, and claims that depend on rejected premises.

### Lean boundary

For a configured Lean target, the controller builds the retained source, loads the compiled declaration, checks its exact type, and asks Lean for its axioms. This avoids relying on a copied theorem statement or regex-parsed terminal output.

A separate semantic review compares the Lean declaration with the intended informal theorem, including hypotheses, quantifiers, domains, branches, and boundary cases. Compilation alone does not establish that the right theorem was formalized.

### Linux sandbox

Agent, command, replay, and Lean stages run in Bubblewrap namespaces and transient user-systemd cgroups by default. The retained workspace is the only writable host path, networking is disabled unless explicitly enabled, and resource limits are recorded in the receipt.

Sandbox creation fails closed. Running without the sandbox requires an explicit manifest setting.

## Requirements

- Linux
- Python 3.12, 3.13, or 3.14
- [uv](https://docs.astral.sh/uv/)
- Bubblewrap and user-systemd for sandboxed execution
- OMP and Herdr for live multi-agent campaigns
- Lean and Lake for projects with formal targets

## Install

```bash
uv sync --locked
```

Optional research dependencies:

```bash
uv sync --locked --extra research
```

Optional regression backends:

```bash
uv sync --locked --extra ml
```

## Try the included claim-ledger example

Validation checks the manifest and feature contracts without launching agents:

```bash
uv run agentic-lean-math-assistant validate \
  --campaign examples/claim-ledger/campaign.toml
```

To run the campaign with OMP and Herdr available:

```bash
uv run agentic-lean-math-assistant run \
  --campaign examples/claim-ledger/campaign.toml
```

After the run, inspect its state, claims, and trust boundaries:

```bash
uv run agentic-lean-math-assistant status --run examples/claim-ledger/runs/<run-id>
uv run agentic-lean-math-assistant claims --run examples/claim-ledger/runs/<run-id>
uv run agentic-lean-math-assistant audit --run examples/claim-ledger/runs/<run-id>
uv run agentic-lean-math-assistant verify --run examples/claim-ledger/runs/<run-id>
```

The example contains a proposer, an independent verifier, a deterministic command gate, and a final claim gate. It is intentionally small enough to inspect by hand.

## Fixed research regime

`regime-run` provides a standard research loop:

1. inspect the problem, references, and retained knowledge;
2. decide whether new source research is needed;
3. create a bounded plan with explicit obligations and falsification checks;
4. run the permitted tasks;
5. assess every obligation and produce a solved, unsolved, or blocked result;
6. retain the evidence and wait for an explicit next-strategy decision when work remains.

Start with the included minimal project:

```bash
uv run agentic-lean-math-assistant regime-run \
  --project examples/minimal-project/project.toml
```

An unresolved run does not silently continue forever. The controller records the available strategies and waits for a user decision:

```bash
uv run agentic-lean-math-assistant choose-strategy \
  --run <run-directory> \
  --strategy <strategy-id-or-stop>
```

## Bounded autonomy

Projects may define an exact success contract: required files, Lean declarations and types, allowed axioms, and independent verification commands. `autonomy-run` can then execute successive bounded campaigns until that contract passes or a campaign, time, or failure limit is reached.

```bash
uv run agentic-lean-math-assistant autonomy-run \
  --project path/to/project.toml
```

A campaign reporting “solved” is not enough. The controller independently rechecks the retained evidence and formal targets before accepting the session.

## Useful commands

```text
validate          validate a campaign without running it
run               start a campaign DAG
resume            resume a retained campaign
regime-run        run the fixed research regime
regime-resume     resume a fixed-regime checkpoint
autonomy-run      run bounded successive campaigns
status            show authoritative run state
dashboard         watch stages, targets, and limitations
claims            inspect claim dependencies and verdicts
audit             report passed and missing trust boundaries
verify            verify the retained evidence bundle
replay            rerun an allowlisted frozen command
publish-plan      show an immutable publication plan
publish           apply an explicitly approved publication plan
stop-all          terminate registered campaign processes
```

Run the CLI with `--help` or append `--help` to any command for its full arguments.

## Repository layout

```text
src/agentic_lean_math_assistant/   controller and reusable library
examples/                          minimal runnable examples
tests/                             unit, failure-path, and integration tests
.github/workflows/ci.yml           Python 3.12–3.14 CI
pyproject.toml                     package and tool configuration
uv.lock                            locked dependency graph
```

The new repository intentionally excludes historical campaign workspaces, superseded design documents, benchmark output, release bundles, and earlier version reports.

## Development

```bash
uv lock --check
uv run ruff format --check src tests
uv run ruff check src tests
uv run mypy src
uv run pytest
uv build
```

The clean core suite currently contains 304 passing tests and one optional-backend skip. CI repeats formatting, linting, type checking, tests, package builds, and installed-wheel smoke tests on Python 3.12, 3.13, and 3.14.

## Limits of the system

This software can make research more inspectable. It cannot turn an unproved claim into a theorem.

- Agent agreement is not evidence.
- Floating-point output is not automatically a proof.
- A passing Lean build does not guarantee that the formal statement matches the intended theorem.
- Mutation tests show that selected failures are detected; they do not prove that a checker has no bugs.
- A scalar model does not settle the original geometric problem until the source-to-model bridge is proved.

The retained result should always be read together with its assumptions, evidence, and unresolved obligations.

## License

This repository is currently distributed under the terms in [`LICENSE`](LICENSE).
