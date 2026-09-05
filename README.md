# Agentic Lean Math Assistant

Agentic Lean Math Assistant is a research controller for mathematical work that may involve computation, source analysis, and Lean. It can coordinate several agents, but it does not treat agreement between agents or confident prose as proof.

A campaign is complete only when its configured checks pass. Depending on the project, those checks may include reproducible commands, exact certificates, independent claim review, semantic comparison, and named Lean declarations with an allowed axiom set.

The system was designed to run through OMP (oh-my=pie) and Herdr. OMP runs the model agents and exposes their allowed tools. Herdr provides the managed terminal workspace in which campaign activity can be inspected. The controller remains responsible for scheduling, retained state, deterministic commands, Lean checks, and acceptance decisions.

## Research status

The principal case study starts from Antonio Cañete, Michele Miranda Jr., and Davide Vittone's paper *Some Isoperimetric Problems in Planes with Density* [1]. In the strip-density setting relevant here, the paper classifies symmetric circular-arc candidates for an isoperimetric problem. This README abbreviates Cañete, Miranda Jr., and Vittone as **CMV**.

The current formal result is a Lean-verified exclusion of every modeled CMV type-(iv) weighted-perimeter minimizer for

$$
\lambda \ge \frac{51}{50}.
$$

On the exact interval $[51/50,9/7]$, Lean checks an equal-area type-(iii) competitor with strictly smaller weighted perimeter. Above $9/7$, the proof uses the geometric two-cap-to-one-cap replacement. The combined theorem is `CMVModeledCutoff.candidate_not_isWeightedPerimeterMinimizer_from_51_50`.

Read the [Lean-verified CMV paper](projects/cmv-strip-density/reports/lean-verified-cmv-cutoff.pdf), or its [HTML edition](projects/cmv-strip-density/reports/lean-verified-cmv-cutoff.html), and the [project reproduction guide](projects/cmv-strip-density/README.md). The paper links every named formal result directly to its Lean declaration and separates the trusted kernel-checked theorem from numerical generators, source interpretation, and open obligations.

This result closes the modeled range $\lambda\ge51/50$. The punctured near-one interval $1<\lambda<51/50$, universal source classification, source-to-model correspondence, and the full CMV conjecture remain open.

## What makes this math assistant unique

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

## Conditional model routing and persistent autorun

`autorun` is an unattended, self-prompting controller for long-running project
work. It reloads the project's `MASTER_PROMPT.md` before every attempt, retains
every prompt, output, receipt, metric, adjudication, and state transition under
`autorun-runs/<session>/`, and resumes the same session after a controller
restart. `attempt_count` tracks every launched conductor attempt; `round_count`
tracks completed executions. The conductor's progress marker is retained as a
claim. A separate read-only adjudicator classifies verified progress as
incremental, meaningful, blocked, or complete; process exit and a passing build
are not meaningful progress.

Projects can route work by reasoning class instead of assigning the most
expensive model to every task:

```toml
[regime]
planner_model = "openai-codex/gpt-5.6-sol"
execution_model = "openai-codex/gpt-5.6-luna"
analysis_model = "openai-codex/gpt-5.6-terra"
invention_model = "openai-codex/gpt-5.6-sol"
audit_model = "openai-codex/gpt-5.6-terra"

strategy_reflection_model = "openai-codex/gpt-6-astra"
targeted_task_model = "openai-codex/gpt-6-astra"
max_targeted_tasks = 1
```

Projects own the strategy threshold, deadline horizon, adjudication budget, and
optional trusted progress measurements:

```toml
[autorun]
worthwhile_likelihood_threshold = 30
strategy_horizon_rounds = 12
adjudication_minutes = 5

[[autorun.progress_metrics]]
id = "coverage"
command = ["python3", "scripts/report_coverage.py"]
timeout = 300
```

Each metric command runs from the project root under the configured execution
policy and must emit one JSON object. Its bounded stdout, stderr, hashes, parsed
value, and error state are retained before adjudication. Keep metric commands in
the trusted project manifest; conductor output cannot add or change them.

The planner leaves a task's `model` field null for normal execution. The
controller then selects `execution_model`, `analysis_model`, `invention_model`,
or `audit_model` from the task's reasoning class. A non-null task model is an
explicit targeted escalation: the controller accepts only the configured
`targeted_task_model` and rejects plans exceeding `max_targeted_tasks`.
Compute profiles may override the same routing fields without changing the
project's base policy.

Strategy review is a fail-closed meaningful-progress gate. At the configured
interval—or when a contract drifts, is falsified, or misses an evidence
deadline—`autorun` launches a separate, read-only Astra request using
`strategy_reflection_model`. The worthwhile threshold comes from `[autorun]`;
Astra cannot choose or relax it. Astra must compare at least two distinct
candidate strategies and return likelihood, expected compute cost, time to first
evidence, ordered observable milestones, kill criteria, and one next action.

The accepted decision is atomically persisted as the active strategy contract
before conductor execution. Milestone and horizon deadlines are measured in
completed executions. A rejected course cannot be reinstated by a later pass,
and a replacement must have higher likelihood than the rejected course while
clearing policy. The controller runs up to three Astra passes; without a valid
contract it retries the gate rather than launching a conductor. The independent
progress adjudicator then evaluates the conductor report, repository evidence,
trusted metrics, and active contract. Drift, falsification, and missed deadlines
force another strategy gate. During a continuous execution-failure streak, one
conductor attempt is routed through `targeted_task_model` after every two failed
primary-model attempts; controller, agent-execution, verification, strategy-gate,
and mathematical-blocker failures have separate retained counters.

Every autorun agent invocation retains the configured transient cgroup deadline,
memory, swap, CPU, task, and file-size limits. A trusted project may set
`execution.sandbox = false` to disable Bubblewrap namespace isolation without
removing those resource ceilings.

Start, inspect, follow, and stop a session with:

```bash
uv run agentic-lean-math-assistant autorun \
  --project path/to/project.toml

uv run agentic-lean-math-assistant autorun-status \
  --session path/to/autorun-runs/<session>

uv run agentic-lean-math-assistant autorun-status \
  --session path/to/autorun-runs/<session> \
  --follow --interval 1 --recap-minutes 10

uv run agentic-lean-math-assistant autorun-output \
  --session path/to/autorun-runs/<session> \
  --interval 1

uv run agentic-lean-math-assistant autorun-events \
  --session path/to/autorun-runs/<session> \
  --interval 1

uv run agentic-lean-math-assistant autorun-stop \
  --session path/to/autorun-runs/<session>
```

Use `--model` to override the primary conductor and `--reflection-model` to
override only the scheduled reflection. The live display identifies the active
route and model. While recovering, it also reports the exact next retry
timestamp, distinguishing bounded backoff from a stopped controller.
The recap reports the latest execution's progress classification, meaningful
versus incremental counts, and the latest Astra likelihood, worthwhile
threshold, decision, and plan status. When Astra changes course, the left status
pane also presents its detailed operator report: rejected course, replacement
method, milestones, first falsifiable check, kill criteria, and next action.

All three followers remain attached while the controller is stopped, paused,
restarted, or temporarily unreadable. They reread `state.json` on every refresh.
The output and raw-event followers switch to `active_round` automatically and
update both their Herdr pane labels and terminal titles to `Round N Output` and
`Round N Raw events`, so a pane cannot remain bound to a completed round.
Interactive followers use a dedicated alternate-screen dashboard and repaint the
entire bounded frame. Prior frames cannot accumulate in pane scrollback or remain
visible after a shorter refresh.

## Useful commands

```text
validate          validate a campaign without running it
run               start a campaign DAG
resume            resume a retained campaign
regime-run        run the fixed research regime
regime-resume     resume a fixed-regime checkpoint
autonomy-run      run bounded successive campaigns
autorun           run a persistent self-prompting conductor
autorun-status    inspect or follow a retained autorun session
autorun-output    follow retained output from the active round
autorun-events    follow raw events while tracking the active round
autorun-stop      request a durable stop at the next safe boundary
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

## References

1. Antonio Cañete, Michele Miranda Jr., and Davide Vittone, “Some Isoperimetric Problems in Planes with Density,” *The Journal of Geometric Analysis* 20 (2010), 243-290. [arXiv:0906.1256](https://arxiv.org/abs/0906.1256).

## License

This repository is currently distributed under the terms in [`LICENSE`](LICENSE).
