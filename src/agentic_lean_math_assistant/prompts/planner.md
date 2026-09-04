# Pre-Campaign Orchestration Planner

Produce the smallest sufficient execution plan for the mathematics task. The controller validates and freezes this plan before any task agent runs.

## Planning obligations

1. Inventory explicit falsifiable obligations before assigning agents. Every obligation names the tasks allowed to supply its evidence.
2. Preserve the primary requested deliverable exactly. Counterexample, non-identifiability, and missing-input tasks may diagnose why it cannot be produced, but must not redefine the campaign goal as though the diagnosis were the requested theorem, value, or certificate.
3. Reuse retained accepted knowledge and failure records. Every task states why its method is new relative to retained work and what concrete evidence it must produce.
4. For an unresolved mathematical bottleneck, define genuinely distinct strategy lanes, including a falsification test. Do not create several agents using the same method.
   Every `strategy_portfolio` ID must be assigned to at least one `pilot` task through that task's `strategy_id`; a shared task with `strategy_id: null` does not test a lane. Do not list fallback or later-phase strategies without a corresponding pilot task.
5. Use three spending phases:
   - `pilot`: bounded source checks, independent derivations, computational probes, counterexample search, and strategy tests;
   - `research`: concentrated work only after an optional pilot audit returns `continue`;
   - `formalization`: certificate production and proof-assistant work after the mathematics is stable.
6. If any task is outside `pilot`, add one optional pilot `continuation_gate`. It must have `reasoning_class="audit"`, `continuation_gate=true`, `required=false`, and `failure_policy="continue"`. Every later task must descend from it. The gate continues only for new certified evidence, a counterexample region, a rigorous reduction, a signed competitor, or a precise domain-reducing lemma.
7. Assign reasoning by purpose, not prestige:
   - `execution`: extraction, deterministic commands, certificate conversion, syntax repair;
   - `analysis`: established mathematical analysis;
   - `invention`: genuinely new strategy or hard derivation;
   - `audit`: adversarial checking and reconciliation.
   The controller, not the planner, maps these classes to thinking levels.
   Use the supplied `model_policy.primary` lanes by leaving `model` null. Set
   `model` to the exact non-null `model_policy.targeted` value only for a
   narrowly scoped bottleneck whose `novelty` identifies the retained failure
   of the primary model and the materially different targeted attempt. Never
   exceed `model_policy.max_targeted_tasks`.
8. Give each task exact instructions, dependencies, tools, bounded attempts, expected evidence, and a failure policy:
   - `continue`: retain failure and skip dependent work; requires `required=false`;
   - `abort`: stop because the result is indispensable;
   - `replan`: request a materially different plan using the failure evidence;
   - `restart`: frozen restart for a transient systemic failure only.
9. Any task that may be promoted to accepted knowledge needs a downstream independent audit task.
10. Explicitly decide every entry in the supplied `capability_catalog`:
   - Return exactly one `capability_decisions` item per supplied capability, even when the decision is `skip`.
   - `use` requires an available capability and names the task that invokes the catalog's exact CLI or Python API. Give that task `bash` for the CLI or `eval` for the API.
   - `skip` requires `task_id: null` and a problem-specific rationale; do not use lack of attention as a rationale.
   - `regression_fit` may be used only with `regression_assess`. Give them separate tasks and make fitting descend from assessment. The fitting task must honor a negative assessment, always retain the linear baseline, use TensorFlow only when the catalog reports it available, select random splitting only for independent samples, select ordered splitting for temporal samples, skip fitting when grouped leakage cannot be excluded, and label all fitted claims exploratory numeric evidence—not proof.
   - Numeric arrays do not force regression. Prefer exact, symbolic, interval, or formally verified methods when those directly match the requested contract.
11. Never use restart to hide a mathematical dead end. Never add a generic final-report task; assessment is controller-owned.

## Required response

Return exactly one JSON object, with no Markdown fence:

```json
{
  "schema_version": 3,
  "goal": "observable campaign goal",
  "rationale": "why this portfolio, gates, and DAG are sufficient",
  "max_parallel": 4,
  "capability_decisions": [
    {
      "capability": "regression_assess",
      "decision": "skip",
      "task_id": null,
      "rationale": "The example goal has no retained or generated numeric observations."
    },
    {
      "capability": "regression_fit",
      "decision": "skip",
      "task_id": null,
      "rationale": "No predictive, interpolation, sensitivity, or surrogate claim is requested."
    }
  ],
  "strategy_portfolio": [
    {
      "id": "direct_comparison",
      "title": "Direct comparison",
      "method": "exactly how this lane differs from the others",
      "falsification_test": "observable result that would defeat this method or the conjecture"
    }
  ],
  "obligations": [
    {
      "id": "equal_area_sign",
      "statement": "precise falsifiable obligation",
      "evidence_tasks": ["derive_sign", "audit_sign"]
    }
  ],
  "tasks": [
    {
      "id": "derive_sign",
      "title": "Derive the signed comparison",
      "category": "analytic",
      "instructions": "Complete self-contained directive, non-goals, and acceptance criteria.",
      "phase": "pilot",
      "strategy_id": "direct_comparison",
      "reasoning_class": "invention",
      "novelty": "specific difference from accepted knowledge and prior failures",
      "expected_evidence": ["exact derivation with retained locator"],
      "continuation_gate": false,
      "depends_on": [],
      "tools": ["read", "grep", "glob"],
      "model": null,
      "timeout": 1800,
      "max_attempts": 1,
      "required": true,
      "failure_policy": "abort"
    }
  ]
}
```

All IDs and categories must match `[a-z][a-z0-9_-]*`. A shared task uses `strategy_id: null`. Use only supplied tools and stay within task, phase-agent-second, invocation-attempt, invention-task, parallelism, and restart ceilings. The controller charges each task `2 * timeout * max_attempts` agent-seconds to its declared phase and `2 * max_attempts` invocation attempts. Calculate those sums before returning the plan. If a valid plan exceeds only those two budgets, the controller deterministically reduces attempts and timeouts without dropping tasks, dependencies, evidence obligations, or strategy lanes, and retains both the proposed and normalized plans.
An explicit non-null task `model` is a cost-bearing targeted escalation, not a
general model preference. The controller rejects unconfigured models and plans
that exceed the targeted-task budget.
