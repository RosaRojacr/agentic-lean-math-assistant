# Post-Campaign Main Assessment

Act as the main research agent. Examine every retained task report, receipt, artifact, verification result, failure record, frozen obligation, and strategy lane. Produce the detailed report and strict outcome record below.

## Assessment rules

- Decide whether the original problem was solved, remains unsolved, or is blocked by a concrete unavailable prerequisite.
- Classify the status of the problem's primary requested deliverable, not the quality of the diagnostic response. `solved` means that exact deliverable was produced. A correct explanation that it cannot be produced is not itself `solved`.
- Use `blocked` when a concrete unavailable input, source fragment, credential, tool, or access grant prevents the primary deliverable. Proving that the missing input is necessary, parameterizing the answer, or giving ambiguity witnesses does not convert `blocked` to `solved` unless identifiability or non-uniqueness was itself the primary requested deliverable.
- Use `unsolved` when the requested proof or claim is false, when a counterexample defeats it, or when retained attempts leave it open without a concrete unavailable prerequisite. A counterexample is successful evidence but does not count as the requested proof.
- Treat fallback instructions such as "if unavailable, identify the prerequisite" or "if false, retain a counterexample" as truthfulness requirements, not replacement primary deliverables.
- Treat agreement and prose confidence as no substitute for mathematical evidence.
- Dispose every frozen obligation as `verified`, `rejected`, or `unresolved`; cite retained evidence for every verified or rejected disposition.
- Separate machine-checked, independently reproduced, numerically observed, conjectured, and unresolved claims.
- Preserve exact limitations, stopped pilot lanes, novelty failures, and failed attempts.
- Use exact retained run-relative file paths for every `evidence` entry; explanations belong in `summary` or `reason`.
- Promote knowledge only when the originating successful task has been independently checked by a successful downstream task whose frozen reasoning class is `audit`.
- `knowledge_promotions` may name only originating and verifying tasks in the current frozen plan. Prior accepted-knowledge artifacts are already promoted inputs: cite them as evidence when relevant, but never promote their historical task IDs again.
- Promotion evidence describes what the report establishes; limitations remain attached permanently.
- If unsolved or blocked, propose two to five genuinely distinct executable strategies and mark exactly one recommended.

## Required artifacts

1. Write a detailed Markdown report to the exact report path.
2. Write exactly this JSON structure to the exact outcome path:

```json
{
  "schema_version": 2,
  "status": "solved, unsolved, or blocked",
  "summary": "concise bottom line",
  "evidence": ["exact/run-relative/artifact-path"],
  "limitations": ["precise unresolved limitation"],
  "obligation_dispositions": [
    {
      "id": "frozen_obligation_id",
      "status": "verified, rejected, or unresolved",
      "reason": "precise evidence-based disposition",
      "evidence": ["exact/run-relative/artifact-path"]
    }
  ],
  "knowledge_promotions": [
    {
      "task_id": "originating_task",
      "summary": "claim safe for reuse",
      "evidence": ["exact/run-relative/artifact-path"],
      "limitations": ["scope restriction that must travel with the claim"],
      "verified_by": ["downstream_audit_task"]
    }
  ],
  "strategies": [
    {
      "id": "strategy_id",
      "title": "short strategy title",
      "rationale": "viability and principal tradeoff",
      "next_prompt": "complete directive for the next campaign",
      "recommended": true
    }
  ]
}
```

For `solved`, every frozen obligation must be disposed, none may be unresolved, and `strategies` is empty. For `unsolved` or `blocked`, include two to five strategies and exactly one recommendation. `knowledge_promotions` may be empty; never promote unverified work.

Your terminal response contains only a short confirmation that both files were written.
