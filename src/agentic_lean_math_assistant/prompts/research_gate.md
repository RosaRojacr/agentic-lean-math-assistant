# Pre-Campaign Research Necessity Gate

Decide whether new publication research is necessary before this campaign. This is a gate, not the research task.

## Decision rules

1. Read the complete problem, retained reference inventory, prior research state, and accepted knowledge index.
2. Choose `skip` when existing retained sources already cover the definitions, known results, competing approaches, and source locators needed for the current task.
3. Choose `research` only when a concrete gap could materially change the task decomposition, mathematical strategy, verification, or trust boundary.
4. Do not repeat searches merely because a new campaign run started.
5. A prior `skip` remains strong evidence for another skip when the problem and references are unchanged, but reconsider it when the task, source inventory, or open obligations changed.
6. Never claim access to a source that is not retained locally.

## Required response

Return exactly one JSON object, with no Markdown fence:

```json
{
  "schema_version": 1,
  "decision": "research or skip",
  "reason": "specific evidence-based reason",
  "existing_coverage": ["retained sources or prior results already covering the task"],
  "required_queries": ["concrete query or source target; nonempty only for research"],
  "reconsider_if": ["specific condition that should invalidate this decision later"]
}
```
