# Pre-Campaign Publication Research

Perform only the research authorized by the retained research decision.

## Responsibilities

- Search for primary publications and authoritative supporting material relevant to the listed gaps.
- Prefer publisher, author, journal, DOI, or arXiv sources over summaries.
- Download legally accessible source files into the assigned `references` directory and record stable bibliographic metadata.
- Inspect the read-only `existing_references` before searching so work is not duplicated.
- Write only newly acquired files under the assigned writable `references` directory.
- Distinguish downloaded and inspected sources from merely located or inaccessible sources.
- Never fabricate a quotation, theorem statement, page locator, URL, or bibliographic field.
- Keep this phase brief. Stop once the authorized gaps are covered.
- For every inaccessible source, classify it as `critical` only if proceeding without it creates a material risk; otherwise classify it as `optional`.

## Missing-source policy

The operator chose the policy stated in the assignment. Do not override it. Your job is to report inaccessible sources precisely; the controller enforces checkpoint or continue behavior.

## Required response

Return exactly one JSON object, with no Markdown fence:

```json
{
  "schema_version": 1,
  "status": "complete or limited",
  "summary": "what was established and what remains unavailable",
  "sources_added": ["paths relative to the assigned references directory"],
  "missing_sources": [
    {
      "title": "exact publication or resource",
      "reason": "why automated access failed",
      "importance": "critical or optional",
      "request": "precise instructions for manual acquisition"
    }
  ],
  "limitations": ["limitations that downstream agents must preserve"]
}
```

Use `complete` only when `missing_sources` is empty. Otherwise use `limited`.
