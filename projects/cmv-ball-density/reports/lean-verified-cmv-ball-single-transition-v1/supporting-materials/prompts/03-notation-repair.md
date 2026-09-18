# Isolated mathematical-notation repair pass

You are a mathematical copy editor. This pass changes notation markup only; it must not change any semantic verdict, mathematical claim, evidence, relation, source hash, finding, or declaration coverage.

Read the corrected author handoff at `/mnt/games/Math_Project/LeanExperiment/projects/cmv-ball-density/reports/lean-verified-cmv-ball-single-transition-v1/supporting-materials/reviews/author-02.json` and the accepted semantic review at `/mnt/games/Math_Project/LeanExperiment/projects/cmv-ball-density/reports/lean-verified-cmv-ball-single-transition-v1/supporting-materials/reviews/reviewer-02.json`. Write `/mnt/games/Math_Project/LeanExperiment/projects/cmv-ball-density/reports/lean-verified-cmv-ball-single-transition-v1/supporting-materials/reviews/reviewer-03.json` as strict JSON with exactly the same schema, review order, declaration set, source hashes, relations, and issue-array cardinalities as `reviewer-02.json`.

Requirements:

1. Copy each review's `informal_statement` exactly from the matching classification in `author-02.json`.
2. In `audit_markdown`, every review `reason`, every nonempty issue string, and every generated-family reason or issue, typeset every mathematical symbol, variable, candidate label, expression, interval, relation, and operator with LaTeX. Use only `\(...\)` for inline mathematics and `\[...\]` for display mathematics. Dollar delimiters are forbidden.
3. Write candidate labels as `type \(\mathrm{B}\)` and `type \(\mathrm{C}\)`, never as plaintext `(B)` or `(C)`.
4. Put exact Lean declaration names, theorem names, source identifiers, and Lean expressions in backticks. Lean references inside backticks are the only exemption from LaTeX notation.
5. Make every LaTeX fragment syntactically balanced: matched delimiters, braces, and environments. Preserve prose and evidence as closely as possible; do not summarize or omit anything.
6. Preserve `package_relation = "equivalent"`, every empty issue array, and all 153 review entries. Do not modify any other file.

The deterministic validator in `/mnt/games/Math_Project/LeanExperiment/src/agentic_lean_math_assistant/proof_builder.py` rejects exposed plaintext notation and broken LaTeX. Return a brief completion line on stdout after writing the JSON.
