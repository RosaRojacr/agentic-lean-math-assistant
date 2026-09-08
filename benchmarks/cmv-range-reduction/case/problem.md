# Cold Reconstruction: Improve the CMV Four-Arc Exclusion Range

## Research objective

Read the supplied primary paper by Cañete, Miranda, and Vittone. Identify a rigorous quantitative improvement to the paper's published exclusion range for regular type-(iv) four-arc candidates in the strip-density isoperimetric problem, and formalize that improvement from a blank Lean project.

The supplied proof directory contains only the Lean/Mathlib build configuration. No prior derivation, proof source, witness, numerical cutoff, or result is supplied. Work from the paper and first principles.

## Required mathematical content

Your retained result must:

1. reconstruct the unit-chord circular-arc length and enclosed-area parametrization used in the comparison;
2. state all parameter domains and inverse branches explicitly;
3. define the comparison function used by the cap-substitution argument;
4. derive its usable derivative formula;
5. prove a global lower bound, not merely locate a numerical stationary point;
6. convert the analytic result into an exact, Lean-checked numerical cutoff that strictly improves the paper's published threshold;
7. explain precisely what this does and does not establish about the full conjecture.

Floating-point exploration may guide the work but is not proof. Every decisive numerical inequality must be reduced to exact rational arithmetic, a proved analytic estimate, or an independently checkable outward-rounded certificate.

## Stable output contract

The final workspace must contain:

- `proof/RangeReduction.lean`, importing every generated proof module and exposing the declarations below;
- `proof/result.json`;
- `proof/verify_certificate.py`;
- `proof/technical-report.md`.

`RangeReduction.lean` must expose these unnamespaced declarations over `ℝ`:

- `ell`, `area`, `θOf`, `arc`, and `g`;
- `ell_formula : ∀ θ : ℝ, ell θ = θ / Real.sin θ`;
- `area_formula : ∀ θ : ℝ, area θ = (θ - Real.sin θ * Real.cos θ) / (4 * Real.sin θ ^ 2)`;
- `thetaOf_mem : ∀ {x : ℝ}, 0 < x → θOf x ∈ Set.Ioo 0 Real.pi`;
- `area_thetaOf : ∀ {x : ℝ}, 0 < x → area (θOf x) = x`;
- `arc_formula : ∀ x : ℝ, arc x = ell (θOf x)`;
- `g_formula : ∀ x : ℝ, g x = 2 * arc x - arc (2 * x)`;
- `hasDerivAt_arc : ∀ {x : ℝ}, 0 < x → HasDerivAt arc (2 * Real.sin (θOf x)) x`;
- `min_g_gt_pi_div_four : ∀ {x : ℝ}, 0 < x → Real.pi / 4 < g x`;
- `cmv_range_reduction`, with the exact type determined by the certified cutoff recorded in `result.json`:

```lean
∀ {lam x : ℝ}, (CUTOFF : ℝ) ≤ lam → 0 < x → 1 / lam < g x
```

The declaration names are fixed for mechanical evaluation; they do not prescribe the proof route or intermediate decomposition.

`result.json` must be canonical JSON with exactly:

```json
{
  "artifact_type": "application/vnd.agentic-lean.cmv-range-reduction.v1+json",
  "certificate_checker": "verify_certificate.py",
  "cutoff": "DECIMAL",
  "declaration": "cmv_range_reduction",
  "module": "RangeReduction",
  "report": "technical-report.md",
  "schema_version": 1
}
```

`cutoff` must be a finite decimal greater than `1`. Smaller is stronger. Do not report more precision than the exact certificate proves.

## Evidence and honesty requirements

- Cite the paper by page, theorem, remark, equation, or other precise locator for every borrowed fact.
- Distinguish published statements, new derivations, numerical observations, formal theorems, and unresolved obligations.
- Run `lake build` from `proof/` and retain the command output.
- Run `verify_certificate.py` from `proof/`; it must exit nonzero on a failed check.
- Do not use `sorry`, `admit`, unsafe declarations, or unproved axioms.
- Do not claim the full CMV conjecture is solved unless the produced theorem actually establishes it without additional geometric hypotheses.
