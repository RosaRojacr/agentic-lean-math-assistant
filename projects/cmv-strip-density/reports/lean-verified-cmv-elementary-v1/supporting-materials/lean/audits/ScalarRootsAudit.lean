import CMVElementary

/-
Exact proof-term and elaborated-dependency certificate for the two scalar roots.
Corrected target: P_lambda(C_h)-P_lambda(E_r)>gamma_lambda/h>0.
The PDF's printed A-minus-P expression is false and is not certified.
-/

open CMVElementary Set

example : ∀ lam : ℝ, 1 < lam → ElementaryRoute lam := elementary_route

example : ∀ lam : ℝ, 1 < lam →
    0 < gamma lam ∧
    ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ r : ℝ, 0 < r ∧ r < h ∧ A3 lam r = A4 lam h ∧
        gamma lam / h < P4 lam h - P3 lam r ∧ 0 < gamma lam / h :=
  scalar_comparison

-- The closed endpoint still gives a strictly interior, equal-area witness.
example (lam : ℝ) (hlam : 1 < lam) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ A3 lam r = A4 lam 1 ∧
      gamma lam < P4 lam 1 - P3 lam r := by
  obtain ⟨r, hr0, hr1, ha, hp, _⟩ := (scalar_comparison lam hlam).2 1 zero_lt_one le_rfl
  exact ⟨r, hr0, hr1, ha, by simpa only [div_one] using hp⟩

#print axioms CMVElementary.elementary_route
#print axioms CMVElementary.scalar_comparison
#print axioms CMVElementary.greatest_root_claims

namespace ScalarRootsAudit
open Lean

-- Same elaborated traversal convention as the retained ingredient certificates.
partial def dependencies (env : Environment) (todo : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then dependencies env rest seen
    else
      let used := match env.find? n with
        | none => []
        | some ci => ci.type.getUsedConstants.toList ++
            ((ci.value? (allowOpaque := true)).map (fun v => v.getUsedConstants.toList)).getD []
      dependencies env (used ++ rest) (seen.insert n)

run_cmd do
  let edges : Array (Name × Name) := #[
    (``scalar_comparison, ``elementary_route),
    (``scalar_comparison, ``ElementaryRoute.greatest_root),
    (``scalar_comparison, ``GreatestRootClaims.q_strict),
    (``scalar_comparison, ``SameCurvatureClaims.support_gap),
    (``elementary_route, ``auxiliary_claims),
    (``elementary_route, ``same_curvature_claims),
    (``elementary_route, ``three_arc_calculus_claims),
    (``elementary_route, ``scalar_identification_claims),
    (``elementary_route, ``greatest_root_claims),
    (``greatest_root_claims, ``three_arc_calculus_claims),
    (``greatest_root_claims, ``ThreeArcCalculusClaims.area_limit_zero),
    (``greatest_root_claims, ``same_curvature_claims),
    (``greatest_root_claims, ``SameCurvatureClaims.area_gap),
    (``greatest_root_claims, ``exists_greatest_level_root),
    (``greatest_root_claims, ``strict_support_comparison),
    (``same_curvature_claims, ``J_lower),
    (``same_curvature_claims, ``H_lower),
    (``same_curvature_claims, ``support_identity),
    (``same_curvature_claims, ``area_identity),
    (``H_lower, ``MonotoneTangent.h_lower_third_of_monotone_tangent)]
  for (src, dst) in edges do
    let info ← getConstInfo src
    let some proof := info.value? (allowOpaque := true)
      | throwError "No elaborated proof value: {src}"
    unless proof.getUsedConstants.contains dst do
      throwError "Missing elaborated proof edge: {src} -> {dst}"
    logInfo m!"EDGE {src} -> {dst}"
  let forbidden := ["universalstationarypair", "typefourstationaryroot", "equalareaenvelope",
    "not_isweightedperimeterminimizer", "cmvsuffixmodel"]
  let forbiddenFrozen := ["fold", "descending", "stationary", "root_unique", "envelope"]
  let required := [``J_lower, ``H_lower, ``support_identity, ``area_identity,
    ``MonotoneTangent.h_lower_third_of_monotone_tangent,
    ``A3_tendsto_atRight_zero, ``three_arc_variational_hasDerivAt,
    ``DerivativePilot.sqrt_normalization, ``exists_greatest_level_root,
    ``strict_support_comparison, ``greatest_root_claims]
  for root in [``elementary_route, ``scalar_comparison] do
    let axioms ← collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Rejected axiom {ax} in {root}"
    let deps := dependencies (← getEnv) [root]
    for dep in required do
      unless deps.contains dep do
        throwError "Missing required transitive dependency {dep} in {root}"
      logInfo m!"REQUIRED {root} -> {dep}"
    for dep in deps.toArray do
      let name := dep.toString.toLower
      if forbidden.any (fun s => (name.splitOn s).length > 1) ||
          (name.startsWith "leansuffixanalytic." &&
            forbiddenFrozen.any (fun s => (name.splitOn s).length > 1)) then
        throwError "Rejected dependency {dep} in {root}"
    logInfo m!"AUDIT {root}: {deps.size} transitive declarations; allowed axioms only; required route present; forbidden comparisons absent"
    let sorted := deps.toArray.qsort (fun a b => a.toString < b.toString)
    for dep in sorted do
      logInfo m!"DEP {root} -> {dep}"

end ScalarRootsAudit
