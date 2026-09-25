import CMVElementaryAudit

/-
Elaborated certificate for the corrected P(C)-P(E) theorem, not the printed
A(C)-P(E) statements. Exact types and axiom prints for all four roots are in
CMVElementaryAudit. No external classification or BV assertion is used here.
-/
open CMVElementary

-- The endpoint instantiates only the four-arc carrier at one.
example (lam : ℝ) (hlam : 1 < lam) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      WeightedArea lam (E lam r) = WeightedArea lam (C lam 1) ∧
      gamma lam < WeightedPerimeter lam (FrontierMeasure (C lam 1)) -
        WeightedPerimeter lam (FrontierMeasure (E lam r)) := by
  obtain ⟨r, hr, hr1, ha, hp, _⟩ :=
    (geometric_comparison lam hlam).2 1 zero_lt_one le_rfl
  exact ⟨r, hr, hr1, ha, by simpa only [div_one] using hp⟩

namespace GeometricRootsAudit
open Lean

-- Retained audits use this same traversal of elaborated types and proof values.
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
    (``geometric_comparison, ``scalar_comparison),
    (``geometric_comparison, ``geometric_realization),
    (``geometric_comparison, ``FourArcRealization.area_formula),
    (``geometric_comparison, ``FourArcRealization.perimeter_formula),
    (``geometric_comparison, ``ThreeArcRealization.area_formula),
    (``geometric_comparison, ``ThreeArcRealization.perimeter_formula),
    (``geometric_realization, ``GeometryBridge.four_realization),
    (``geometric_realization, ``GeometryBridge.three_realization)]
  for (src, dst) in edges do
    let info ← getConstInfo src
    let some proof := info.value? (allowOpaque := true)
      | throwError "No elaborated proof value: {src}"
    unless proof.getUsedConstants.contains dst do
      throwError "Missing elaborated proof edge: {src} -> {dst}"
    logInfo m!"EDGE {src} -> {dst}"
  let scalarRequired := [``J_lower, ``H_lower, ``support_identity, ``area_identity,
    ``MonotoneTangent.h_lower_third_of_monotone_tangent,
    ``A3_tendsto_atRight_zero, ``three_arc_variational_hasDerivAt,
    ``DerivativePilot.sqrt_normalization, ``exists_greatest_level_root,
    ``strict_support_comparison, ``greatest_root_claims]
  let geometryRequired := [``GeometryBridge.C_assembly,
    ``GeometryBridge.K_core, ``GeometryBridge.cap4_upper, ``GeometryBridge.cap4_lower,
    ``GeometryBridge.four_regularity, ``GeometryBridge.four_upper_chord,
    ``GeometryBridge.four_lower_chord, ``GeometryBridge.C_area, ``GeometryBridge.C_perimeter,
    ``FourArcCandidate.candidate_area_formula, ``FourArcCandidate.candidate_perimeter_formula,
    ``FourArcAssembly.weightedArea_formula, ``fourArc_frontier_weightedPerimeter_eq,
    ``fourArc_euclidean_frontier, ``GeometryBridge.E_assembly,
    ``GeometryBridge.K3_core, ``GeometryBridge.cap3_outer, ``GeometryBridge.three_regularity,
    ``GeometryBridge.three_strict_chord, ``GeometryBridge.E_bottom_frontier,
    ``GeometryBridge.E_half_disk, ``TypeThreeAssembly.weightedArea_formula,
    ``TypeThreeAssembly.weightedPerimeter_formula, ``TypeThreeAssembly.euclidean_frontier,
    ``TypeThreeAssembly.bottomSegmentCarrier_subset_frontier]
  let roots := [( ``elementary_route, scalarRequired),
    (``scalar_comparison, scalarRequired),
    (``geometric_realization, geometryRequired),
    (``geometric_comparison, scalarRequired ++ geometryRequired)]
  let forbidden := ["universalstationarypair", "typefourstationaryroot", "equalareaenvelope",
    "not_isweightedperimeterminimizer", "cmvsuffixmodel", "sorryax"]
  let forbiddenFrozen := ["fold", "descending", "stationary", "root_unique", "envelope"]
  for (root, required) in roots do
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

end GeometricRootsAudit
