/-
Copyright (c) 2026 author. Released under Apache 2.0 license.
-/
import CMVElementaryGeometry

/-!
# Exact proof-term audit of the four corrected explicit-family roots

The four examples below independently state the retained contract types and
check actual proof terms, not equalities between proposition definitions.
Each root also has a `#print axioms` check. Only propext, Classical.choice and
Quot.sound are permitted.

Reproduce from the workspace root:
`python agents/formalization/geometric_roots/verify.py`
This builds the library, compiles this module, and runs the retained scalar and
geometric elaborated-dependency audits. The latter traverse opaque proof values,
require the new J/H and greatest-root/Q route and actual integral/frontier
identities, and reject the old all-density/stationary/fold-envelope shortcuts.
Evidence is retained in `agents/formalization/geometric_roots/verification.json`
and its associated logs. The supplied snapshot lacks project.toml; no missing
metadata is reconstructed or certified by these retained Lean type checks.

## Source-level scope (not Lean assertions or assumptions)

In `references/references/CMV_Strip_Density_Problem.pdf`, BOTH Theorem 1 displays
(page 2, Section 2.1.2; page 3, equation (3.2)) must read
P_lambda(C_h) - P_lambda(E_r) > gamma_lambda/h > 0,
NOT A_lambda(C_h) - P_lambda(E_r). The literal A-minus-P assertion is false and
is not certified. The original PDF is unchanged; verification checks SHA-256
d04a2e8e2ad45fe505345037c046ceaeb2a8d63b9e2b1c1eeb020b5251c576ff.

The following classification corollary is INFORMAL, not a Lean theorem or axiom.
In `references/references/Canete2010.pdf`, Lemma 3.8 (including the horizontal
symmetry of type (iv) in its proof, Step 2) classifies vertically symmetric
candidates; Proposition 3.9 supplies vertical symmetry for arbitrary minimizers.
Theorem 3.16 supplies the area ranges and transition coexistence, leaving only
type (iv) to exclude for all densities. Combining those external results with
the corrected explicit-region comparison gives the cited Conjecture 3.12:
for each lambda > 1, a threshold v0 > pi separates balls (0 < v <= pi),
stadiums (pi <= v <= v0), and three-arc minimizers (v >= v0).
At pi the stadium degenerates to a disk. At v0 stadium and three-arc minimizers
coexist; no uniqueness is asserted. Classification is up to density-preserving
isometries and the appropriate measure equivalence, not literal set equality.

Canete2010, Remark 3.17 explains the older argument's limitation: its replacement
of two caps by one proves exclusion for lambda >= 4/pi (with some improvement),
but not for lambda close to one. The present J/H and greatest-root proof does
not use that final comparison and retains every lambda > 1.

The draft's page-2 claim that the conjecture holds in full is thus a cited
corollary using the external classification, not an extra kernel conclusion.
Its page-8 Remark 3 correctly restricts the self-contained theorem to the
explicit regions. The boundary convention in draft Section 3 (page 3) transfers
between complete and reduced boundaries for these finite piecewise-circular
Jordan representatives: the two agree H^1-almost everywhere, including the
interface-density convention of one. Applying the comparison to arbitrary
minimizers first requires the external identification of regular representatives.
Reduced-boundary perimeter respects area-null modifications; complete-frontier
perimeter need not. Neither that BV transfer, external classification, nor the
entire unrestricted conjecture is formalized or assumed as an axiom here.

No uniform positive margin down to lambda=1 is claimed. The draft records gamma
approaching zero as lambda decreases to one and, at lambda=1, A_i(t)=pi/t^2 and
P_i(t)=2*pi/t. These boundary explanations are not additional proved roots here.
-/

open CMVElementary

-- Inhabited elementary-route theorem at the exact supporting type.
example : ∀ lam : ℝ, 1 < lam → CMVElementary.ElementaryRoute lam :=
  CMVElementary.elementary_route

#print axioms CMVElementary.elementary_route

-- Inhabited scalar theorem at its fully expanded contract type.
example :
    (∀ lam : ℝ, 1 < lam →
      0 < CMVElementary.gamma lam ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        ∃ r : ℝ, 0 < r ∧ r < h ∧
          CMVElementary.A3 lam r = CMVElementary.A4 lam h ∧
          CMVElementary.gamma lam / h <
            CMVElementary.P4 lam h - CMVElementary.P3 lam r ∧
          0 < CMVElementary.gamma lam / h) := CMVElementary.scalar_comparison

#print axioms CMVElementary.scalar_comparison

-- Inhabited realization theorem, not merely an equality of proposition definitions.
example : ∀ lam : ℝ, 1 < lam →
    (∀ h : ℝ, 0 < h → h ≤ 1 → CMVElementary.FourArcRealization lam h) ∧
    (∀ r : ℝ, 0 < r → r < 1 → CMVElementary.ThreeArcRealization lam r) :=
  CMVElementary.geometric_realization

#print axioms CMVElementary.geometric_realization

-- Inhabited geometric comparison at its independently expanded contract type.
example :
    (∀ lam : ℝ, 1 < lam →
      0 < CMVElementary.gamma lam ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        ∃ r : ℝ, 0 < r ∧ r < h ∧
          WeightedArea lam (CMVElementary.E lam r) =
            WeightedArea lam (CMVElementary.C lam h) ∧
          CMVElementary.gamma lam / h <
            WeightedPerimeter lam (FrontierMeasure (CMVElementary.C lam h)) -
              WeightedPerimeter lam (FrontierMeasure (CMVElementary.E lam r)) ∧
          0 < CMVElementary.gamma lam / h) := CMVElementary.geometric_comparison
 
#print axioms CMVElementary.geometric_comparison

-- Retained general-purpose helpers used by the greatest-root/Q proof.
#print axioms CMVElementary.exists_greatest_level_root
#print axioms CMVElementary.strict_support_comparison
#print axioms CMVElementary.exists_equal_area_strict_support_comparison
