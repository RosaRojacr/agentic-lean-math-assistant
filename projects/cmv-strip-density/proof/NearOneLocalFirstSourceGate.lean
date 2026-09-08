/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalThirdSource
import NearOneLocalPredictor

/-!
# Source-side complete-third gate for the seam cell

This module discharges the three source denominators before applying the grouped
complete-third identity on the retained target band 0, cell 0.  It does not yet
identify the emitted CSE arithmetic or prove its centered interval enclosure.
-/

namespace NearOneLocalFirstSourceGate

open NearOneAnalyticSystem NearOneRegularizedThirdRow
open NearOneLocalCoordinates NearOneLocalThirdSource
open NearOneLocalPredictor
noncomputable section

private def seamS (mu dTau : ℝ) : ℝ :=
  (firstScale : ℝ) *
    ((firstTauCenter : ℝ) +
      (firstTauSlope : ℝ) * (mu - (firstMuMid : ℝ)) + dTau)

private def seamU (mu du : ℝ) : ℝ :=
  (firstUCenter : ℝ) +
    (firstUSlope : ℝ) * (mu - (firstMuMid : ℝ)) + du

private def seamV (mu dv : ℝ) : ℝ :=
  (firstVCenter : ℝ) +
    (firstVSlope : ℝ) * (mu - (firstMuMid : ℝ)) + dv

private def seamW (mu dw : ℝ) : ℝ :=
  (firstBCorrectionCenter : ℝ) +
    (firstBCorrectionSlope : ℝ) * (mu - (firstMuMid : ℝ)) + dw

/-- The existing seam-cell interval proofs establish every denominator needed
by the complete source reconstruction, in dependency order. -/
theorem seam_source_guards {mu dTau du dv dw : ℝ}
    (hmu : firstMuInterval.RealContains mu)
    (hdTau : firstTauDisplacement.RealContains dTau)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    seamS mu dTau ≠ 0 ∧
    1 - yCoord (seamS mu dTau)
      (physicalZ (seamS mu dTau) Real.pi (seamU mu du)) ^ 2 ≠ 0 ∧
    1 + seamS mu dTau * yCoord (seamS mu dTau)
      (physicalZ (seamS mu dTau) Real.pi (seamU mu du)) ≠ 0 ∧
    1 + wCoord (seamS mu dTau)
        (physicalA (seamS mu dTau) Real.pi (seamV mu dv)) *
      vCoord (seamS mu dTau)
        (physicalZ (seamS mu dTau) Real.pi (seamU mu du))
        (physicalA (seamS mu dTau) Real.pi (seamV mu dv))
        (physicalB (seamS mu dTau) Real.pi (seamW mu dw)) ≠ 0 := by
  let s := seamS mu dTau
  let u := seamU mu du
  let v := seamV mu dv
  let w := seamW mu dw
  have hz : physicalZ s Real.pi u =
      Real.pi + (Real.pi ^ 2 * s + u * s ^ 2) := by
    simp only [physicalZ]
    ring
  have ha : physicalA s Real.pi v =
      (((5 / 12 : ℚ) : ℝ) * Real.pi +
        (s * (((1 / 144 : ℚ) : ℝ) *
          (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
          (s * s) * v)) := by
    simp only [physicalA]
    norm_num
    ring
  have hb : physicalB s Real.pi w =
      ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
        (s * (((1 / 216 : ℚ) : ℝ) *
          (Real.pi *
            (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
          (s * s) * w) := by
    simp only [physicalB]
    norm_num
    ring
  have hsEnclosure := first_s_pos_enclosure hmu hdTau
  have hyEnclosure := first_density_den_enclosure hmu hdTau hdu
  have hdFourEnclosure := first_angle_den_four_enclosure hmu hdTau hdu
  have hdThreeEnclosure := first_angle_den_three_enclosure
    hmu hdTau hdu hdv hdw
  have hs : 0 < s := by
    apply ScalarSuffixCertificate.QInterval.positive_of_realContains
      (i := firstSPosCertificate) (x := s)
    · simpa only [s, seamS] using hsEnclosure
    · norm_num [firstSPosCertificate]
  have hy : 0 < 1 - yCoord s (physicalZ s Real.pi u) ^ 2 := by
    apply ScalarSuffixCertificate.QInterval.positive_of_realContains
      (i := firstDensityDenCertificate)
    · dsimp only at hyEnclosure
      change firstDensityDenCertificate.RealContains
        (1 - yCoord s (Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)) ^ 2)
        at hyEnclosure
      rwa [← hz] at hyEnclosure
    · norm_num [firstDensityDenCertificate]
  have hdFour : 0 < 1 + s * yCoord s (physicalZ s Real.pi u) := by
    apply ScalarSuffixCertificate.QInterval.positive_of_realContains
      (i := firstAngleDenFourCertificate)
    · dsimp only at hdFourEnclosure
      change firstAngleDenFourCertificate.RealContains
        (1 + s * yCoord s (Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)))
        at hdFourEnclosure
      rwa [← hz] at hdFourEnclosure
    · norm_num [firstAngleDenFourCertificate]
  have hdThree : 0 < 1 + wCoord s (physicalA s Real.pi v) *
      vCoord s (physicalZ s Real.pi u)
        (physicalA s Real.pi v) (physicalB s Real.pi w) := by
    apply ScalarSuffixCertificate.QInterval.positive_of_realContains
      (i := firstAngleDenThreeCertificate)
    · dsimp only at hdThreeEnclosure
      change firstAngleDenThreeCertificate.RealContains
        (1 + wCoord s
            ((((5 / 12 : ℚ) : ℝ) * Real.pi +
              (s * (((1 / 144 : ℚ) : ℝ) *
                (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
                (s * s) * v))) *
          vCoord s (Real.pi + (Real.pi ^ 2 * s + u * s ^ 2))
            ((((5 / 12 : ℚ) : ℝ) * Real.pi +
              (s * (((1 / 144 : ℚ) : ℝ) *
                (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
                (s * s) * v)))
            (((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) *
                (Real.pi * Real.pi)) +
              (s * (((1 / 216 : ℚ) : ℝ) *
                (Real.pi * (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) -
                  (14256 : ℝ)))) + (s * s) * w)))
        at hdThreeEnclosure
      rwa [← hz, ← ha, ← hb] at hdThreeEnclosure
    · norm_num [firstAngleDenThreeCertificate]
  exact ⟨ne_of_gt hs, ne_of_gt hy, ne_of_gt hdFour, ne_of_gt hdThree⟩

/-- Source-connected complete analytic identity on every point of the seam
cell.  This closes the source-side guard obligation for this sample only. -/
theorem seam_sourceGroupedThird_div_sq_eq_complete_div_four
    {mu dTau du dv dw : ℝ}
    (hmu : firstMuInterval.RealContains mu)
    (hdTau : firstTauDisplacement.RealContains dTau)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    sourceGroupedThird (seamS mu dTau) Real.pi
        (seamU mu du) (seamV mu dv) (seamW mu dw) /
        seamS mu dTau ^ 2 =
      completeThirdRowNumerator (seamS mu dTau)
        (physicalZ (seamS mu dTau) Real.pi (seamU mu du))
        (physicalA (seamS mu dTau) Real.pi (seamV mu dv))
        (physicalB (seamS mu dTau) Real.pi (seamW mu dw)) Real.pi /
        seamS mu dTau ^ 4 := by
  rcases seam_source_guards hmu hdTau hdu hdv hdw with
    ⟨hs, hy, hdFour, hdThree⟩
  exact sourceGroupedThird_div_sq_eq_complete_div_four
    (seamS mu dTau) Real.pi (seamU mu du) (seamV mu dv) (seamW mu dw)
    hs hy hdFour hdThree

end

end NearOneLocalFirstSourceGate
