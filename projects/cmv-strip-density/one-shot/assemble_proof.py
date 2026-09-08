from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path.cwd()
PROOF = ROOT / "proof"
REQUIRED_MODULES = (
    "MorgansArcFunction.lean",
    "GFunction.lean",
    "Minimiser.lean",
    "MinimumValue.lean",
    "Certificate.lean",
    "CMVGeometry.lean",
    "FrontierPerimeter.lean",
    "FourArcCandidate.lean",
    "CapReplacement.lean",
    "GeometricBridge.lean",
    "TypeThreeAssembly.lean",
    "CandidateExclusion.lean",
)

RANGE_REDUCTION = """import CandidateExclusion
import TypeThreeAssembly

/-!
# One-shot CMV range-reduction deliverable

This root exposes the scalar certificate, modeled type-(iv) exclusion, and
branch-complete modeled type-(iii) coordinate contract through stable
declarations.  Source-facing CMV identification remains an explicit external
premise, as documented in the cited report.
-/

noncomputable section

/-- The certified scalar cap comparison at the inclusive decimal cutoff. -/
theorem cmv_range_reduction {lam x : ℝ}
    (hlam : (1.2581840884 : ℝ) ≤ lam)
    (hx : 0 < x) :
    1 / lam < g x :=
  cmv_comparison_bound_optimized hlam hx

/-- The remaining open range for an explicitly modeled type-(iv) minimizer. -/
theorem cmv_type_four_range_reduction {lam : ℝ}
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    1 < lam ∧ lam < (1.2581840884 : ℝ) :=
  type_four_minimizer_open_range candidate hcandidate hmin

/-- The regular modeled type-(iii) carrier covers its complete finite branch
partition, including the point-segment degeneration at `h = 1 / 2`. -/
theorem cmv_type_three_branch_contract {lam : ℝ}
    (assembly : TypeThreeAssembly lam) :
    (assembly.h < 1 / 2 →
      assembly.branch = .major ∧
        Real.pi / 2 < assembly.outerAngle ∧ 0 < assembly.bottomChord) ∧
    (assembly.h = 1 / 2 →
      assembly.branch = .semicircular ∧
        assembly.outerAngle = Real.pi / 2 ∧ assembly.bottomChord = 0) ∧
    (1 / 2 < assembly.h →
      assembly.branch = .minor ∧
        assembly.outerAngle < Real.pi / 2 ∧ 0 < assembly.bottomChord) :=
  assembly.branch_complete

#print axioms cmv_range_reduction
#print axioms cmv_type_four_range_reduction
#print axioms cmv_type_three_branch_contract
"""


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    missing = [name for name in REQUIRED_MODULES if not (PROOF / name).is_file()]
    if missing:
        raise SystemExit(f"missing required Lean modules: {missing}")

    destination = PROOF / "RangeReduction.lean"
    destination.write_text(RANGE_REDUCTION, encoding="utf-8")
    lakefile = PROOF / "lakefile.toml"
    lakefile_text = lakefile.read_text(encoding="utf-8")
    old_roots = '"GeometricBridge", "CandidateExclusion", "TypeThreeAssembly"]'
    new_roots = (
        '"GeometricBridge", "CandidateExclusion", "TypeThreeAssembly", '
        '"RangeReduction"]'
    )
    old_targets = (
        'defaultTargets = ["Certificate", "CandidateExclusion", '
        '"TypeThreeAssembly"]'
    )
    new_targets = (
        'defaultTargets = ["Certificate", "CandidateExclusion", '
        '"TypeThreeAssembly", "RangeReduction"]'
    )
    if old_roots not in lakefile_text or old_targets not in lakefile_text:
        raise SystemExit("lakefile.toml has an unexpected target or root list")
    lakefile.write_text(
        lakefile_text.replace(old_roots, new_roots, 1).replace(
            old_targets, new_targets, 1
        ),
        encoding="utf-8",
    )

    files = [*REQUIRED_MODULES, destination.name]
    manifest = {
        "schema_version": 1,
        "root": destination.name,
        "declarations": [
            "cmv_range_reduction",
            "cmv_type_four_range_reduction",
            "cmv_type_three_branch_contract",
        ],
        "files": [
            {
                "path": name,
                "sha256": sha256(PROOF / name),
                "size": (PROOF / name).stat().st_size,
            }
            for name in files
        ],
    }
    (PROOF / "proof-manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print("assembled proof/RangeReduction.lean")
    print(f"manifested {len(files)} Lean modules")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
