"""Public API for the deterministic Agentic Lean Math Assistant."""

__version__ = "1.2.0"

from .autonomy import (
    AutonomyError,
    AutonomyRunner,
    AutonomyRuntimeOptions,
    autonomy_status,
    record_autonomy_decision,
)
from .benchmark import (
    BenchmarkRuntime,
    BenchmarkSuite,
    resume_benchmark_suite,
    run_benchmark_suite,
)
from .claims import ClaimProposalBundle, ClaimVerdictBundle, build_claim_ledger
from .config import CampaignSpec, ConfigurationError, ObligationSpec, TargetSpec
from .inspection import inspect_assurance, inspect_claim_ledgers
from .metrics import collect_compute_metrics, write_compute_ledger
from .project import (
    AutonomySpec,
    AutonomySuccessSpec,
    ComputeProfile,
    LeanTheoremSpec,
    ProjectSpec,
)
from .proof_builder import (
    ProofBuilderError,
    ProofPackageResult,
    ProofPackageSpec,
    build_proof_package,
    initialize_proof_manifest,
    resume_proof_package,
    verify_proof_package,
)
from .regime import RegimeError, RegimeOptions, RegimeRunner, choose_strategy
from .regression import (
    RegressionAssessment,
    RegressionConfig,
    RegressionError,
    assess_regression,
    fit_regression,
    load_array,
)
from .runtime import (
    CampaignBuilder,
    CampaignOptions,
    CampaignRunError,
    replay_verifier_command,
)
from .semantic import SemanticReview

__all__ = [
    "AutonomyError",
    "AutonomyRunner",
    "AutonomyRuntimeOptions",
    "AutonomySpec",
    "AutonomySuccessSpec",
    "BenchmarkRuntime",
    "BenchmarkSuite",
    "CampaignBuilder",
    "CampaignOptions",
    "CampaignRunError",
    "CampaignSpec",
    "ClaimProposalBundle",
    "ClaimVerdictBundle",
    "ComputeProfile",
    "ConfigurationError",
    "LeanTheoremSpec",
    "ObligationSpec",
    "ProjectSpec",
    "ProofBuilderError",
    "ProofPackageResult",
    "ProofPackageSpec",
    "RegimeError",
    "RegimeOptions",
    "RegimeRunner",
    "RegressionAssessment",
    "RegressionConfig",
    "RegressionError",
    "SemanticReview",
    "TargetSpec",
    "__version__",
    "assess_regression",
    "autonomy_status",
    "build_claim_ledger",
    "build_proof_package",
    "choose_strategy",
    "collect_compute_metrics",
    "fit_regression",
    "initialize_proof_manifest",
    "inspect_assurance",
    "inspect_claim_ledgers",
    "load_array",
    "record_autonomy_decision",
    "replay_verifier_command",
    "resume_benchmark_suite",
    "resume_proof_package",
    "run_benchmark_suite",
    "verify_proof_package",
    "write_compute_ledger",
]
