# Changelog

## Unreleased

### CMV formalization

- Completed the kernel-replayed 113-cell middle-face inventory, the 1,024-cell
  compact inventory, and both exact prototype seams. `CMVModeledCutoff`
  composes these candidate-facing type-(iii) improvements with the geometric
  cap-replacement theorem to exclude every modeled type-(iv) minimizer for
  \(\lambda\ge51/50\), including the \(h=1\) endpoint.
- Added source-coordinate transfer theorems with explicit normalization and
  boundary-semantics contracts; canonical complete-frontier semantics
  discharge those contracts internally.
- Replaced the scalar-only paper with a cited Lean-verified cutoff paper in
  Markdown, standalone HTML, and PDF, including direct declaration links,
  pinned reproduction commands, and an explicit statement of the remaining
  \(1<\lambda<51/50\) scope.

### Unattended operation

- Added the persistent `autorun` mode and direct command. It reloads a
  user-editable project `MASTER_PROMPT.md` before every self-directed conductor
  round, retains prompts and receipts, resumes after controller interruption,
  recovers from agent failures with bounded backoff, and forces periodic
  strategy and ALMA-improvement reflection.
- Added a pane-bounded graphical autorun readout with ten-minute, milestone-rich
  verbal progress recaps, plus incrementally followable round output logs.
- Added reasoning-class model routing, a separately bounded read-only strategy
  reflection model, and controller-enforced limits for explicit targeted-model
  escalations.


## 1.1.1 — 2026-08-31

### Release engineering

- Enabled the bubblewrap user-namespace runtime required by the fail-closed
  sandbox on GitHub-hosted Linux runners.
- Fixed sandbox visibility for versioned Python installations reached through
  virtual-environment and managed-runtime symlink aliases.
- Isolated the Lean-backed benchmark calibration in the retained-certificate
  job and installed its locked Python dependencies before verification.
- Retain pytest run artifacts for three days when a Python CI job fails.

## 1.1.0 — 2026-08-31

### CMV continuation

- Promoted the retained full-domain directed-MPFR ledgers into the canonical
  proof tree and added a hash-bound exact-ledger replay to the project success
  checks. The replay covers the low-density scaled regime, the compact
  \([17/16,3/2]\) regime, and the rational analytic-tail margins; it does not
  independently recompute the transcendental interval enclosures.
- Formalized the type-(iii) principal-angle incidence equation and the shared
  upper-junction coordinates between its strip arcs and exterior cap.
- The full-domain scalar conclusion remains conditional on the equal-area
  reduction and source-to-model bridge; no full CMV theorem is claimed.
- Added a canonical mutation-sensitive calculus checker for the independently
  derived type-(iii)/(iv) Green-integral normal forms, exact fold derivatives,
  and \(P_i'(h)=hA_i'(h)\). The new evidence reduces the scalar problem to the
  attained type-(iv) fold-gap sign but does not prove that sign on the full
  unresolved interval.
- Retained an independent exact-rational compact fold-gap certificate and
  fail-closed checker. It covers \([33/32,9/7]\) with 1,024 adjacent boxes,
  proves both implicit roots unique in every box, recomputes rational
  elementary-function enclosures, leaves no unresolved boxes, and rejects all
  four retained certificate mutations. The near-one interval and Lean
  translation remain open.
- Retained the exact near-one germ checker, a fail-closed opposite-face
  prototype, and a 113-brick middle certificate. Together with the compact
  certificate they prove the scalar suffix \([51/50,9/7]\), with exact seams
  and 30 middle-certificate mutations rejected. The attempted near-one
  barrier failed independent face, germ-initialization, and endpoint branch
  checks, so the punctured near-one interval and Lean translation remain open.

### Publication and reliability

- Added the publication-ready scalar-suffix paper in Markdown, standalone
  HTML, and PDF, with exact theorem scope, proof decomposition, trust boundary,
  reproduction commands, artifact hashes, and explicit open obligations.
- Failed agent stages now retain regular files from their personal workspace
  under an attempt-scoped partial-artifact directory before deterministic
  checkpoint restoration. This prevents useful certificates and diagnostics
  from being erased when an agent times out without final prose.

## 1.0.0 — release candidate

Agentic Lean Math Assistant 1.0 is the first employer-facing release of the retained
research system and its CMV proof case study.

### Campaign engine

- Added strict, manifest-driven research and build DAGs with immutable inputs,
  durable state, bounded recovery, and content-addressed evidence.
- Added OS-enforced Linux execution containment with explicit network, resource,
  environment, executable, and secret policies.
- Added typed claim proposal, independent verification, adjudication, target
  closure, and replay contracts.
- Separated Lean kernel acceptance from informal-to-formal semantic review.
- Added fixed-regime, bounded-autonomy, benchmark, and regression-assessment
  workflows with retained compute and failure evidence.

### CMV case study

- Retained the exact Lean and arithmetic certificates for the modeled type-(iv)
  range reduction at the inclusive cutoff `1.2581840884`.
- Added a branch-complete modeled type-(iii) coordinate carrier, including its
  major, semicircular, and minor exterior-arc regimes.
- Added citation-complete HTML/PDF reports, a one-page portfolio summary, an
  independently replayable proof bundle, and deterministic archive publication.

### Release engineering

- Added Python 3.12–3.14 qualification, installed-wheel smoke testing, a bounded
  source distribution, version reporting, release manifests, and checksums.
- Made sandboxed commands retain read-only access to both virtual environments
  and externally installed interpreter runtimes without exposing unrelated host
  paths.
- Declared the repository's proprietary evaluation license.

### Scope

This release does not claim the full Cañete–Miranda–Vittone conjecture. The
source-to-coordinate normalization, type-(iii) weighted area and perimeter,
reduced-boundary correspondence, and final global comparison remain open.
The native control-plane architecture in `V2_BUILD_PLAN.md` is a post-1.0
roadmap, not part of this release.
