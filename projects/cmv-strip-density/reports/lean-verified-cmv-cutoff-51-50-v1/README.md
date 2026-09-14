# A Lean-Verified 51/50 Cutoff for Four-Arc Minimizers

> **Package status: VERIFIED AND SEMANTICALLY ACCEPTED**

This folder is intentionally small. Read `MainProof.pdf` first. Use its Lean
reference blocks to locate declarations in `LemmaSupplement.pdf`, then consult
`SemanticAudit.pdf` for the independent semantic review and declaration ledger.

## Five-minute verification

1. Install Git, Python 3, and Lean through Elan.
2. Open a terminal in this folder.
3. Run:

```text
python supporting-materials/verify.py
```

The script verifies every retained SHA-256 digest and runs the pinned Lake build. The
primary declaration is `CMVPublishedCutoff51_50.candidate_not_isWeightedPerimeterMinimizer_from_51_50`. A successful Lean build establishes
kernel acceptance; `SemanticAudit.pdf` separately records the informal/formal review.

## Linux

Install Git and Python with your distribution package manager. Install Elan from
<https://lean-lang.org/lean4/doc/quickstart.html>, restart the shell, and run the
verification command above.

## macOS

Install Git and Python using Xcode Command Line Tools and Homebrew or their official
installers. Install Elan from <https://lean-lang.org/lean4/doc/quickstart.html>, open
a new Terminal window, and run the verification command above.

## Windows

Install Git for Windows, Python 3, and Elan from
<https://lean-lang.org/lean4/doc/quickstart.html>. In PowerShell, change to this
folder and run `py supporting-materials\verify.py`.

## Rebuild strategy

The verifier runs `lake update`, then checks every retained project-local module's
OLean artifact in dependency order. It invokes one local module build at a time to
bound peak memory and removes the entire scratch workspace after verification.
`lean-toolchain`, `lake-manifest.json`, the minimal `lakefile.toml`, and all
project-local source modules are retained. Lake downloads the pinned external
dependencies; offline operation is not required. Exact prompts, model identifiers,
review JSON, build receipts, references, and provenance are under
`supporting-materials/`; rendering intermediates are discarded after PDF creation.

## Status meanings

- **VERIFIED AND SEMANTICALLY ACCEPTED:** Lean and every semantic audit passed.
- **LEAN VERIFIED BUT SEMANTICALLY CONDITIONAL:** compilation passed, but the prose
  describes only a conditional or differently scoped result.
- **SEMANTIC REVIEW FAILED:** at least one mismatch, unclear claim, citation problem,
  or critical review finding remains.
