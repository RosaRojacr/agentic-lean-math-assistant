Delivered standalone branch-explicit scalar artifacts under:

`agents/analytic/scalar_formula_producer/`

### Artifacts

- `scalar_spec.md`
  - Defines \(A_3,P_3,A_4,P_4\).
  - Principal `asin`/`acos` branches and exact domains.
  - Circle centers, endpoints, counterclockwise arc orientations, and density weights.
  - Type-(iii) major/semicircle/minor transition at \(h=\tfrac12\).
  - Signed circular-segment terms and bottom-segment sign.
  - Regular domain \(0<h<1\); \(h=1\) closure-only; \(h\to0^+\) separate degeneration.
  - Exact endpoint and scaled-limit table.
  - CMV locators: Lemma 3.8, equations (24)–(27), printed pp. 15–19.

- `formula_checker.py`
  - Independent coordinate reconstruction using circle centers and Green integrals.
  - Exact branch-polynomial and scaled coefficient-map checks.
  - Deterministic 80-digit numerical checks on 20 \((\lambda,h)\) pairs.
  - Endpoint and \(h=\tfrac12\) checks.
  - Accepts independently modified fixtures with `--fixtures PATH`.

- `mutation_fixtures.json`
  - Seven formula-sign mutations.
  - Four inverse-trigonometric branch mutations.

- `checker_receipt.json`
  - Clean unmutated baseline and mutation results.

- `artifact_manifest.json`
  - Reproduction command, source identity, hashes, results, and explicit non-claims.

### Critical formula normalization

The source terms are

\[
\lambda\alpha-\sin\alpha\cos\beta,
\]

not

\[
\lambda(\alpha-\sin\alpha\cos\beta).
\]

This distinction is preserved in both area formulas and covered by mutation fixtures.

### Verification

Command:

```text
cd agents/analytic/scalar_formula_producer
python3 formula_checker.py --output checker_receipt.json
```

Result: exit code 0, `PASS`.

- Type (iii): 40 checks, maximum residual `1.0795211e-78`.
- Type (iv): 40 checks, maximum residual `2.1590421e-78`.
- Closure and \(h=\tfrac12\) transition: maximum residual `3.3735033e-80`.
- Scaled \(h\to0^+\) probe at \(h=10^{-20}\): maximum residual `3.968627e-20`.
- Mutations rejected: `11/11`.
- Symbolic branch and coefficient-map checks: all true.

### Hashes

```text
d2ff4165c6b391fdead2639163a1b07c1c0c6d911925b50b8812cb56ace2765f  scalar_spec.md
3b7abebce26b65041bf248e013c9a3f6ee13a4f0b60a82669a164bcd0b75f093  formula_checker.py
9fc9a83c8fdaf6fe2a91955436c23a21172dbb0f558b37eb347b42371aea7ce3  mutation_fixtures.json
8fbc66b6f0fa4af2eb27f866b2735b9abd659aa3f3afbb9d7d181793b9a77d29  checker_receipt.json
a24d943b102d3150b9e1673c730f6a6f65e2335f727bffe1e9a0136b4221df36  artifact_manifest.json
```

Source PDF SHA-256:

```text
0ee9b4787aa3c09f9a4ed05fb66563a820cd13596af401b76e7900e597711230
```

### Encountered failures

- `sympy` was unavailable (`ModuleNotFoundError`); the checker instead uses standard-library exact coefficient maps and `mpmath` 1.4.1.
- The first checker execution exposed the parenthesization error above, exiting 1. Correcting it to the exact CMV p. 19 expression reduced baseline residuals to the final values reported above.

### Explicit limitations

The checker does **not** certify profile topology, fold structure, equal-area roots, \(\Gamma\)’s sign, source normalization, the source-to-model geometric bridge, minimization, or CMV Conjecture 3.12.
