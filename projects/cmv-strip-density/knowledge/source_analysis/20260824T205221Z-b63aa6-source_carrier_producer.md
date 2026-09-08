Delivered the finite source/carrier contract.

### Artifacts

- `agents/source_analysis/source_carrier_producer/source_carrier.json`  
  SHA-256: `5b72b27863f76bce1f102a10c49e2e2b8189a447c88dc323e511bc5b2dcf51a8`
- `agents/source_analysis/source_carrier_producer/coordinate_formula_receipt.json`  
  SHA-256: `8fbc66b6f0fa4af2eb27f866b2735b9abd659aa3f3afbb9d7d181793b9a77d29`
- `agents/source_analysis/source_carrier_producer/artifact_manifest.json`  
  SHA-256: `f30f0e263d04fce6d5b165228af47b4551793a214c1d74205c3ad6c2ab1ea1fa`

`source_carrier.json` contains:

- 18 source rows, each with:
  - precise printed-page and statement locator;
  - source hypotheses;
  - angle/orientation convention;
  - parameter range;
  - equality or degeneration cases;
  - Lean predicate or missing lemma;
  - carrier construction;
  - complete-frontier/reduced-boundary obligation;
  - minimizer-quantifier transfer.
- 12 bridge-ledger entries.
- Explicit regular type-(iv) carrier.
- Explicit type-(iii) major, semicircular, and minor carriers.
- Source-to-model, competitor, boundary-semantics, and quantifier-transfer contracts.
- Domain discrepancies and a reproducible next-stage order.

### Source conclusions

[Published] Audited locators include:

- weighted volume and relaxed/reduced-boundary perimeter: printed pp. 2–3;
- Proposition 2.13 and equation (13): pp. 9–10;
- Section 3.2, Propositions 3.5–3.6: pp. 13–14;
- pre-Lemma regularity reduction, Lemma 3.8, Figure 4, equations (24)–(25), Proposition 3.9: pp. 15–18;
- Conjecture 3.12 and equations (26)–(27): p. 19;
- Remark 3.14: p. 21;
- Theorem 3.16: pp. 22–24;
- Remark 3.17: p. 24.

[Derived from published domain statements] Regular type-(iii) and type-(iv) profiles satisfy

\[
\lambda>1,\qquad 0<h<1.
\]

Equation (27) permits \(h=1\) only at the displayed-formula level. Remark 3.14 and the radius argument on p. 23 require \(R>1\), hence strict \(h<1\), for regular profiles. The current `FourArcCandidate` is deliberately broader: it permits and constructs \(h=1\). The table therefore marks \(h=1\) as closure-only and does not identify `SatisfiesCMVTypeIVHypotheses` with exact source regularity.

### Carrier normalization

For type (iv), the table fixes

\[
R=1/h,\quad b_4=\arccos h,\quad a_4=\arccos(h/\lambda),
\]

with explicit centers, four interface endpoints, closed-set unions, and counterclockwise arc intervals. All four regular arcs are minor.

For type (iii), it fixes

\[
R=1/h,\quad
b_3=\pi-2\arcsin\sqrt h,\quad
a_3=\arccos((2h-1)/\lambda),
\]

with the upper cap, two strip-side disks, central rectangle, and bottom segment given in coordinates. The finite branch partition is:

- \(0<h<\tfrac12\): major upper arc;
- \(h=\tfrac12\): semicircle, zero-length bottom segment, radius-two disk centered on \(y=1\);
- \(\tfrac12<h<1\): minor upper arc.

The word “descending” remains conditional on the later exact fold theorem: CMV does not prove a global fold or identify the decreasing branch for every \(\lambda\).

### Exact open bridge obligations

[Unresolved]

1. Normalize every regular source type-(iv) minimizer, up to a density-preserving isometry, to the explicit \(E_4\) carrier with \(0<h<1\).
2. Implement a genuine `TypeThreeAssembly` and `AdmissibleCompetitor` for all three \(E_3\) branches.
3. Prove complete-frontier versus CMV reduced-boundary equality for \(E_3\), \(E_4\), and replacement carriers; prove the needed source-perimeter inequality for arbitrary `.general` model competitors.
4. Transfer source minimality over all finite-perimeter equal-area sets to `FourArcCandidate.IsWeightedPerimeterMinimizer`.

Formula agreement alone discharges none of these obligations.

### Verification

```text
sha256sum references/Canete2010.pdf
```

Result:

```text
0ee9b4787aa3c09f9a4ed05fb66563a820cd13596af401b76e7900e597711230
```

`pdfinfo references/Canete2010.pdf` reported 40 pages.

Coordinate reconstruction:

```text
cd agents/analytic/scalar_formula_producer
python3 formula_checker.py \
  --fixtures mutation_fixtures.json \
  --output ../../source_analysis/source_carrier_producer/coordinate_formula_receipt.json
```

Result: exit 0, 80-digit precision, 40 type-(iii) checks, 40 type-(iv) checks, and all 11 formula-sign/branch mutations rejected.

Table-schema and required-field checks returned `true`.

Current Lean model:

```text
cd proof
/home/rosa/.elan/bin/lake build
```

Result: exit 0, `Build completed successfully (8707 jobs)`. Existing linter warnings remained; no build failure.

One tool recovery link for the initial PDF extraction was unavailable; direct ranged PDF reads succeeded, and the tool inconsistency was reported through `xd://report_issue`.

### Strongest justified conclusion

The finite source/carrier ledger is complete, but its geometric and perimeter-semantics lemmas remain unimplemented. No audited source row proves small-\(\lambda\) type-(iv) exclusion or supplies a counterexample. This stage does not establish the immutable `CMVConjecture.cmv_conjecture_3_12` theorem.
