# Round 192: scale-local two-band pilot

## Status and self-prompt

**Numerical two-band enclosures: PASS. New kernel-checked density coverage: none.**

Self-prompt: abandon serial cusp-majorant sharpening; complete the retained exact-jet evaluator, certify the two complete prescribed bands within 64 subslabs each, and connect the local source obligations to the existing scalar consumer. Do not identify roots across charts or extrapolate the old endpoint box.

The interrupted execution left `model.py`, its generated expressions, and the separately audited height-order theorem. This execution completed and ran the numerical pilot and added the local scalar transport theorem. The retained Bun crash was a controller failure, not a mathematical failure.

| Closed density-increment band, delta = lambda - 1 | Subslabs accepted | Minimum face margin / corresponding displacement radius | Uniform normalized gap upper bound |
|---|---:|---:|---:|
| `[251/40326519148554080, 251/5040814893569260]` = `[delta0, 8*delta0]` | 64/64 | `> 27/100` | `< -18` |
| `[1/1000, 1/500]` | 64/64 | `> 79/1000` | `< -30` |

Here `delta0=(251/20)*(1/126334)^3`. All inequalities in this table were checked using exact rational comparisons of retained enclosures, not rounded displays. Every cell has eight strict opposite-face signs and all 18 positive guard enclosures. The polynomial height-order margin is positive in every cell. The arctangent-remainder evaluation domains are also retained in `metrics.json`.

**Interpretation:** the reusable numerical method passed the prescribed two-band falsification experiment with a specified soundness/replay path below. This is not a Lean slab theorem. Generated-expression identities and interval-to-real replay still need kernel proofs. Rational spotchecks, source regeneration, independent model review, and passing statuses are diagnostics, not substitutes for those proofs. Intermediate factor-eight bands have not been tested.

## Exact data and transformations

`pilot.json` retains every rational scale, closed parameter interval, center, affine predictor slope, displacement radius, and 4-by-4 row preconditioner. There are 64 equal-width density subslabs in each band. The checker requires exact adjacency, includes both endpoints, checks the specified outer endpoints, and rejects more than 64 subslabs.

For each cell:

- `sigma = 1/126334` in the first band and `sigma = 1/25` in the second;
- `s = sigma*tau`, `delta = sigma^3*mu`;
- `(tau,u,v,w) = center + slope*(mu-mu_mid) + d`;
- `-r_i <= d_i <= r_i`;
- physical coordinates are

  `z = pi + s*pi^2 + s^2*u`,

  `a = 5*pi/12 + s*(43*pi^2+1056)/144 + s^2*v`,

  `b = -44+19*pi^2/24 + s*pi*(295*pi^2-14256)/216 + s^2*w`.

These are independent physical correction coordinates, not the old endpoint-box shear coordinates. No endpoint-box assumption is used.

Write `F=completeFoldNumerator`, `C=H2.eval`, `T=completeThirdRowNumerator`, and `G=reducedGapNumeratorBar`, evaluated at these physical coordinates. The generated mathematical quantities are

1. `fold = F/s^2`;
2. `cosine = C/s^2`;
3. `third = regularizedThirdRow/s^2 = T/s^4`;
4. `gap = G/s^2`;
5. `density_cube = densityCubeQuotient`.

The four equations tested on the faces, before the retained invertible row preconditioner, are

`[fold, cosine, third, tau^3*density_cube - mu] = 0`.

In particular, the gap is not an equation and the third row has an overall fourth-order division relative to `T`. Exact cancellations are performed before interval evaluation; the evaluator never subtracts the raw almost-equal source area terms and then divides by a tiny power of `s`.

## Soundness derivation and precise Lean path

### 1. Exact jets, not truncated equations

`Jet(c,tail)` represents `f(s)=sum(k<N,c_k*s^k)+s^N*tail` exactly. Its tail is a retained function, not an omitted error. Multiplication splits the polynomial product into degrees below `N` and the remaining coefficients; its tail is

`high + T_f*P_g + T_g*P_f + s^N*T_f*T_g`.

For inversion, construct the inverse low polynomial `Q`. If `f*Q=1+s^N*U`, then `1/f=Q-s^N*U/f` wherever `f` is nonzero. This is the implemented inverse-tail formula. Truncation moves discarded coefficients into the tail. Dividing by `s^k` requires zero low coefficients and `k<=N`; the retained producer now rejects unsupported division orders.

The source formulas transcribed in `model.py:128-185` correspond to:

- `NearOneNormalizedFlow.lean:32-117`: polynomial coordinates and cleared rows;
- `NearOneAnalyticSystem.lean:73-133,319-355`: half-angle functions, density, and complete numerators;
- `NearOneRegularizedThirdRow.lean:324-412`: exact angle corrections and regularized third row;
- `NearOneFirstCellGap.lean:29-63`: source reduced gap and clearing identity.

The cancellation engine's assertions and SymPy CSE do not discharge the Lean identity obligation. Replay must prove the generic jet operations and the concrete model transcription/reconstruction, then share that proof across cells. `audit_pilot.py` independently computes the *uncancelled source residuals* at eight rational configurations with arbitrary rational third remainders; all 40 rational output comparisons agree. These are explicitly only spotchecks.

### 2. Arctangent remainder and derivatives

Define

`R_k(x)=(-1)^k * integral(t=0..1, t^(2k)/(1+x^2*t^2))`.

The finite geometric identity gives

`R_k(x)=sum(j<N, (-1)^(k+j)*x^(2j)/(2*(k+j)+1)) + x^(2N)*R_(k+N)(x)`.

For every real `x`,

`|R_m(x)| <= 1/(2*m+1)`,

`|R_m'(x)| <= 2*|x|/(2*m+3)`.

The derivative formula follows by differentiation under the integral on the compact integration interval; its denominator is at least one. Thus on `|x|<=B`, the value-tail error is

`B^(2N)/(2*(k+N)+1)`,

and the derivative-tail error is

`2*N*B^(2N-1)/(2*(k+N)+1) + 2*B^(2N+1)/(2*(k+N)+3)`.

The checker uses `N=20`, includes both derivative-tail terms, and requires `B<=1/2`. The actual generated remainder calls have `k=3`. Their arguments are `s`, `W`, `(Y-s)/(1+s*Y)`, and `(V-W)/(1+W*V)`. All four domain margins are recoverable from each cell's guard enclosures; `metrics.json` retains conservative per-cell lower margins to `1/2`.

Round 193 kernel-checks the generic `R_k` recurrence, exact finite expansion, differentiation under the compact integral, global value and derivative bounds, and both uniform tail bounds in `NearOneAtanRemainder.lean`. The retained `k=3`, `N=20` specializations are exactly `B^40/47` and `40*B^39/47 + 2*B^41/49`. `atanRemainder_one` identifies `R_1` with the corrected source remainder. This discharges the reusable analytic remainder and derivative-tail formulas, but not the four generated argument enclosures, their `B<=1/2` guards, or the generated DAG/mean-value replay.

### 3. Arithmetic and mean-value face certificates

All accepted arithmetic is integer/rational. Interval endpoints are multiples of `2^-160`. Addition and negation are exact on this grid. Multiplication uses the minimum/maximum of all four exact endpoint products, rounded down/up. Reciprocal rejects zero-containing denominators and rounds its two rational endpoints outward. Powers are integer-only. Pi comes from the retained exact alternating-series enclosure for `16*atan(1/5)-4*atan(1/239)` in `face_bridge_pilot/check_bridge.py:131-143`; 36 terms are used for each arctangent.

The five AD variables are `theta=mu-mu_mid` and the four displacements. All predictor slopes and the explicit density derivative `-1` are differentiated. For preconditioned row `h_i`, with derivative intervals `J_ij` on the full box, the lower/upper face enclosure is

`h_i(0) + J_i0*[-theta_radius,theta_radius] + sum(j != i,J_ij*[-r_j,r_j]) +/- r_i*J_ii`.

This follows by integrating the derivative along the straight segment from the center to the face point. The box is convex. Pi is held fixed at its true value in its certified interval; independent interval occurrences only enlarge the enclosure. The implementation reuses the centered mean-value pattern of `face_bridge_pilot/check_bridge.py:320-337`.

Round 194 adds `NearOneLocalPredictor.lean`. Its generic
`affineEnclosure_sound` and `scaledEnclosure_sound` declarations connect exact
rational predictor intervals to their real affine coordinates. Instantiating
the actual first-cell `mu` interval, `tau` center/slope, displacement radius,
and scale proves the retained 160-bit `s_pos` and `s_lt_one` enclosures and
therefore `0 < s < 1` throughout the seam-adjoining subslab. This replays two of
that cell's 18 guards; it does not replay a generated nonlinear expression,
face sign, gap bound, or root.

Rounds 195 through 198 extend the same module through the nonlinear coordinate
guards. The saved affine `u` predictor, `z = pi + pi^2*s + u*s^2`, and
`Y = s*(1+s*z)` replay the retained `y_pos` and `y_lt_one` endpoints. The saved
affine `v` predictor, the corrected physical
`a = 5*pi/12 + s*(43*pi^2+1056)/144 + v*s^2`, and `W = s*(2+s*a)` replay the
retained `w_pos` and `w_lt_one` endpoints. Finally, the saved affine `w`
predictor, corrected physical
`b = -44+19*pi^2/24 + s*pi*(295*pi^2-14256)/216 + w*s^2`,
`e = 6*a-2*z+s*b`, and `V = s*(2+s*a+s*e)` replay `v_pos` and `v_lt_one`.
Dependency-aware interval evaluation of the exact identities
`Y-s = s^2*z` and `V-W = s^2*e` replays `y_gt_s` and `v_gt_w`; subtracting the
independently rounded `Y,s,V,W` intervals would lose both strict signs. Thus ten
of the first cell's 18 guards are kernel-replayed, proving
`0 < s < Y < 1` and `0 < W < V < 1`; no face sign, gap bound, or root is
obtained.

Round 199 replays the next three generated guards directly from those checked
coordinate intervals: `density_den = 1-Y^2`, `angle_den_four = 1+s*Y`, and
`angle_den_three = 1+W*V`. Exact interval multiplication followed by outward
containment recovers the retained 160-bit endpoints, whose lower endpoints are
strictly positive. Thirteen of the first cell's 18 guards are now
kernel-replayed; density coverage remains unchanged.

Round 200 replays the two arctangent-addition guards
`atan_guard_four = 1-s*q4` and `atan_guard_three = 1-W*q3`. Their exact interval
DAGs reconstruct `s^3*z/(1+s*Y)` and `s^3*R*e/(1+W*V)` from the affine
predictors, use the checked positive denominators for exact rational division,
and fit inside the retained outward-rounded 160-bit endpoints. Both retained
lower endpoints are strictly positive. Fifteen of the first cell's 18 guards
are now kernel-replayed; density coverage remains unchanged.

Round 201 replays the polynomial height guard
`height_order = (1-s^2)*R^2-2`. A direct natural interval loses the opposing
dependence of `1-s^2` and `R^2`; instead, reusable lemmas prove the margin
monotone in the positive physical `a` coordinate and in `s` on
`0 <= s <= 1/100`. Exact rational corner evaluation from the checked affine
`s` and physical `a` predictors fits inside the retained 160-bit enclosure.
Its lower endpoint is strictly positive, and
`NearOneLocalHeightOrder.height_order_iff` transports that margin to the actual
strict source height order. Sixteen of the first cell's 18 guards are now
kernel-replayed; density coverage remains unchanged.

Round 202 replays `A_pos = 1+s*z`. The forty-decimal `pi` enclosure was too
wide to fit the pilot's rounded 160-bit `A_pos` endpoints, so
`NearOneLocalInterval.piInterval` is now the exact dyadic interval used by the
checker; the same Machin identity and 36-term analytic remainder prove it.
Natural interval evaluation of `z = pi + pi^2*s + u*s^2` and `A = 1+s*z`
then fits inside the retained enclosure, whose lower endpoint is strictly
positive. Seventeen of the first cell's 18 guards are now kernel-replayed;
density coverage remains unchanged.

Every evaluated denominator must avoid zero over the full box. The now-replayed source guards retain positive intervals for `1-Y^2`, `1+s*Y`, and `1+W*V`; the reduced-gap denominator is still pending. All other nonconstant clearing factors are positive `1+x^2` factors. Compact integral remainders and these denominator guards give the required local smoothness. Exact rational Gaussian elimination rejects a singular row preconditioner; no inverse-Jacobian uniqueness claim is made.

**Pending Lean work:** interval operation/AD/mean-value soundness for the generated DAG, the remaining first-cell guard expression (`gap_den`), and replay of the saved face and gap endpoints. Once available, the eight signs instantiate `BoxPoincareMiranda.poincareMiranda` (`BoxPoincareMiranda.lean:166-174`) for `Fin 4`, separately at each fixed `mu`.

### 4. Source guards, density, height order, and strict improvement

Every cell records positive bounds for

`s, 1-s, Y, 1-Y, W, 1-W, V, 1-V, Y-s, V-W, 1-Y^2, 1+s*Y, 1+W*V, 1-s*q4, 1-W*q3, (1-s^2)*R^2-2, A, gapDenominator`.

These give the actual principal-chart and arctangent-addition guards, rather than extrapolated cusp-box bounds. Density is prescribed using `NearOneAnalyticSystem.density_sub_one_eq_cube_mul` (`NearOneAnalyticSystem.lean:104-112`). The positive slab parameter gives `lambda>1`.

The zero-set reconstruction uses these existing declarations:

- `NearOneAnalyticSystem.sourceFoldResidual_eq_zero_iff_complete` (`:570-584`);
- `NearOneAnalyticSystem.sourceCosineResidual_eq_zero_iff_H2` (`:588-607`);
- `NearOneRegularizedThirdRow.sq_mul_regularizedThirdRow_eq_complete` (`:790-811`);
- `NearOneRegularizedThirdRow.sourceAreaResidual_eq_zero_iff_regularizedThirdRow` (`:833-864`).

At positive `s`, negative generated gap implies `G<0`. The exact identity `gapDenominator*sourceReducedGap=s^2*G` is `reducedGap_clearing_identity` (`NearOneFirstCellGap.lean:60-70`), so the positive denominator transports the sign. `reducedFoldGap_eq_sourceReducedGap` (`:221-229`) identifies the scalar gap.

The new checked declaration `NearOneLocalHeightOrder.height_order_iff` (`NearOneLocalHeightOrder.lean:12-29`) proves that positive polynomial height-order margin is exactly `h3<h4`. The new checked consumer

`NearOneLocalSource.stationaryEqualAreaPair_strictImprovement`

accepts the explicit local source equations, prescribed density, principal coordinates, polynomial height order, and negative `G`, and returns exactly

`exists pair : StationaryEqualAreaPair lambda, typeThreeFold lambda pair.h3 < 0 and P3(lambda,pair.h3) < P4(lambda,pair.h4)`.

It has no endpoint-box assumption and no `s<1/100` assumption. Its proof reuses `sourceResiduals_stationaryEqualAreaPair`, `typeThreeFold_neg_of_equalArea_of_lt`, and `stationaryEqualArea_typeThree_improves_iff`. Its conclusion is accepted unchanged by `CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_stationaryEqualAreaPair` (`CMVSuffixModel.lean:223-239`). This transport theorem is conditional on the genuine equations and inequalities, and is not reported as a completed slab.

For the adjoining cell specifically,
`NearOneLocalPredictor.first_height_order_positive` proves the polynomial
margin from the saved enclosure, while
`NearOneLocalPredictor.first_strict_height_order` performs the checked
`height_order_iff` transport. These declarations remain conditional on a point
inside the saved affine predictor box; the root construction is still pending.

## Verification and reproduction

From the project root, in bounded foreground processes:

```sh
python3 proof/scale_local_atlas/generate_pilot.py --output proof/scale_local_atlas/pilot.json --receipt proof/scale_local_atlas/producer-receipt.json
python3 proof/scale_local_atlas/check_atlas.py proof/scale_local_atlas/pilot.json --output proof/scale_local_atlas/enclosures.json
python3 proof/scale_local_atlas/audit_pilot.py --output proof/scale_local_atlas/diagnostics.json
```

From `proof/`, with the inherited elan executable on PATH:

```sh
lake build NearOneLocalAtlas
lake env lean _Assumptions.lean
```

Retained receipts:

- `generation-command.json`: producer completed in about 53.1 seconds; both bands 64/64. The untrusted predictor uses 65 decimal digits, 64 remainder terms, 100-bit rationalized centers/slopes, endpoint predictor defects for initial radii, and at most 12 face-directed radius doublings. Only exact uniform enclosures can accept a cell.
- `replay-command.json`: separate saved-input replay completed in about 6.8 seconds, both bands 64/64; output says `NOT_KERNEL_REPLAYED`.
- `enclosures.json`: every face interval, guard interval, gap interval, and center residual, as exact rational strings.
- `metrics.json`: exact per-band minima and conservative remainder-domain margins, deterministically regenerated by the audit command.
- `diagnostics.json`, `audit-command.json`: reproduced generated source; 118 arithmetic enclosures, 24 independently summed remainder/derivative enclosures, 40 source rational spotchecks, and six invalid-operation/missing-guard rejections passed. These are diagnostics, not a universal proof.
- `independent-review.json`: independent reasoning audit. It found unsupported exponent/division contracts and a possible silent missing-guard truncation. Those paths now reject; the passing pilot was replayed after the corrections. Its warnings about absent kernel replay remain valid.
- `lean-build.json`: targeted library build passed. Existing dependency warnings were not suppressed.
- `allowed-axioms.json`: `_Assumptions.lean` completed; all reported axioms are among `propext`, `Classical.choice`, and `Quot.sound`, including the audited local declarations. No additional axioms were found.
- `NearOneAtanRemainder.receipt.json`: `NearOneLocalAtlas` including the generic remainder module built successfully; the seven audited public declarations use only `propext`, `Classical.choice`, and `Quot.sound`. This adds no density coverage.
- `NearOneLocalPredictor.receipt.json`: `NearOneLocalAtlas` including the exact
  affine replay and local interval modules built successfully. The shared
  outward-rounded multiplication lemma, Machin-certified exact 160-bit dyadic
  `pi` interval, generic evaluators, the seventeen retained guard enclosures,
  and their principal-chart, tangent-order, arctangent-guard, height-order, and
  `A`-positivity consequences use only `propext`, `Classical.choice`, and
  `Quot.sound`. This replays `s_pos`, `s_lt_one`, `y_pos`, `y_lt_one`, `w_pos`,
  `w_lt_one`, `v_pos`, `v_lt_one`, `y_gt_s`, `v_gt_w`, `density_den`,
  `angle_den_four`, `angle_den_three`, `atan_guard_four`, `atan_guard_three`,
  `height_order`, and `A_pos`, but adds no density coverage.

## Round 210 target-manifest preflight and shared semantics

The exact checker now accepts a separate thirteen-band target schema. It derives
the required bands
`[8^j*delta0, min(8^(j+1)*delta0, 1/1000)]` and scales
`2^j/126334` for `j = 0,...,12` internally, requires every saved cell to use
the prescribed scale, checks exact endpoints and adjacency, and retains the
64-cell-per-band cap. The original two-band pilot schema remains accepted
separately.

Generation and independent saved-input replay accepted all 832 target cells:
every cell passed the eight strict mean-value faces, eighteen positive guards,
negative normalized gap, exact invertible-preconditioner check, and remainder
domain check. The weakest normalized face is row 3 of band 10, cell 11, on
`35391/1280 <= mu <= 9287/320`; its exact positive margin is retained in
`target-metrics.json`. `target-manifest.json`, `target-enclosures.json`,
`target-producer-receipt.json`, and `target-diagnostics.json` retain the inputs,
enclosures, producer settings, and diagnostics. This is numerical preflight,
not kernel replay and not new density coverage.

`NearOneLocalTranscription` kernel-checks the shared five-coordinate enclosure
as five telescoped applications of the existing scalar mean-value theorem. It
also proves the exact `atanQuotient` expansion through the retained analytic
`R3` tail, its actual derivative including the `R3` derivative, and the genuine
source normalization
`regularizedThirdRow/s^2 = completeThirdRowNumerator/s^4` under nonzero scale
and the three source denominator guards. The targeted build and axiom audit
passed; these declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. The command, resource, hash, and exact-margin receipt is
`target-preflight-receipt.json`.

## Round 213: execution-209 semantic gate falsified

The complete emitted third-expression/source identity and both pilot cells'
uniform value plus five actual slice-derivative enclosures are absent.
`NearOneLocalGeneratedThird.lean` ends at the algebraic-only
`algebraicThirdDivided_value`; this is not the required complete analytic row.
Its bounded direct source check failed with Lean's `memory_exception` at a
9000 MB limit: exit 134, 17.36 seconds elapsed, 17.09 CPU seconds, and
9218152 KiB peak RSS. The recovery cgroup recorded no OOM kill. This does not
establish the cause of earlier empty-output conductor failures.

`NearOneLocalJet.lean` passed a direct source check in 6.36 seconds.
The retained focused audit covers six jet declarations and three shared
transcription declarations; all use only `propext`, `Classical.choice`, and
`Quot.sound`. Neither this partial evidence nor the numerical preflight passes
the two-cell gate. No complete cell was kernel-checked.

Strategy `strategy-00037` is terminated on its original execution-209 deadline,
not restarted under another name. The independent compatibility re-gate remains
unauthorized at its retained 20% estimate: the canonical two-sided relaxed-cost
argument and coverage of the unrestricted `AdmissibleCompetitor.general`
constructor are still missing. Smoothing selected circular assemblies alone
would not discharge `CompatibleWithModel.model_covered`.

The durable receipt is
`autorun-runs/20260902T064759Z-62a799/rounds/round-00213/semantic-gate-recovery.json`
relative to the project root. It retains every recovery command, log, resource
measurement, exact cell locator, partial axiom declaration, and missing gate
obligation. Recovery checks consumed 38.61 measured CPU seconds including
failures. The five earlier failed invocations total 1620.185 elapsed seconds,
not measured CPU time; cumulative campaign CPU compliance remains unestablished.
The prior interrupted `semantic-gate-receipt.json` is preserved separately.

The public kernel-checked prefix still ends at
`1+(251/20)*(1/126334)^3`. No target-manifest cell has been composed into it.
Universal source classification, actual reduced-boundary compatibility, and
the entire remaining modeled interval are still unresolved. A successful atlas
would not by itself complete those source obligations.
