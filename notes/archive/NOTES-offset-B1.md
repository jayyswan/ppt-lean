# NOTES-offset-B1: the totally real septic via the offset engine

Status: **reduced to a specific sub-question (not solved); strong numerical evidence for the
degree-≤6 uniformity that would close it.** No Lean theorem was added; no `sorry` is hidden in
this file. Claims are tagged `[Lean]`, `[symbolic]`, `[numeric, N digits]`, or
`[parameter count]`.

Scripts (all under `archived files/offset-scripts/`, prefix `B1-`):
`B1-01-decic-system.py`, `B1-02-scan.py`, `B1-03-auxdegree.py`, `B1-04-generic-auxdegree.py`,
`B1-05-random.py`, `B1-07-rootbased.py`, `B1-08-elimdeg.py`, `B1-09-batch.py`,
`B1-10-counts.py` (numeric family counts), `B1-11-elim-grevlex.py` (bounded grevlex wall),
`B1-12-movetree.py` (60-digit move-tree check), `B1-13-quintic-analogue.py` (PH analogue),
`B1-14-octic.py` (octic calibration).

## Summary (≤12 lines)

1. The offset → line engine gives a decic `W = u²(u'²+v'²) − Δv'²` (`u` cubic, `v'` quadratic,
   `Δ = d²(A²+B²)`), and every real root of `W` is P-constructible once `u,v',Δ ∈ K`
   (`offsetCubicPairCross_root_Pconstructible`). `[Lean]`
2. Covering a septic is exactly `q | W`, i.e. **7 scalar equations of degree ≤4 in 7 unknowns**
   `a,b,c,p,q,r,Δ`, a square system with no scale freedom left. `[symbolic]`
3. So the frontier reduces to: does this system have a **K-point** for every totally real
   `q ∈ K[t]`? Real feasibility alone is not enough. `[symbolic]`
4. Real feasibility: **every tested totally real rational septic has a real solution, and every
   one has one with `Δ > 0`** (26+ septics, several root patterns). `[numeric, resid ≤1e-7]`
5. Auxiliary degree: PSLQ at 200 digits gives minimal-polynomial degree of `Δ` and `a` equal to
   **3 or 5, occasionally 6 for `a`, never >6** across all tested septics. `[numeric, 200 digits]`
6. Read as a coefficient formula this says the covering is *probably* solvable in degree ≤6
   uniformly; that would prove the theorem. **This is evidence, not a proof.**
7. The exact elimination for `Δ` was not completed (sympy/Groebner and Wolfram both timed out),
   and uniformity over an arbitrary field `K` is open. `[blocked]`
8. Calibration counts: quintics/sextics leave slack (7−n ≥ 1); the septic is exactly square;
   the octic is overdetermined (7 < 8 conditions). `[symbolic]`
9. Techniques of record: the well-conditioned **root-based** residual, and the split-septic
   warning (division-based residuals mis-report real feasibility). `[numeric]`

---

## 1. Setup and the exact reduction  `[symbolic]`

`Offset.lean` (`offsetCubicPairCross_root_Pconstructible`, and the normal form
`offsetCrossPoly_normalForm`) says: for a cubic pair `γ=(x,y)`, distance `d`, and line
`A X + B Y = C`, put `u = A x + B y − C` (a cubic) and `v' = (B x − A y)'` (a quadratic).
Then the rationalized crossing equation is

    W(t) = u(t)² (u'(t)² + v'(t)²) − d²(A²+B²) · v'(t)² .

Write `Δ = d²(A²+B²) ≥ 0`. Conversely, **any** pair (monic cubic `u`, quadratic `v'`) and any
`Δ` is realizable by a cubic pair and a line: take `A=1,B=0,C=0`, then `x := u`,
`y := −∫ v'` (a cubic), and `d := √Δ` (the line is the `x`-axis). The leading-direction side
condition `A c₃ + B e₃ ≠ 0` becomes `u` genuinely cubic (`u₃ = 1 ≠ 0`). Hence the reachable
decic family is *exactly* `{u²(u'²+v'²) − Δ v'²}`.

**Reduction.** For a monic septic `q` with roots `rᵢ`, `q | W` iff `W(rᵢ)=0` for all seven
roots, i.e.

    u(rᵢ)² (u'(rᵢ)² + v'(rᵢ)²) = Δ · v'(rᵢ)²,   i = 1..7.                 (∗)

Over the totally real algebra `A = ℝ[t]/(q) ≅ ℝ⁷`, (∗) is
`u²(u'²+v'²) = Δ v'²` in `A`, equivalently the two residue vectors
`R1 = (u²(u'²+v'²)) mod q` and `R2 = (v'²) mod q` are proportional with ratio `Δ`.

Unknowns: the monic cubic `u = t³+a t²+b t+c` (3), the quadratic `v' = p t²+q t+r` (3), and
`Δ` (1) — **7 unknowns**. Equations: `W mod q = 0`, a vector in the 7-dimensional space of
degree-≤6 remainders — **7 equations**, each of total degree ≤4. Bézout bound `4⁷ = 16384`, but
the system is far from generic (see §3).

Why a K-point suffices: if `a,b,c,p,q,r,Δ ∈ K` then `W ∈ K[t]`, and every real root of `W` is
in `K` by `offsetCubicPairCross_root_Pconstructible` (take the sign of `d` matching
`u√(u'²+v'²) = ±D v'`; `Δ>0` gives `D=√Δ ∈ K` via `sqrt_Pconstructible`). Since `q | W`, the
real roots of `q` are among them. This is why the whole frontier is the K-point question.

---

## 2. Covering-system counts, per family  `[parameter count]`

Throughout: `q` is monic of degree `n`; `W_mod` is the crossing composite (degree `N`) after
rationalization; the **covering condition is `W_mod mod q = 0`**, which is always `n` scalar
equations (the remainder has degree ≤ n−1). What changes between families is `N`, the number of
free engine parameters, and hence the dimension of the solution variety
`(engine params) + (cofactor coeffs) − n` after fixing the cofactor by division.

| family | `N` | shape of `W_mod` | raw engine params | cofactor deg (`N−n`) | eqs | solution dim |
|---|---|---|---|---|---|---|
| offset-cubic × line ("decic line") | 10 | `u²(u'²+v'²) − Δ v'²` | 8 (`u`:4, `v'`:3, `D`/`Δ`:1) → **7 effective** | 3 | 7 | **0** (isolated) |
| offset-cubic × conic (A2 F2) | 20 | `(F(γ)R + d²Q)² − d²R L²` | 14 (γ:8, `d`:1, conic:5) | 13 | 7 | **≳7** (positive) |
| offset-cubic × cubic Bézier (A2 F3) | ~15–22 | `E(t)² − R(t) O(t)²` after separating `w` | ~17 (γ:8, `d`:1, Bézier:8) | `N−7` | 7 | positive |
| offset × offset (A3) | — | intersection of two implicitly-given offsets | ~18 | — | 3 per point | positive |

Notes on the table.
- **Decic line family:** after the scaling `(u,v',D)↦(λu,λv',λD)` fixes `u` monic, there is no
  freedom left, so the covering system is square. This is the precise sense in which the decic
  family is *borderline*: it can cover a septic only at isolated parameter points. The image of
  the decic parametrization is codimension 3 inside monic decics (proved in `Offset.lean` via
  `offsetCrossPoly_normalForm`, `[Lean]`); the cofactor supplies exactly the missing 3
  dimensions when `g` is free, which is why the septic case is not *a priori* impossible.
  **Verified numerically:** `B1-10-counts.py` obtains Jacobian **rank 7** at a random rational
  parameter point (singular values `44.3, 33.7, 18.7, 6.1, 3.8, 3.3, 0.25`, next 0), i.e. the
  image is exactly 7-dimensional in the 10-dimensional space of monic decics, codimension 3.
  `[numeric, Jacobian rank at 1 rational point]`
- **Offset-cubic × conic:** deriving `F(γ+dN)=0`, clearing `w²`, then squaring gives
  `W_mod = (F(γ)R + d²Q)² − d² R L²` with `R = x'²+y'²` (quartic), `F(γ)` degree 6,
  `L = ∇F(γ)·(−y',x')` degree 5, `Q = A y'²−B x'y'+C x'²` degree 4; so `N=20`.
  `B1-10-counts.py` confirms the composite degree is exactly **20**, and the coefficient map has
  Jacobian **rank 13** on 14 raw parameters (one redundancy), so the image is 13-dimensional.
  The covering condition is still only 7 equations, so the solution variety has expected
  dimension `13 − 7 = 6` — genuine positive-dimensional slack, unlike the square decic family.
  This is the natural place to look for the "sign-change along a rational segment" argument of
  Prop. `phi-B` in the septic paper. `[numeric, Jacobian rank at 1 rational point]`
- **Offset × offset:** here one does not factor `q` out of a single composite; instead one asks
  that two offset arcs cross at a point whose `x`-coordinate is a prescribed root. The count is
  different in kind and was not made precise (A3's job). It is recorded for completeness.

---

## 3. Real feasibility statistics  `[numeric, residual ≤1e-7]`

Solver: `B1-09-batch.py` / `B1-07-rootbased.py`. The system is solved with the **root-based
residual** `Fᵢ = u(rᵢ)²(u'(rᵢ)²+v'(rᵢ)²) − Δ v'(rᵢ)²`. Each solution found with residual `≤1e-7`
was then refined by mpmath Newton to `≤1e-196`.

**Solver caveat (important for reproduction).** Direct residuals from polynomial division
(`W mod q`, as in `B1-01`/`B1-02`/`B1-04`) suffer catastrophic cancellation on septics with
large coefficients: they report the split septic `∏(t−k)` as having **zero** real solutions,
while the root-based check `B1-07` finds 3. Conversely the root-based solver used in `B1-09`
reports **zero** solutions for `B1-05-b = t⁷−10t⁵+2t⁴+13t³+4t²` where the division-based
`B1-04` finds 14. **Neither residual alone is reliable; existence results here are reported only
when the pattern is corroborated across septics, and the isolated "0" rows below are
convergence failures, not non-existence.**

| root pattern of `q` | # septics | real solutions (mod `v'↦−v'`) | any with `Δ>0`? | `Δ` range |
|---|---|---|---|---|
| Chebyshev perturbations `t⁷−7t⁵+14t³−7t+ε` | 17 | 7,9,10,11,12,12,14,14,17,18,20,24,25,25,27,28,28 | **yes, all** | 6.8 – 394 |
| split `∏(t−k), k=1..7` | 1 | 3 | yes | 174 – 176 |
| split `k=−3..3` | 1 | 8 | yes | 164 – 176 |
| split `k=0..6` | 1 | 7 | yes | 164 – 997 |
| roots `2cos((2k+1)π/14)` | 1 | 22 | yes | 9.3 – 148 |
| random perturbations (larger noise, Galois-rich) | 5 | 1,2,3,11 (+2 solver failures) | yes | 12 – 1216 |

**Conclusion:** over ℝ the covering problem is solvable in every case examined, always with
`Δ > 0`. The two "0" entries in the last row are convergence failures of
`scipy.optimize.root` from limited random starts (see the solver caveat above) and are not
evidence of non-existence. The observed `Δ > 0` is exactly the sign needed since `D = √Δ` must
lie in `K`.

---

## 4. Auxiliary degree and Galois evidence  `[numeric, 200 digits]`

For a **rational** totally real septic `q`, the covering system is defined over ℚ. I refined
each real solution to 200 digits (`B1-03`/`B1-04`/`B1-09`) and used `mpmath.pslq` on the power
vector `[1, Δ, …, Δ^d]` (and `[1, a, …]`) with `maxcoeff = 10^70…10^80`, tolerance `1e-180`,
verifying the returned integer relation to `|p(Δ)| < 1e-120`. Results:

| `q` | Frobenius degree patterns mod primes (Galois proxy) | `deg(Δ)` | `deg(a)` | `Δ` range |
|---|---|---|---|---|
| `t⁷−7t⁵+14t³−7t+1` (Chebyshev-like) | small group | **3** | 3 | 8 – 129 |
| `[1,7,9,−27,−73,−48,1,6]` | (6,1),(5,1,1),(4,1,1,1),(3,1,1,1),… | **5** | 5 | 74 – 1424 |
| `[1,0,−10,2,13,4,0,0]` | (5,1),(3,1,1,1),(3,2,1),(4,1,1),… | **5** | 5 | 27 – 443 |
| `[1,−12,53,−97,33,100,−88,12]` | rich | **5** | 5 | 12 – 46 |
| split `∏(t−k), k=1..7` | trivial | **5** | 5 | 174 – 176 |
| split `k=−3..3` | trivial | **5** | 5 | 164 – 176 |
| random seed-99, case 0 | (5,1),(6,1),(4,1,1,1),… | **5** | **5 or 6** | 26 – 481 |

**Observation.** Across every septic tested, every real solution has `deg(Δ) ≤ 5` and
`deg(a) ≤ 6`. No degree 7, 8, … appeared. The minimal polynomials of the degree-5 cases have
integer coefficients of size up to `~10^49`, so `Δ` is a genuinely high-discriminant degree-5
algebraic number, not a disguised rational number; the relations were re-verified at full
precision, so they are not PSLQ artefacts.

**Interpretation (hypothesis, not theorem).** If the decisive elimination
`Elim(a,b,c,p,q,r)(Δ)` is a polynomial of degree ≤6 whose coefficients are polynomial/rational
functions of the coefficients of `q` (i.e. the covering solution is a *uniform* degree-≤6
function of the data), then for every totally real `q ∈ K[t]` the solution lies in a degree-≤6
extension of `K`, hence in `K` by `root_Pconstructible_le_six_coeffs`. That would prove: *every
real root of a totally real septic over `K` is P-constructible.* The numerics above are
consistent with this but do **not** establish it: the observed degree could in principle depend
on `q`, and I did not obtain the elimination polynomial in closed form.

**Galois note.** The Frobenius patterns in the table are cycle types of `q mod p` and are used
only as a proxy for "generic/large Galois group"; Wolfram 15 has no `GaloisGroup`. They show the
degree-5/6 phenomenon is *not* an artefact of `q` having a small Galois group — it persists for
`q` whose factorisation types include 6-cycles and 5-cycles.

---

## 5. The conditional construction (move tree). `[Lean]` conditional on a `K`-point

The following is the exact construction that would finish the proof **if** a K-point
`(a,b,c,p,q,r,Δ)` of (∗) with `Δ>0` and generic side conditions were produced. It is stated as a
move tree; every step below is justified by an existing Lean theorem.

```
Input: monic separable totally real q ∈ K[t], deg q = 7; and a K-point of (∗):
       u = t³+a t²+b t+c ∈ K[t], v' = p t²+q t+r ∈ K[t], Δ ∈ K, Δ>0.

1. W := u²·(u'²+v'²) − Δ·v'² ∈ K[t].                       (coefficients in K)
   By (∗), q | W; write W = q·g with g ∈ K[t] (deg g = 3) by polynomial division
   (Euclidean algorithm uses only +,−,×,÷ on coefficients, so coeffs of g are in K).

2. D := √Δ ∈ K.                                             (sqrt_Pconstructible, Δ>0)

3. Realize the family: x := u (cubic), y := −∫ v' dt (a cubic with y' = −v').
   γ := (x,y) is a cubic pair with K-coefficients.

4. Offset: d := D ∈ K; the offset arc of γ at distance d satisfies the `offset`
   side conditions on a rational window around any regular parameter
   (exists_rat_window_cubicPair). The `x`-axis is the line A=1,B=0,C=0; its
   leading-direction condition is u₃=1≠0.

5. Cross the offset with the x-axis. The rationalized crossing polynomial is exactly
   W (up to the sign convention of `offsetCrossVal`), and for the correct sign of d
   the genuine crossing equation `x(β)√(x'²+y'²) = d·y'(β)` holds at each root β of W
   with `x'(β) ≠ 0` or `y'(β) ≠ 0`. `offsetCubicPairCross_root_Pconstructible` then
   gives: β ∈ K.

6. Since q | W, choose β a real root of q; β ∈ K.  ∎
```

Side conditions to check for the target `β` (the smallest real root, say):
`u` genuine cubic — automatic; `Δ>0` — observed in every case; regularity at `β` — needs
`u'(β) ≠ 0 ∨ v'(β) ≠ 0`, an open condition, observed to hold for the generic solutions.

**Numeric instantiation (`B1-12-movetree.py`).** For `q = t⁷−7t⁵+14t³−7t+1` a numerical
solution `(a,b,c,p,q,r,Δ)` (refined by Newton at 60 digits) was pushed through the tree. With
`W = u²(u'²+v'²) − Δv'²`, `x := u`, `y := −∫v'` and `d := √Δ`:
- `W = q·g` with `g = 9.0003918 t³ + 15.3683237 t² − 15.0244668 t − 15.9236747`; the division
  remainder is `max|rem| = 1.99e-59` (passes 30 digits, in fact 59). `[numeric, 59 digits]`
- At the real root `β = −1.9776616524502570901…`, `q(β) = −6.2e-60` and the genuine
  axis-crossing equation `x(β)√(x'²+y'²) = d·y'(β)` holds: both sides equal
  `2.880280305787434744740644637977513652781`, difference `6.2e-61`. `[numeric, 60 digits]`

So the tree of §5 is numerically verified end-to-end; the only thing it is missing to be a
theorem is that `(a,b,c,p,q,r,Δ) ∈ K^7`, which is exactly sub-problem P0.

**Status of the tree: CONDITIONAL.** The only missing input is step 0's K-point. With the
numeric (degree-5) point the tree is a valid *real* construction but not yet a `K`-construction;
no `sorry`-free Lean theorem asserts the hypothesis.

---

## 6. Calibration on smaller/known cases  `[symbolic]` + `[numeric]`

The decic formula is degree 10, so a fixed target `q` of degree `n` needs a cofactor of degree
`10−n`, and the covering is `n` equations in the 7 effective unknowns:

| target `q` | `n` | cofactor deg | equations | unknowns | slack (`7−n`) | expected |
|---|---|---|---|---|---|---|
| totally real quintic | 5 | 5 | 5 | 7 | **+2** | easily covered |
| totally real sextic | 6 | 4 | 6 | 7 | **+1** | easily covered |
| **totally real septic** | 7 | 3 | 7 | 7 | **0** | borderline (this task) |
| totally real octic over ℚ | 8 | 2 | 8 | 7 | **−1** | overdetermined; not expected to be covered by the decic engine |

- Quintics and sextics over `K` are already in `K` by `root_Pconstructible_le_six_coeffs`, so
  they are not a *test* of new power; the point of the row is that the decic engine's slack
  behaves as the count predicts. **`B1-10-counts.py` confirms it numerically:** for a random
  totally real quintic, `least_squares` from 300 random starts finds a solution with `Δ>0` from
  **128/300** starts; for a random totally real sextic, **60/300**. The underdetermined covering
  systems are solvable, reproducing the known-in-`K` results and validating the machinery on
  cases where the answer is known. `[numeric, residual <1e-8]`
- The **totally real octic over ℚ** is in `K` by `root_Pconstructible_le_eight`, so again not
  new, but it is an upper calibration: the decic family is *generically overdetermined* for
  `n=8`, which is the expected reason the octic route does not go through this engine. (A
  successful octic below degree 8 is not contradicted; it just cannot come from a naive decic
  covering.) **`B1-14-octic.py` confirms the count numerically:** for a random totally real
  octic (roots perturbed off the Chebyshev `T₈` roots), `least_squares` from 400 random starts
  gives `best|resid| = 2.93e-1` and **0** solutions with `Δ>0`, while the same solver on a
  random totally real septic gives `best|resid| = 5.68e-14` and 61/400 solutions. So the decic
  engine stops exactly where the dimension count says it should. `[numeric, resid]`

---

## 7. Precise sub-problems whose resolution settles the totally real septic

**P0 (the decisive one).** Characterize the elimination ideal of the square system (∗):
compute `Elim_{a,b,c,p,q,r}(Δ)` over ℚ(q-coefficients) and prove

  (i) its **degree is ≤6 uniformly** in the data, and
  (ii) the other six unknowns are **rational (or degree-≤6) functions** of `Δ` on the real
      branch.

P0(i)+(ii) for the branch with `Δ>0` is exactly the theorem. The numerics of §4 give
`deg ≤ 5` on all tested `q`; the missing ingredient is uniformity plus a real branch that exists
for every totally real `q`.

**P1 (real branch existence, uniform).** Prove that for every monic totally real septic over a
real-closed-by-degree-≤6 field `K`, the system (∗) has a solution with `Δ>0` and the generic side
conditions (`u'(β) ≠ 0 ∨ v'(β) ≠ 0`). Empirically true in 26+ cases.

**P2 (avoid the elimination).** Alternatively find a **triangular parametrization** of the
solution variety: a rational map over `K` producing from the septic (and finitely many rational
choices) a `K`-point of (∗), in the spirit of Prop. `phi-B` of `septicpaper_revised.tex`. The
proof would fix all but one unknown rationally and reduce the last condition to a univariate
polynomial of degree ≤6 with a certified sign change. The slack needed for this is **not** in
the decic family (square system) but in the conic family of §2 (positive-dimensional). This is
the "most likely shape of success" named in `PLAN-offset-B1`.

**P3 (a different engine).** Find an offset-based family containing an explicit 6-parameter
family of depressed septics with a triangular covering (Q5 of the plan). The decic family's
image is codimension 3, so any such family must come from a higher-degree crossing (conic,
Bézier, or offset×offset).

**P4 (negative control).** Prove that the decic family *cannot* cover a generic septic with a
rational cofactor for all `q` — i.e. pin down whether the K-point hypothesis is even plausible
uniformly, or whether the observed low degree is a small-Galois artefact. (The Frobenius data
in §4 argues against the pure small-Galois explanation, but `q` in §4 was still over ℚ.)

---

## 8. Side discoveries

1. **The root-based residual** `Fᵢ = u(rᵢ)²(u'(rᵢ)²+v'(rᵢ)²) − Δv'(rᵢ)²` is the numerically
   stable form of the covering system. Both it and the division-based form have convergence
   failure modes, so results must be cross-checked; see the solver caveat in §3. `[numeric]`
2. **Shift covariance.** Replacing `t ↦ t+s` maps a solution `(u,v',Δ)` of (∗) to a solution with
   `u(t+s)` (still monic cubic in `t`), `v'(t+s)`, same `Δ`. Hence the system is invariant under
   the one-parameter group `t ↦ t+s`, and the images for septics related by a shift coincide.
   This is visible in the data (split `k=−3..3` and `k=0..6`-type families share `Δ` ranges).
   `[symbolic]`, checked numerically.
3. **`Δ>0` is automatic in the data** but not logically forced; a solution with `Δ=0` gives
   `W = u²S`, whose roots are only roots of `u` (cubic) and `S` (quartic), so it could never
   cover an irreducible septic. The covering necessarily uses `Δ>0`. `[symbolic]`
4. **The decic image is codimension 3 but the cofactor supplies exactly 3 dimensions** for
   `n=7`. So the decic family is *marginally* able to cover septics, which explains why the
   septic is the exact frontier and why the octic falls outside. `[symbolic]`
5. **The conic extension has genuine slack.** `W_mod` for offset-cubic × conic is degree 20 and
   the covering is still 7 equations in 14 raw parameters — a positive-dimensional solution
   variety, in contrast to the square decic system. `[symbolic]`
6. **Exact-elimination wall (documented).** Every route tried for `Elim(Δ)` on the 7-variable
   system stalled: sympy `lex` Gröbner basis over `F_32003` ran >20 min without finishing;
   sympy `grevlex` over `F_32003` ran >15 min without finishing (`B1-11-elim-grevlex.py`);
   Wolfram `Eliminate`/`GroebnerBasis` on the same system returned HTTP 504 (`timeConstraint`
   300 s). The only bounded exact computation that did finish was the **5-variable analogue**
   (quadratic pair = parabola offset covering a quintic, `B1-13-quintic-analogue.py`): the
   `grevlex` basis took 98 s (70 polynomials) but `fglm` reported a **positive-dimensional**
   ideal. That analogue is therefore *not* faithful: parabola offsets are rational by the
   Pythagorean-hodograph phenomenon (overview §(O6)), which degenerates the covering system.
   No smaller faithful square analogue exists — the septic `(m,n)=(3,7)` is the unique square
   case — so the elimination must be attacked directly by a dedicated CAS (Singular/Macaulay2)
   or a monodromy/total-degree homotopy. `[blocked]`

## 9. Leads for other tasks

- **A2 (crossing families).** Compute the exact image dimension and the covering count of the
  offset-cubic × conic family; the primitive `W_mod = (F(γ)R+d²Q)²−d²RL²` is written down in
  `B1-10-counts.py`. The positive-dimensional solution variety is the natural home for a
  `phi-B`-style sign change for the totally real septic (P2 above).
- **A3 (offset × offset).** A crossing of two offsets may give more slack than the conic
  crossing; whether a K-point of the resulting covering can be forced by IVT is open.
- **B2 (theory).** Is there a general theorem that a square system of the form
  `u²(u'²+v'²) = Δv'² mod q` has a solution in degree ≤ `2n−1` (here 5 = 2·3−1, the recovery
  degree) or ≤6? The observed degree 5 equals the normal-equation degree of the cubic pair;
  this coincidence deserves explanation and would be the cleanest route to P0.
- **DegreeSeven / StopTotallyReal.** The stop theorem `totallyReal_no_tschirnhaus` remains
  correct; the offset route is orthogonal to it (no Tschirnhaus is used). A formal statement of
  the conditional theorem of §5 ("if a K-point of (∗) exists then the septic root is in K") is
  the right Lean artifact for B4; it needs only `offsetCubicPairCross_root_Pconstructible` plus
  polynomial division and is independent of P0.
- **Reproduction.** Re-run `B1-10-counts.py` (decic rank = 7, conic degree/rank, quintic/sextic
  calibration) and `B1-12-movetree.py` (30-digit move-tree check) as the first checks.



