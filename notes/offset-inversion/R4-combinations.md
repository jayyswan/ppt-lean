# R4: combinations (feeding outputs forward, non-uniform targets, `am`)

Stream R4 of `PLAN-offset-inversion.md`. No `.lean` edit, no commit, no `lake`. Inputs read: the plan,
`CLAUDE.md`, `Defs.lean` (re-read against the remodelled `offset`), `notes/offset-inversion-tangent-angle.md`,
`R0`, `R1`, `R2`, `R3`, `R5`, `W0`, `atlas.wl`, `sheared-sine-intersections.md`, `sheared-sine-inversion.md`,
`Jacobi.lean` (Outlook only), `ppt-curves/M.md` §2, `spiral/C.md`, and `OffsetInversion/Parabola.lean` (names only).

Labels: **[Proof]**, **[Wolfram]**, **[Heuristic]**, **[Open]**. **Backend: every number in this note was produced by
the Wolfram Language MCP** (5 evaluator calls, 30 to 130 digit working precision; no Python). `atlas.wl` could not be
`Get[]`-ed (the evaluator is a Linux sandbox without the Windows mount, `W0.md` §0); its conventions
(`n = (-y', x')/s`, `kappa = (x'y''-y'x'')/s^3`, speed `sqrt(x'^2+y'^2)`) were re-typed inline in each call.

Status vocabulary, mapping the plan's "E/R/N/?" to this programme. **E** elementary or algebraic (no new function).
**R** already reachable without offset inversion. **N** a new equation family (an offset-inversion shape).
**?** unsettled. A second tag, **P** (parameter extension: same equation shape as a one-step entry, parameters moved to
earlier outputs) or **C** (genuinely coupled: one step contains two unknown-bearing objects).

---

## Findings summary

1. **Feeding outputs forward is triangular, so it enlarges the set of numbers, not the set of equation shapes
   [Proof].** Every constructor takes numbers fixed before the step is posed, so a depth-n number is the last entry
   of `w_1 = f_1(data)`, `w_2 = f_2(w_1, data)`, ..., with each `f_k` one entry of the one-step catalogue
   (`R(psi) - d psi = x` over R1/R2 curves) (spiral `C.md` S1, transferred). Outputs can enter as `d`, `x`, the start
   point, a window bound, a scale factor (the elliptic modulus of R2's weights) or a rotation; every such slot takes
   any P-constructible number (`arctan`, `log`, `pi` are P-constructible, `Basic.lean` lines 1902, 2850, 1711), so
   every case is **P**. Worked example with 130-digit numbers in §1.2.

2. **Curve-level coupling reduces to the same thing, by a cut-commutation lemma [Proof sketch, §1.3].** There is no
   union constructor, so every curve is a parameter window of a tower word applied to a base curve, and `offset`,
   affine maps and `restrict` act pointwise. An arc laid by `arc_of_length` is therefore "the whole word, cut at
   an unknown parameter". The unknown enters later steps only as (i) an evaluation point of a tower function (a
   number), (ii) the upper limit of an arc length (a number), or (iii) a selector among intersection points of the
   *uncut* curves. None of these couples two unknowns. Offset of an offset arc, a non-uniform scaling in between
   (R2's N1), arcs started at an earlier endpoint, intersections with the cut arc: all **P**.

3. **N1 (R2's best candidate) is a legal construction and its root is P-constructible, but R2's cusp condition is
   wrong [Proof + Wolfram, §1.4].** Legal route: `restrict` the parabola to `[0,B]`, `offset d1`, `scale_y c`,
   `offset d2`, `arc_of_length` from `(0, c d1 + d2)`, `box_xmax` and `box_ymax`. The root `W` is a *rational*
   function of the two readouts (checked at one parameter set, 40 digits). The corrected cusp-free condition is
   `1 - d1 - d2 c > 0` (for `d1, d2 >= 0`), not `|d1| < 1, |d2| c < 1`: R2's displayed `Phi'` is wrong while its
   equation (2.3) is right.

4. **Non-uniform targets: nothing reached, nothing excluded.** `tan x = x`, the cantilever beam and the goat equation
   are *not* roots of any parabola-offset-inversion or N1 equation with rational data (288 PSLQ tests, positive
   controls found, §2.2); the only hits are the beam's own identity `asinh w + arctan w = pi`, which is the log-cosine
   curve's equation (coefficient of the parabola term `w sqrt(1+w^2)` is 0). Triangular chains cannot make `d` or `x`
   depend on the root, which is the uniform obstruction, but for a *single number* the question is arithmetic and is
   **[Open]**. New partial result: an intersection of an offset sheared sine with any offset/affine word on an
   *algebraic* base curve never gives `tan x = x` uniformly [Proof sketch, §2.3], which closes the first bullet of
   `sheared-sine-intersections.md` §3e.

5. **`am`: confirmed, and the weighted integrals do not change it [Proof + Wolfram, §3].** On the sine tower,
   `dpsi` (and every R2 weighted angle form `W dpsi`) is holomorphic at the two points over `u = cos t = infinity`;
   the residue of `ds` there is `+-i <p,r>/|r|` (`p, r` the columns of the net linear part) and the leading double pole
   `-|r| tau^-2` is nonzero, and offsets add nothing to either. So no sine-tower inversion is `am`, and none is a
   pure `F/E` combination unless the net linear part has orthogonal columns.

---

## 1. Feeding outputs forward

### 1.1 The slots

Facts from `Defs.lean` used throughout: `offset` needs a *whole* curve (`himg`, `a < b`, injective on `Ico`, `hseam`,
`C^1`, `hreg`), so the parabola must first be cropped by `restrict` to a window `[0,B]` with `P`-constructible `B`
and `B` must not depend on the unknown (any `B` with `Phi(B) >= x` works; see §1.4); `arc_of_length` needs a
`P`-constructible start; `box_*` need compact non-empty sets.

| output used as | where it enters | effect on the equation | verdict |
|---|---|---|---|
| `d` of an offset | coefficient of `psi` | `R(psi) - d psi = x`, new `d` | **P**, N |
| `x` of `arc_of_length` | right-hand side | new `x` (also `x = Phi(w)` by `arc_length`, forward evaluation) | **P**, N |
| start point | constant `R(psi_s) - d psi_s` | absorbed into `x`: the equation is `R(psi) - d psi = x + F(psi_s)`, and `psi_s` is algebraic over the readouts, so `F(psi_s)` is P-constructible | **P** |
| scale factor `c` (`scale_y`) | elliptic modulus `k^2 = 1 - c^2` and weights in R2 §Q1 | N1 with new `c` | **P**, N |
| rotation angle | cancels (R2 §Q2.2: only shifts `x`) | none | **P**, E |
| translation | none for arc length; moves intersection partners | none / new partner position | **P** |
| `restrict` window bound | which sub-arc survives | same as an arc of length `x1` from the vertex (monotone case) | **P** |
| window end of an arc later offset | offset of the arc = the word cut at the same parameter (§1.3) | adjacent offsets add, `d = d1 + d2` | **P**, E |
| partner position/parameters in `inter_x/y` | data of the partner curve | one-step entry of R3's class with new parameters | **P** |

### 1.2 Worked example [Wolfram, 130 digits, one call]

Step 1: parabola, `d1 = 1/2`, `x1 = 1`:
`(w s + asinh w)/2 - (1/2) arctan w = 1`, `s = sqrt(1+w^2)`, root `w1 = 1.19469384349484182976872145227272`.
Positive control for the PSLQ machinery: the relation `(1, 1, -1, 0, -2)` on `{w s, asinh w, arctan w, pi, 1}` is
found.

Step 2 (feed forward): `d2 = 1/s1 = cos psi1` and `x2 = e_x1 = w1(1 - d1/s1)` (the `box_xmax` readout of step 1).
Solve `F_{d2}(w2) = x2`: `w2 = 1.14359939644826983061461319389880`.

* Relation over `Q` (basis `{w2 s2, asinh w2, arctan w2, pi, 1}`): **none** (`FindIntegerNullVector` fails, bound 10^12).
* Relation over the field generated by step 1: `(1, 1, -2, -2, 1)` on `{w2 s2, asinh w2, arctan(w2)/s1, w1, w1/s1}`,
  i.e. the step-2 equation with `d2 = 1/s1`, `x2 = w1 - w1/(2 s1)`.
* A mixed relation between `w2` and `w1` constants: only step 1's own equation `(0,0,0,1,1,-1,-2)`.

So `w2` is a root of a one-step equation whose coefficients live in `Q(w1, s1)`, and of no one-step equation with
rational coefficients. That is exactly "parameter extension". Whether `w2` lies in the field generated by `w1` and
standard constants is a transcendence question [Open] (same status as spiral `C.md` §4.3).

### 1.3 Curve-level composition: the cut-commutation lemma

**Lemma (cut commutation) [Proof sketch].** Let `gamma: [a,b] -> R^2` be a regular C^1 tracing and `a < c <= b`. Then
`offsetParam (gamma|_[a,c]) d = (offsetParam gamma d)|_[a,c]`, and likewise for every affine map and for the
spatial `restrict`-by-window up to which parameters survive.
*Reason.* `offsetParam gamma d t = gamma t + d * unitNormal gamma t` uses `gamma` and its derivative at `t` only, and at
`t = c` the one-sided derivative from inside `[a,c]` is the derivative of `gamma` (this is why the remodelled
`offset` insists on `a < b`). The non-local constructors are exactly `inter_*`, `box_*`, `arc_length`,
`arc_of_length`. Hence every curve is `{Psi(t) : t in J}` with `Psi` a tower word (an offset/affine composition) on a
base parametrisation and `J` an interval whose ends are P-constructible spatial cuts or laid-arc ends.

Consequences, each by checking the four non-local constructors:

* **Offset of an offset-inversion arc.** Offsetting the laid arc `[0,w1]` of `P_{d1}` by `d2` gives `P_{d1+d2}` on
  `[0,w1]` when `1 - d1 kappa > 0`. If `1 - d1 kappa < 0` along the whole arc the tracing is regular but the normal of
  `P_{d1}` is the *negative* of that of `gamma`, so the second offset gives `P_{d1-d2}`. [Wolfram, parabola, `d1 = 3`:
  at `w = 0.3` (`1 - 3 kappa = -1.636`) offsetting by `+1` lands exactly on `P_2` (residual 0 to 179 digits, versus 2
  from `P_4`); at `w = 3` (`1 - 3 kappa = +0.905`) it lands exactly on `P_4`.] An arc that contains a cusp cannot
  be offset at all (`hreg` fails on every tracing).
* **Laying again from the end.** Starting at the readout point `E = (e_x, e_y)` along the same offset curve with length
  `x2` solves `F(psi2) = x1 + x2`. Starting along a *different* curve through `E` (translate so that its vertex is
  `E`) is a fresh one-step entry. A start at an interior point of a tower curve only adds the P-constructible constant
  `F(psi_s)`.
* **Intersection with the cut arc.** `A(x1) cap T = {pt}` where `A(x1) = P[0,w1]`: the point is an intersection of the
  *uncut* `P` with `T` lying in the window. The unknown `w1` can change only *which* point is selected, never its
  value; and a selection by the root can already be made by a P-constructible `restrict` using `e_x` or `e_y`. So
  "OI arc cap curve" is a one-step R3 intersection with a window.
* **OI then box/intersection, and the reverse.** A readout number enters a later curve as a data number (§1.1).
  Intersection output as `d` or `x`: same, with the intersection coordinate in the data field.

So the "same unknown in two places" configuration never arises: in a chain the later steps see `w1` only as a number.

### 1.4 N1 as a worked, legal construction [Proof + Wolfram]

Word: `poly_graph` (parabola) -> `restrict` to `[0,B]` -> `offset d1` -> `scale_y c` -> `offset d2` -> `arc_of_length`
from the vertex image `(0, c d1 + d2)` -> `box_xmax`, `box_ymax`.

* **Closed forms** (checked against the `Defs` definitions of `unitNormal`/`offsetParam` at three points, residual 0
  to 90 digits): with `s = sqrt(1+w^2)`, `t = sqrt(1+c^2 w^2)`,
  `X(w) = w - d1 w/s - d2 c w/t`, `Y(w) = c(w^2/2 + d1/s) + d2/t`.
* **Speed (correcting R2).** True speed of the final curve, 30-digit numerical differentiation of the definitions, at
  `(c,d1,d2) = (2,1/3,1/5)`, `w in {0.1, 0.5, 1.5}`:
  `Phi'(w) = (1 - d1/s^3) t - d2 c/t^2` (agreement to 30 digits). R2's displayed product
  `(1 - d1/s^3)(1 - d2 c/t^3) t` is **different** (0.4266 vs 0.3003 at `w = 0.1`), although R2's integrated
  equation (2.3) is correct. `Phi'` is increasing in `w`, so the final curve is cusp-free iff `Phi'(0) = 1 - d1 - d2 c > 0`.
  [Wolfram, `(c,d1,d2) = (2, 3/5, 2/5)`: R2's stated conditions hold (`|d1| < 1`, `|d2| c = 0.8 < 1`) yet
  `Phi'(0) = -0.4` and a cusp sits at `w = 0.3179`.] Equivalent: `d2 c/(1 - d1) < 1` is the curvature condition at the
  vertex (the offset's curvature there is `c/(1 - d1)`).
* **Monotone readout.** `X'(w) = (1 - d1/s^3) - d2 c/t^3` (checked to 30 digits) is increasing, `X'(0) = 1 - d1 - d2 c`,
  and `Y' = w X' >= 0`, so both coordinates are strictly monotone on `w >= 0`; `box_xmax` and `box_ymax` return
  `X(w*)` and `Y(w*)`.
* **Window.** `Phi(W) >= X(W) >= (1 - d1 - d2 c) W`, so `B = x/(1 - d1 - d2 c)` is P-constructible, independent of the
  root, and suffices (for `d1, d2 >= 0`).
* **The root is P-constructible [Wolfram, one parameter set; Heuristic for general].** For `(c,d1,d2) = (2,1/3,1/5)`
  the lex Groebner basis of `{ex - X, ey - Y, s^2 - 1 - w^2, t^2 - 1 - c^2 w^2}` contains three polynomials linear in
  `w` with coefficients in `Q[ex,ey]` and a relation `f(ex,ey) = 0` of bidegree `(16, 12)`; solving the first for `w`
  at the readouts of `w = 3/2` returns `3/2` to 40 digits. So `w = r(ex, ey)` is a rational function of the two
  readouts: the map `(w,s,t) -> (X,Y)` is birational onto its image. Using the x-readout alone would give an
  equation of degree well above 6, so the **y-readout (or a vertical-line intersection) is needed here**, unlike
  the single-offset parabola where R0's quartic in the x-readout suffices. For general `(c,d1,d2)` birationality is
  expected (generic) but not proved here.
* **Then** `E(arctan w*|1-c^2)` is the length of an elliptic arc between P-constructible points (`arc_length`), so the
  whole of (2.3) is P-constructible data.

---

## 2. Non-uniform targets

### 2.1 What the structure says

* **One step, uniform:** excluded by R2's parallelism theorem (matching the beam spectrum for all `x` forces
  `rho = A + sec psi`, i.e. a parallel curve of the log-cosine; `tan x = lambda x` forces `rho = A + B sec^2 psi`, i.e.
  a parallel of the catenary), and no base curve satisfies either [R2 Proof + Wolfram].
* **Chains (§1):** triangular, parameters cannot depend on the root, so the uniform obstruction survives in the
  form: the last step is a one-step entry whose `d, x` lie in the field of earlier outputs. This does not rule out a
  chain whose *earlier outputs happen to be* the numbers needed for one particular root.
* **Differential degree does not separate.** Every OI-inverse `w(x)` has `w' = x'/(s - d/(1+w^2))`, algebraic in
  `(w, s)`; the root of `tan x = lambda x` has `x' = x/(1 + lambda^2 x^2 - lambda)`, rational in `(lambda, x)`.
  Both lie in Pfaffian chains with algebraic right-hand side, so the Jacobi-style differentiation step produces no
  contradiction. This is why the Jacobi collapse ("`L` affine") does not transfer: it used that `am` composed with an
  elementary function is non-elementary; here the target is a Pfaffian function of the same differential type as the
  generated ones, and a separation needs the branch-point invariant of R3 (infinitely many finite log branch points
  of `gd`), which R3 proves only for depth <= 2 (offset inversion is depth 3; a chain of two is depth 6).
  **[Open]**: no obstruction is proved against a depth-6 chain; none was found.

### 2.2 PSLQ scan [Wolfram, 130 digits, one call]

Targets (all to 130 digits, 25 shown): `tan x = x`: 4.49340945790906417530788, 7.72525183693770716419507; beam
`cos x cosh x = -1`: 1.87510406871196116644531, 4.69409113297417457643639; goat `sin b - b cos b = pi/2`:
b = 1.90569572930988389488267, and the rope ratio `2 cos(b/2)` = 1.19469... (the scan used it as a fifth/sixth target).

For each target `r` the maps `w in {r, 1/r, tan r, tan(r/2), sinh r, tanh r, e^r, r^2, sin r, cos r, sec r, r - pi}`
(those with `1e-6 < |w| < 1e8`) were tested:

* parabola atoms: `FindIntegerNullVector[{w sqrt(1+w^2), asinh w, arctan w, pi, 1}]`, bound `10^12` (a relation with
  coefficient ratio 1:1 on the first two entries is exactly `F_d(w) = x` with rational `d, x`; the test is a superset);
* N1 atoms for `c in {2, 1/2, 3}`: `{w t, asinh(cw), E(arctan w|1-c^2), arctan(cw), pi, 1}`.

**Positive controls found:** parabola root of `F_{1/2} = 1`: `(1,1,-1,0,-2)`; N1 root at
`(c,d1,d2,x) = (2,1/3,1/5,3/2)` (`W = 1.2604885628591584442733575166`): `(30,15,-20,-12,0,-90)`.
**Results:** 72 parabola tests, 216 N1 tests. N1: **0 hits**. Parabola: **2 hits**, both for the first beam root
(`w = sinh r`: `(0,-1,-1,1,0)`; `w = tan r`: `(0,1,1,1,0)`), i.e. `asinh w + arctan w = pi`, which is the beam
equation `x + gd x = pi` itself. The coefficient of `w sqrt(1+w^2)` is 0, so these are the log-cosine curve's
equation (R5 row 8), not a parabola equation. They are a useful check that the dictionary row is correct to 130
digits and that the scan is sensitive. No other target/map pair has a relation of height <= 10^12 in either family;
for 5 to 6 constants at 130 digits the expected number of accidental relations is negligible. **Evidence only:**
it says the roots are not values of these families at rational (or `pi`-rational) data; it says nothing about
P-constructible data.

### 2.3 Intersections: closing the first bullet of `sheared-sine-intersections.md` §3e [Proof sketch]

Setting: uniform `tan x = x` from a sheared sine (or an offset of it) meeting an algebraic partner `Q`. By §3b the
partner must contain the whole curve `Gamma_{a,b,d}`, which is irreducible (degree 4 for `d = 0`, 12 for `d != 0`)
with two ends running to infinity along `+-(-b,a)` and approaching the two *distinct parallel* lines
`aX + bY = +-a - d rho` (§3c).

Let `Q` be (the Zariski closure of) an arc of `A_k P_{d_k} ... A_1 P_{d_1}(C)` with `C` an algebraic base curve and the
`A_j` affine. Then `Q = closure(Gamma)`, so the real branch of the full word curve containing the arc is the branch
of `Gamma`, and by analytic continuation along `t` its two ends are within bounded distance of two parallel lines.
Each factor moves points a bounded distance (an offset by `|d|`; an invertible affine map sends a strip around a
line to a strip around its image line and preserves parallelism). So a branch of `C` itself would need both ends in
strips about two parallel lines, with opposite directions. Base algebraic branches:

| `C` | branch ends | verdict |
|---|---|---|
| ellipse | bounded | no ends |
| polynomial graph `deg >= 2`, cubic Bezier continued, `y = a x^b` with `b > 0, b != 1` | super- or sub-linear unbounded; distance from any line `-> infinity` | none |
| line, rectangle sides | lines (offset of a line is a parallel line; no curve) | trivial |
| `y = a x^b`, `b < 0` | ends along the two axes, **non-parallel** asymptotes | not parallel |

So no word on an algebraic base curve contains `Gamma`: uniform `tan x = x` is not an intersection of an offset sheared
sine with such a curve. Gaps (so this is a sketch): (i) the continuation step from "an arc meets `Gamma` in infinitely
many points" to "the full real branch is `Gamma`'s branch" (cusps/folds of the intermediate offsets, where the tracing
is not regular, need care); (ii) rank-1 affine maps (degenerate images, lines) are trivially excluded; (iii)
non-algebraic partners (`exp_two`, other sine words, `arc_of_length` subsets of them) are untouched and remain
**[Open]**. It does not use any new Wolfram computation; the asymptote data is from §3c of that note.

### 2.4 Other combinations tried (no new route)

* Box of an offset of a sheared sine: `sheared-sine-intersections.md` §3a (algebraic in `(sin t, cos t)`), unchanged.
* OI arc cap a line/conic: algebraic elimination (R3 Lemma 2.3), the root is a function of the cut-free curves.
* Spiral and other new curves (catenary, `y = ln sec x`) are out of scope; the dictionary of R5 stands: `tan x = lambda x`
  needs a catenary-like `rho`, the beam a log-cosine-like `rho`, the goat a transcendental Whewell function.

---

## 3. `am` and the residue obstruction

Normal form (`sheared-sine-inversion.md` §1): `gamma(t) = (-b t + sin t, a t)`, `u = cos t`, `q(u) = (u-b)^2 + a^2`,
`tau = 1/u` (a local coordinate at each of the two points over `u = infinity` on the curve `W^2 = (1-u^2) q(u)`,
since the quartic is unramified over infinity).

**(a) `dpsi` has zero residue and no pole at `infinity` [Proof + Wolfram].** `psi = arg((cos t - b) + i a)`,
`dpsi/dt = a sin t/q(cos t)` [Wolfram, symbolic check], hence `dpsi = -a du/q(u)`. In `tau`:
`d psi/d tau = a + 2ab tau + (3ab^2 - a^3) tau^2 + ...` (series at `tau = 0` [Wolfram]), **holomorphic and nonzero**. In
particular residue 0. (The poles of `dpsi` are at `u = b +- i a`, the roots of `q`, where `W` is a local parameter
and `ds` vanishes: the statement of the note.)

**(b) The residue of `ds` [Wolfram + Proof].** `ds = sqrt(q/(1-u^2)) du` up to the choice of branch. Series [Wolfram]:
`ds/dtau = -tau^-2 + b tau^-1 - (1+a^2)/2 + ...` times the constant `+-i`. So the double pole has leading coefficient
`-+i` (nonzero) and the residue is `+-i b`, the note's `+-iB` with `B = -b`.

**(c) General linear image, all of R2's weights.** A linear part `L` with columns `p = L e1`, `r = L e2` gives
`Q(u) = |p + u r|^2` and `ds_L = sqrt(Q/(1-u^2)) du`.
* Series [Wolfram, symbolic in `p1,p2,r1,r2`]: coefficient of `tau^-1` is `-<p,r>/|r|`, double-pole coefficient `-|r|`.
  So the residue at `infinity+-` is `+-i <p,r>/|r|`, zero **iff the columns of `L` are orthogonal**; this is `b = 0`
  in the normal form (`L = [[-b,1],[a,0]]` has `<p,r> = -b`).
* R2 weighted form at step `i` (matrices `L_<=i` up to the offset, `M` after it): with `Q_i = |L_<=i (1,u)|^2`,
  `Q_tot = |M L_<=i (1,u)|^2`, the form is `omega_i = sqrt(Q_tot/Q_i) det(L_<=i) du/Q_i`
  (since `dpsi_i = det du/Q_i`, checked symbolically to 0). Both quadratics have degree 2, so the ratio is bounded and
  `du/Q_i = O(du/u^2) = O(dtau)`: **holomorphic at `tau = 0`, residue 0** [Proof]. Wolfram, `L_<=i = [[2,1],[1,3]]`,
  `M = [[1,2],[0,1]]`: `omega/dtau = -sqrt(29/5)/2 + 14/sqrt(145) tau - ...`, starting at `tau^0`.
* Whole tower on the sine: `ds_word = ds_{L_tot} - sum_i d_i omega_i` (R2 (2.1)). All `omega_i` are holomorphic at
  `infinity+-`, so the double pole `-|r_tot|` and the residue `+-i <p_tot,r_tot>/|r_tot|` are **exactly those of the
  final affine image `L_tot gamma`, whatever the offsets are**.
* Numerical sanity [Wolfram, 45 digits]: for the sine with `d = 1/5`, `L = [[1,1/2],[0,3/2]]`, window `[0, 0.7]`, the
  true arc length of `L P_d` equals `int |L gamma'| - d int |L T| dpsi` to 44 digits (R2 (1.1) on a bounded curve).

**Conclusions.**
1. **Never `am` [Proof].** A first-kind inversion needs `ds` to be the pullback of a holomorphic differential under
   any finite cover. `ds_word` has a nonzero double pole at the points over `infinity` (offset terms are holomorphic
   there), which cover-pullback cannot remove. Same for the ellipse: its bounded curve has the double pole at
   `z = 0, infinity` of `e^{it}` and `omega_i` vanishes there (`dpsi ~ z dz`), as the Outlook of `Jacobi.lean` says;
   the Outlook's "regular at the poles above, so they cannot cancel them" is confirmed here, with the additional
   fact that the weighted terms have simple poles (third kind) at the roots of `Q_i`, away from `infinity`.
2. **Never a pure `F/E` combination when `<p_tot,r_tot> != 0` [Proof].** `dF, dE` have zero residues, `ds_word` has
   the residue `+-i <p,r>/|r|` at `infinity+-` regardless of offsets.
3. **When `<p_tot,r_tot> = 0`** the residue obstruction at `infinity` disappears, but offset terms with `d_i != 0`
   contribute residues at the finite roots of `Q_i` (they are logarithms: the bare `arctan` and the third-kind part of
   weighted `E`). They can only cancel against each other, i.e. against terms with the same `Q_i`, which R2 §Q2.3
   shows merge into one coefficient; so they cancel only when that net coefficient is 0, which is the offset-free case.
   [Proof for the terms listed; **[Open]** only in that the exhaustive case analysis of cancellations among
   different `Q_i` was not written out.]
4. Hence offset inversion on the sine tower (or ellipse tower) does not approach `sn/cn/dn/am`; the statement of
   `sheared-sine-inversion.md` §4(c) ("offsetting keeps the double poles and the residues") is confirmed and extended
   from a single offset to arbitrary tower words.

---

## 4. Classification table

| # | combination | system | decouples? | status |
|---|---|---|---|---|
| 1 | OI output -> `d` of another OI (same or other curve) | `F_{d1}(w1) = x1`; `F_{h(w1)}(w2) = x2` | yes (S1) | **P**, N (§1.2) |
| 2 | OI output -> `x` (also via `arc_length`) | `F(w2) = Phi(w1)` | yes | **P**, N |
| 3 | OI output -> start point or window end | `F(w2) = x2 + F(psi_s)` | yes | **P** |
| 4 | OI output -> scale `c` (modulus) | N1 with new `c` | yes | **P**, N |
| 5 | OI output -> rotation, translation | cancels / moves partner | yes | **P**, E |
| 6 | offset of the laid arc (adjacent) | `d = d1 + d2`, or `d1 - d2` on a reversed arc | yes | **P**, E (§1.3) |
| 7 | offset, non-conformal affine, offset (N1) | `Phi(W) = x`, cusp: `1 - d1 - d2 c > 0` | yes | **P**, N (§1.4) |
| 8 | second arc laid from an earlier readout | `F(w) = x1 + x2` | yes | **P**, E |
| 9 | OI arc cap another curve | intersection of uncut curves with a window | yes | **P**, R/? by partner |
| 10 | OI -> intersection with sine/exp/ellipse (OI number as parameter) | Kepler-type with new parameters | yes | **P**, R |
| 11 | intersection -> OI (`d`, `x` from coordinates) | one-step entry over a larger field | yes | **P**, N |
| 12 | OI -> box of a tower curve | number | yes | **P** |
| 13 | N1-type curve cap sine/exp (one step, two transcendental curves) | R3 Lemma 2.3 `F = g1 - g2` | no (one step) | **C**, ? (not analysed) |
| 14 | sine tower words, any offsets | `ds` residue and pole at `infinity` unchanged | n/a | never `am`, §3 |

---

## 5. What stays open

* Transcendence statements: whether `w2` (§1.2), or any tower number, lies in the field generated by earlier ones.
* A separation theorem against depth-6 chains for `tan x = lambda x` or the beam (§2.1).
* Row 13: curves from two different transcendental towers meeting once (needs R3's two-coordinate readout gap).
* §2.3 gaps (continuation along cusps; non-algebraic partners).
* §1.4: birationality of `(w,s,t) -> (X,Y)` for general `(c,d1,d2)`, and the general N1 window/readout for negative `d_i`.

## Other things noticed

1. **R2 error.** The displayed derivative `Phi' = (1 - d1/s^3)(1 - d2 c/t^3) t` in R2 §Q2.4 (and the cusp-free condition
   `|d1| < 1, |d2| c < 1` derived from it) is wrong; the correct speed is `(1 - d1/s^3) t - d2 c/t^2`, with
   cusp-free condition `1 - d1 - d2 c > 0` (§1.4). Equation (2.3) and all of R2's numerical tables are unaffected.
2. **Crop requirement.** Because the remodelled `offset` needs a whole compact curve, every parabola construction needs
   `restrict` first, with a root-independent bound; `halfParabolaArc_PConstructibleCurve` in `Parabola.lean` (a
   P-constructible `W`) is that crop. For N1 the bound is `B = x/(1 - d1 - d2 c)`.
3. **Readout.** N1's root needs both box readouts (rational in `(e_x, e_y)`); the x-readout alone is a polynomial of
   high degree (the Groebner relation has bidegree (16,12)), so the Lean headline (parabola, quartic in `e_x`) is the
   special case where one readout suffices.
4. **A dictionary hit for free.** The scan rediscovered `x + gd x = pi` for the beam at 130 digits; it is a quick
   regression test for any future `A(u)` candidate (a curve whose `A(u) = u`).
5. **Signs.** `dpsi = -a du/q` with `u = cos t` (the sign in the note's `ds = -+i (1 + B/u ...)` is a branch choice);
   the residue of `ds` is `<p,r>/|r|`, positive-definite in the net columns, a one-line criterion
   ("orthogonal columns") that `sheared-sine-inversion.md` states in the `(a,b)` normal form.
6. **Reversed-arc offsets.** An arc on which `1 - d kappa < 0` is a legal input to `offset` (regular tracing) and gives
   `P_{d-d2}` on the second offset (§1.3), an extra legitimate `d`-range for the family `R - d psi = x`, worth a line
   in R0's list of hypotheses.
7. **Cheap partners.** Since `arctan`, `log`, `pi` and `arccos` of P-constructible numbers are P-constructible, the
   triangular tower `D_n` of spiral `C.md` §4 exists here too; "new numbers over the offset-free class" is the right
   phrase for downstream notes, not "new numbers over P".
