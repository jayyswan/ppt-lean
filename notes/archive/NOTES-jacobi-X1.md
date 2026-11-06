# NOTES-jacobi-X1 — the amplitude as a measured length

Research task `PLAN-jacobi-X1-measure.md` (X series). **No `.lean` file was created or edited.**
Numerics: Python 3.12 with `mpmath`/`sympy`/`scipy` at
`C:\Users\jason\AppData\Local\Programs\Python\Python312\python.exe`; scripts in
`archived files/jacobi-scripts/` with the `X1-` prefix. Every identity is tagged
**[symbolic]** (proved here or reduced to a named theorem) or **[numeric, N digits]**
(checked to N significant digits; the script is named). Web sources carry URLs.
`am, sn, cn, dn` use the parameter `m = c`; `mpmath.ellipfun`/`ellipf` agree with that.

---

## Plain-language summary (10 lines)

1. `am(u)` is **not** D-finite: as a function of the complex variable `u` it has infinitely many
   branch points, and a D-finite function can only be singular at finitely many points.
2. The "linear-equation test" is a real filter for the *purely algebraic* fragment of the
   constructor language: an arc length of an algebraic curve whose shape parameters and endpoints
   depend **algebraically** on `u` is D-finite, and no arithmetic combination of such lengths can
   be `am`.
3. The test's step for **moving endpoints** is correct: an algebraic change of variable turns such
   a length into a definite integral of an algebraic integrand over a fixed interval, which is
   D-finite. The `offset` step is also correct: the parallel curve of an algebraic curve is
   algebraic.
4. What the test **cannot** touch is the transcendental fragment, which `Defs.lean` permits:
   endpoints of the form `sin u`, `cos u`, `2^u`, `log u`, `ellipticEAm c u`, and the `sine` /
   `exp_two` base curves.
5. In that fragment the test genuinely fails to apply. The simplest witness is already
   constructible: the arc of the ellipse to eccentric angle `u` has length `E(u,c)`, which has
   infinitely many branch points and is not D-finite.
6. Since `am` is itself not D-finite, **any successful measured-length construction must live in
   the very fragment the test excludes**; the D-finite test is therefore correct but
   non-conclusive for the target.
7. Moving-modulus `E`/`F` combinations (the sine-curve and moving-axis candidates) were tested and
   do **not** equal `am`: the off-grid residual plateaus at `≈0.1` [numeric].
8. The DLMF derivative formulas (§19.4) show why: cancelling the `E,F` coefficients forces `dn` to
   be an algebraic function of `u`, which it is not; the only solutions are circular (they use the
   amplitude to define `φ` or `m`).
9. DLMF §22.16 offers no integral representation of `am` beyond `∫ dn` and an infinite Fourier
   series; the epsilon-function representations all have Jacobi functions in the integrand.
10. **Outcome: negative/partial.** No construction is offered; the D-finite test excludes the
    algebraic fragment precisely, and the surviving fragment (transcendental endpoints/curves) is
    where all future measured-length attempts must look.

---

## 0. What the brief asked, and the verdict in one line

The brief asks (Q1) to verify or break the D-finite test step by step — moving endpoints,
parameters inside square roots, `offset`; (Q2) whether moving-modulus `E`/`F` combinations can equal
`am`/`sn`; (Q3) to collect integral representations of `am`/`sn` and test them as arc lengths;
(Q4) two-measurement arithmetic.

**Verdict on Q1: correct with exceptions, and the exceptions are exactly the target's habitat.**
For the fragment of `Defs.lean` with only algebraic curves, algebraic shape parameters and
algebraic endpoints, the claim is correct. Its hypotheses fail for the transcendental constructors
(`sine`, `exp_two`) and for endpoints/parameters built with `sin`, `cos`, `2^x`, `log`, `arccos`,
`ellipticEAm`; there the length can be non-D-finite and the test is silent. Because `am` is not
D-finite, no D-finite length can be `am`, so a successful measurement *must* use those escapes.

**Verdict on Q2:** no moving-modulus `E`/`F` combination tested equals `am` (or `sn`); the
derivative analysis reduces any such identity to the circular cases.

**Verdict on Q3:** DLMF §22.16(i) lists only `am(x,k)=∫₀^x dn(t,k) dt` and an infinite Fourier
series (§22.16.9); no integral with an elementary integrand and constructible limits is available.

**Verdict on Q4:** D-finite functions are closed under `+ − × ÷`, algebraic substitution, and
antiderivatives, so arithmetic combinations of D-finite lengths remain D-finite and are excluded.
Combinations of *non*-D-finite lengths can cancel, but none tested reproduces `am`; the cheapest
escape is a single partial arc with a transcendental endpoint (the ellipse witness).

No positive claim is made, so the brief's construction-tree + 20-digit protocol has nothing to
attach to. The escape witness in §4 does come with an explicit move-tree, because it is the
sharpest available statement of what the test leaves open.

---

## 1. Conventions and the D-finite facts used

Write `c < 1` for the modulus parameter and

  `Δ_c(θ) = √(1 − c sin²θ)`, `F_c(φ) = ∫₀^φ dθ/Δ_c(θ)`, `E_c(φ) = ∫₀^φ Δ_c(θ) dθ`,

so `am_c' = dn_c = Δ_c∘am_c`, `sn_c = sin∘am_c`, `cn_c = cos∘am_c`, and `am_c = F_c^{-1}`
(DLMF 22.16.1, 22.16.3, https://dlmf.nist.gov/22.16 ). A one-variable function is **D-finite**
(holonomic) if it satisfies `Σ_{i=0}^{r} p_i(x) f^{(i)} = 0` with polynomials `p_i`, not all zero.

Three facts are used repeatedly.

* **[symbolic] (F1) A D-finite function has finitely many singularities.** The singular points of a
  solution of such an ODE lie among the roots of the leading coefficient `p_r` (plus possibly
  `x = ∞`); finitely many. Standard; see e.g. Flajolet–Sedgewick, *Analytic Combinatorics*,
  Note VI.9, or the Wikipedia article "Holonomic function",
  https://en.wikipedia.org/wiki/Holonomic_function .
* **[symbolic] (F2) D-finite is closed under `+`, `−`, `×`, `÷`, derivatives, and
  *antiderivatives*.** Sum/product/quotient are classical; the antiderivative is a one-line
  operator argument: if `L = Σ p_i D^i` annihilates `f` and `g' = f`, then
  `(L ∘ D)(g) = L f = 0`, and `L D` again has polynomial coefficients. Hence the integral of any
  algebraic function (algebraic ⇒ D-finite) is D-finite. D-finiteness is *not* closed under
  composition in the other order: `a(f(x))` with `f` D-finite and `a` algebraic need not be
  D-finite, which is why `Δ_c(u) = √(1−c sin²u)` is not.
* **[symbolic] (F3) Definite integrals of algebraic families over fixed or algebraic bounds are
  D-finite.** If `σ(t,u)` is algebraic in `(t,u)` and `a(u), b(u)` are algebraic, then
  `u ↦ ∫_{a(u)}^{b(u)} σ(t,u) dt` is D-finite. This is the multivariate holonomic closure
  ("integration of holonomic functions over algebraic domains"); see A.-L. Sattelberger and
  B. Sturmfels, *D-Modules and Holonomic Functions*, arXiv:1910.01395, or Wikipedia "Holonomic
  function" (closure under definite integration). It is what makes the moving-endpoint step of the
  test correct, see §3.

## 2. `am` is not D-finite

### 2.1 The complete integrals `K`, `E` *are* D-finite (calibration) **[numeric, 40 digits]**

Script `X1-01-dfinite-basics.py`, part (A). With parameter `m`,

  `m(1−m)K'' + (1−2m)K' − K/4 = 0`,   `m(1−m)E'' + (1−m)E' + E/4 = 0`

were evaluated with `mpmath.diff` at 40 dps at `m ∈ {0.09, 0.3, 0.7, 0.93}`. Worst residual
`3.4·10⁻⁴¹` (the `E` residual is `5.7·10⁻⁴²` everywhere, i.e. rounding). This is the expected
period/Picard–Fuchs behaviour (F3) and calibrates the method.

### 2.2 The incomplete integrals `E(φ,m)`, `F(φ,m)` are *not* D-finite in `φ`
**[symbolic + numeric, 8 digits on the exponent]**

For fixed `m ∈ (0,1)`, `Δ_c(φ)` has branch points exactly where `sin²φ = 1/m`. Since `1/m > 1`,
these are **complex**: `φ* = arcsin(1/√m)`, e.g. `φ* = 1.5708 − 1.8738 i` at `m = 0.09`. Because
`Δ_c` and `1/Δ_c` are `π`-periodic up to sign, the branch points repeat at `φ* + kπ`, `k ∈ ℤ`:
infinitely many. By (F1), `Δ_c`, `1/Δ_c` are not D-finite; by (F2) `E(φ,m)` and `F(φ,m)` are not
either (if `E` were D-finite, so would be `E' = Δ_c`). Script part (B) measured the local
exponents along a complex path to `φ* + h`:

  `E(φ* + h) − E(φ*) ∼ C h^{1.5}` (measured `1.5 + 2·10⁻⁶ i` at `m = 0.09` and `m = 0.5`),
  `F(φ* + h) − F(φ*) ∼ C h^{0.5}` (measured `0.5 − 1.6·10⁻⁶ i`),

as predicted by `E' = Δ_c` vanishing like `h^{1/2}` and `F' = 1/Δ_c` diverging like `h^{−1/2}`.

### 2.3 `am` is not D-finite **[symbolic + numeric, 40 digits]**

`am' = dn`, and `dn` has simple poles with residues `(−1)^{m+1} i` on the infinite lattice
`u = iK' + 2ℤK + 2ℤ iK'` (DLMF 22.4.5, https://dlmf.nist.gov/22.4 ). Script part (C) located
`dn`-poles numerically at `iK' = 2.62777 i`, `3iK' = 7.88332 i`, `5iK' = 13.13887 i` and
`2K+iK' = 3.21610 + 2.62777 i` for `m = 0.09`, with residues `−i, +i, −i, −i`. Hence
`am = ∫ dn` has a **logarithmic** branch point at each of them: infinitely many singularities. By
(F1), `am` is not D-finite.

**Independent confirmation.** Wolfram's `JacobiAmplitude` documentation states the branch-cut
structure in the complex `u` plane runs from `2sK(m) + i(4t+1)K(1−m)` to
`2sK(m) + i(4t+3)K(1−m)` for all integer `s,t`,
https://reference.wolfram.com/language/ref/JacobiAmplitude.html — an infinite lattice, exactly what
(F1) forbids for a D-finite function. DLMF 22.16.2 records the quasi-periodicity
`am(x+2K,k) = am(x,k) + π`.

## 3. Dissecting the D-finite test, step by step

The test asserts: *if a curve's equation is polynomial (ellipse, Bézier, polynomial graph, power
law, and their affine/rotated/scaled images) and its shape parameters and endpoints are algebraic
functions of `u`, then its arc length `L(u)` is D-finite; hence no such measurement equals `am`.*

| step | claim | verdict |
|---|---|---|
| fixed algebraic curve, fixed endpoints, algebraic shape parameters | `L(u)` is a period of an algebraic family → D-finite | **correct** (F3); calibrated in §2.1 |
| parameters inside a square root (`√(poly(u))` as a semi-axis) | still algebraic in `u`; (F3) applies verbatim | **correct** |
| moving endpoints `a(u), b(u)` algebraic in `u` | still D-finite: an algebraic change of variable turns the length into a definite integral of an algebraic integrand over a fixed interval | **correct** (F3); see §3.1 |
| `offset` | the parallel curve of an algebraic curve is algebraic, so `speed·|1−dκ|` is again an algebraic differential | **correct**; see §3.2 |
| `sin`/`2^x` curve families (partial arcs) | arc-length integrand is transcendental in the parameter; (F3) does not apply | **exception**; see §3.3, §4 |
| endpoints transcendental in `u` (`sin u`, `cos u`, `2^u`, `log u`, `ellipticEAm c u`) | (F3) does not apply | **exception**; see §4 |
| output of one measurement reused as a shape parameter of the next | that parameter is not algebraic in `u` unless the measurement happens to be | **exception**; see §4.1 |
| arithmetic combinations `+ − × ÷` of D-finite lengths | D-finite is closed under these | **correct**; §7 |

### 3.1 Moving algebraic endpoints are D-finite (the earlier objection was wrong)

To see it concretely, take the ellipse `x = a cos t`, `y = b sin t` with `a = √(1−c)`, `b = 1`.
Its arc length from `t = 0` to `t = φ` is `E_c(φ)` **[symbolic]** (verified to `0.0` residual at
40 digits, `X1-01` part (D)). Substitute `z = sin θ` in the defining integral:

  `E_c(φ) = ∫₀^{φ} √(1−c sin²θ) dθ = ∫₀^{sin φ} √(1−c z²)/√(1−z²) dz`.   (★)

The right side has an **algebraic** integrand and an upper limit `sin φ`. If the plane endpoint is
algebraic in `u`, then `sin φ` is algebraic in `u`, and (F3) gives D-finiteness. Script check: at
`c = 0.37`, `u = 0.8`, `E(arcsin(u/2), c) = ∫₀^{u/2} √(1−cz²)/√(1−z²) dz` to `0.0` residual, and its
derivative is the algebraic function `½√(1−cu²/4)/√(1−u²/4)` to `0.0` residual. So this function is
D-finite (indeed `F'' = R(u) F'` for a rational `R`). **The moving-endpoint step of the test is
correct for algebraic endpoints.**

### 3.2 `offset` does not escape

For a regular plane curve with unit tangent `t`, unit normal `n`, speed `v = |γ'|` and signed
curvature `κ`, the offset `γ_d = γ + d n` satisfies

  `γ_d' = v(1 − dκ) t`,   so   `speed γ_d = v |1 − dκ|`.   **[symbolic]**

Script `X1-02-offset.py` verified this to 40 digits on a circle (`resid 0.0`) and an ellipse
(`resid ≤ 2.3·10⁻⁴¹`). Consequentially the offset arc length is

  `∫ v |1 − dκ| dt = E_c(φ) − d·(turning angle) + O(…)`,

verified at 40 digits (`resid ≤ 2.3·10⁻⁴¹`) for four `(c,d)` pairs; over a full closed convex
curve this is the classical parallel-curve perimeter `P − 2πd` (Steiner), also verified at 40 digits
(`resid ≤ 9.2·10⁻⁴¹`) for four `(c,d)` pairs. Since the parallel curve of an algebraic curve is
algebraic, `v(1−dκ)` is an algebraic differential, so (F3) still gives D-finite fixed-endpoint
lengths. `offset` adds a curvature term but no first-kind capability, matching the remark in
`Pptc/Jacobi.lean`'s outlook that `offset` alone adds only `−d` times the turning angle.

### 3.3 The sine curve is the canonical transcendental escape

For `y = A sin(Bx)` on `[0, X]`,

  `L = ∫₀^X √(1+A²B²cos²(Bx)) dx = (√(1+A²B²)/B)·E(XB, m)`,   `m = A²B²/(1+A²B²)`,
  **[symbolic]**, verified to `0.0` residual at 40 digits (`X1-01` part (D)).

When `A, B, X` are allowed to depend on `u`, *both* the modulus and the angle move, and `L(u)` is
an incomplete elliptic integral of the second kind with moving modulus: generically not D-finite
(§2.2). A full period (`XB` a fixed multiple of `π/2`) collapses to a complete `E` of an algebraic
function of `u` and *is* D-finite; it is the **partial** arc (moving angle) that escapes.

## 4. The escape witness: a constructible length that is not D-finite

The ellipse arc with a transcendental endpoint is legal in `Defs.lean` and yields a non-D-finite
length. Construction tree in the move language of `Defs.lean`:

1. `c ∈ (0,1)` P-constructible (given). `sub`: `1−c`; `sqrt` (known black box from `Pptc.Basic`)
   gives `a := √(1−c)` P-constructible.
2. `ellipse(0,0, 2a, 2)` with `width = 2a > 0`, `height = 2 > 0` is
   `PConstructibleCurve` (`Defs.lean:172`); call it `S`.
3. Trace `γ(t) = (a cos t, sin t)`, parameters `a = 0`, `b = u`.
   * `hsub`: `((a cos t)²)/a² + (sin t)² = 1`, so `γ '' Icc 0 u ⊆ S`, for `0 ≤ u ≤ π`.
   * `hinj`: `cos` is injective on `[0,π]`, so `γ` is injective on `Icc 0 u`.
   * `hdiff`: `sin`, `cos`, and constant multiples are differentiable.
   * `hint`: `speed γ = Δ_c` is continuous, hence interval-integrable.
   * endpoints: `γ(0) = (a,0)`; `γ(u) = (a cos u, sin u)`. Both coordinates are P-constructible:
     `a`, and `cos u`, `sin u` are black boxes (`Pptc.Basic`), and products of P-constructible
     numbers are (constructor `mul`).
4. `PConstructible.arc_length S γ (a=0) (b=u) …` gives `PConstructible (arcLengthOf γ 0 u)`.

And `arcLengthOf γ 0 u = ∫₀^u Δ_c(t) dt = E_c(u)` **[symbolic]**, which by §2.2 is **not**
D-finite (branch points at `u = arcsin(1/√c) + kπ`). This is a legal `PConstructible` number whose
defining length is non-D-finite, so the D-finite test genuinely cannot exclude measured-length
constructions of this shape. The same tree with endpoint `u` replaced by a purely algebraic
eccentric angle (endpoint `sin φ` algebraic in `u`) *is* D-finite, by §3.1.

### 4.1 Reusing a measured length as a later shape parameter

The same objection applies to the brief's "using the output of one measurement as a shape
parameter of the next": (F3) needs the shape parameter to be *algebraic* in `u`, and a measured
length generally is not. For example, feeding the ellipse length `E(u,c)` back in as a semi-axis
`b(u) = E(u,c)` of a second ellipse makes the second length a function of a non-D-finite function;
there is no reason for it to be D-finite and (F3) cannot be invoked. A construction of this shape
could in principle cancel the transcendental dependence against a boundary term, and the test says
nothing about it. No such cancellation was found (R3 §2.4 (F-i) is the same loophole).

## 5. Moving-modulus `E`/`F` candidates (Q2) **[numeric]**

Candidate family, all functions of `u`: `am(u,c) =? a1 E(φ,m) + a2 F(φ,m) + a3 u + a4`, with
`E,F` the incomplete Legendre integrals in the candidate modulus `m`, and `φ = b u` (so this
includes the sine-curve-moved and moving-ellipse-axis shapes). Script `X1-03-candidates.py` fitted
the 4- and 6-constant versions by least squares on an interior grid and evaluated **off-grid**:

  c=0.09: 4-param train `9.8·10⁻⁷`, off-grid `1.5·10⁻¹`; 6-param train `1.5·10⁻⁷`, off-grid `1.5·10⁻¹`;
  c=0.30: 4-param train `1.1·10⁻⁴`, off-grid `1.4·10⁻¹`; 6-param train `3.8·10⁻⁶`, off-grid `1.4·10⁻¹`;
  c=0.70: 4-param train `8.8·10⁻⁴`, off-grid `1.3·10⁻¹`; 6-param train `2.0·10⁻⁴`, off-grid `1.1·10⁻¹`.

Training residuals fall (the family overfits) but the off-grid residual plateaus at `≈0.1`: no
identity. A 30-dps `mpmath` spot re-check of the 4-param fit at `c=0.09` gives
`|am − model| ≈ 3·10⁻⁷` — a fit artefact, not a zero.

**Why (derivative analysis).** Let `am(u,c) = a1(u) E(φ(u),m(u)) + a2(u) F(φ(u),m(u)) + a3(u)`.
Differentiating and using DLMF 19.4.5–19.4.6 (verified to 30 digits in `X1-04-dlmf-derivs.py`,
residuals `≤ 2·10⁻³¹`):

  `∂E/∂k = (E−F)/k`,   `∂F/∂k = (E − k'²F)/(k k'²) − k sinφ cosφ/(k'² Δ)`,   `k'² = 1−m`,

the total coefficient of `E` in `dn_c(u)` is `a1' + (m'/(2m))a1 + (m'/(2m(1−m)))a2` and that of `F`
is `a2' − (m'/(2m))(a1+a2)`. Setting both to zero removes the elliptic functions from the right
side and leaves `dn_c(u) =` an algebraic expression in `u`. But `dn_c` is not algebraic (it is a
non-elementary elliptic function), so this fails unless `φ` or `m` is already built from `am_c`
(e.g. `φ = am_c(u)`, or `φ = ellipticEAm_c(am_c(u))`), which is circular. This is the precise
sense in which the moving-modulus route is blocked; it is the same conclusion as R3's loophole L1,
reached by the derivative rather than the composition test.

## 6. Integral representations (Q3)

DLMF §22.16(i), https://dlmf.nist.gov/22.16 , lists for the amplitude:

* `am(x,k) = ∫₀^x dn(t,k) dt` (22.16.3) — the integrand `dn` is the unknown itself, so this is the
  defining relation, not an element-ary-integrand construction;
* the Fourier series `am(x,k) = (π/(2K))x + 2Σ_{n≥1} (qⁿ sin(2nζ))/(n(1+q^{2n}))` (22.16.9) — an
  **infinite** sum, whereas constructions are finite trees, and the nome `q` is transcendental in
  `c`;
* the special values `am(x,0)=x`, `am(x,1)=gd(x)` (22.16.4–5) at the excluded endpoints `c=0,1`.

The epsilon-function integral representations (22.16.14–23) are all of Jacobi functions or have
`sn(x,k)` as a limit, e.g. `ℰ(x,k) = ∫₀^{sn(x,k)} √((1−k²t²)/(1−t²)) dt`; none gives `am` as a
finite integral of an elementary integrand with constructible limits. MathWorld's "Jacobi
Amplitude", https://mathworld.wolfram.com/JacobiAmplitude.html , records only the same `∫dn`.
No usable representation was found.

## 7. Two measurements and arithmetic (Q4) **[symbolic]**

D-finite functions are closed under `+ − × ÷`, algebraic substitution, and antiderivatives (F2), so
any arithmetic combination of D-finite lengths is D-finite and cannot be `am`. Two distinct
non-D-finite lengths can cancel to something finite, so no general exclusion applies to
`L₁(u) − L₂(u)`. Differentiating a combination of fixed-curve lengths with moving endpoints,

  `(L₁−L₂)'(u) = [σ₁(b₁)b₁' − σ₁(a₁)a₁'] − [σ₂(b₂)b₂' − σ₂(a₂)a₂']`  (curves independent of `u`),

is elementary in `u`; since `dn_c` is not, no difference of two fixed-curve lengths can be `am`.
When the curves themselves move with `u`, the extra terms `∫ ∂_u σᵢ dt` appear and can be
non-elementary — this is the surviving loophole, already ranked first in R3 §6, and no candidate
was found. The cheapest escape is a *single* partial arc with a transcendental endpoint, the ellipse
witness of §4.

## 8. The precise negative statement

**Excluded class.** Let `𝒟` be the set of real functions of `u` that can be written as a finite
arithmetic expression (using `+ − × ÷`, algebraic substitution) in arc lengths of the *algebraic*
constructor families (ellipse, rectangle boundary, polynomial graph, power law, cubic Bézier, and
their `translate`/`scale`/`rotate`/`restrict`/`offset` images) in which **every shape parameter and
each traced endpoint is an algebraic function of `u`**. Every element of `𝒟` is D-finite, so no
element of `𝒟` equals `am(u,c)` (which is not D-finite). This is a genuine partial negative result
for exactly that fragment.

**Which assumption would let a construction through.** One transcendental dependence on `u`
anywhere in the data suffices: a `sine`/`exp_two` base curve, an endpoint or shape parameter built
with `sin`, `cos`, `tan`, `2^{·}`, `log`, `arccos`, or `ellipticEAm c ·`. `Defs.lean` permits all
of these (they are among the already-known P-constructible black boxes), and §4 exhibits a legal
construction in that fragment whose length is not D-finite. The D-finite test therefore cannot rule
out measured-length constructions in general; it only proves that they must use the transcendental
fragment.

## 9. Scripts, sources, verification

**Scripts** (`archived files/jacobi-scripts/`):

| script | contents |
|---|---|
| `X1-01-dfinite-basics.py` | complete `K`/`E` ODEs; incomplete `E`/`F` branch points and exponents; `dn` pole lattice; ellipse & sine arc-length calibration |
| `X1-02-offset.py` | offset speed factor `|1−dκ|`; offset arc length = `E_c(φ) − d·(turning)`; Steiner perimeter `P − 2πd` |
| `X1-03-candidates.py` | moving-modulus `E`/`F` vs `am`, least-squares + off-grid + 30-dps re-check |
| `X1-04-dlmf-derivs.py` | DLMF 19.4.5–19.4.6 calibration; `E`/`F` coefficient cancellation analysis |

**Sources:** DLMF §19.4 (derivatives), https://dlmf.nist.gov/19.4 ; DLMF §22.4 (poles),
https://dlmf.nist.gov/22.4 ; DLMF §22.16 (amplitude, epsilon, Fourier series),
https://dlmf.nist.gov/22.16 ; Wolfram `JacobiAmplitude` branch cuts,
https://reference.wolfram.com/language/ref/JacobiAmplitude.html ; MathWorld "Jacobi Amplitude",
https://mathworld.wolfram.com/JacobiAmplitude.html ; Sattelberger–Sturmfels, *D-Modules and
Holonomic Functions*, arXiv:1910.01395; Flajolet–Sedgewick, *Analytic Combinatorics*, Note VI.9.
`Pptc/Defs.lean` (constructors, line 148 `arc_length`, line 172 `ellipse`, line 372 `offset`),
`Pptc/Jacobi.lean` (outlook, lines 687–751), `Pptc/ThirdKind.lean` (third-kind identities) for the
Lean-level facts cited.

**Independent re-check.** All numeric claims were produced by the four archived `X1-` scripts under
`mp.dps = 30–40`; the decisive ones (complete `K`/`E` ODEs; `dn` pole residues; ellipse and sine
arc-length identities at `0.0` residual; DLMF 19.4.5–19.4.6) were re-run from scratch. The
`X1-03` off-grid residual is representative (`≈10⁻¹`), not a knife-edge measurement.
