# NOTES-jacobi-R1b — arc lengths of polynomial / Bézier / power-law chains

Research task R1b (`PLAN-jacobi-R1b-polynomial-chains.md`), scope: bases `poly_graph`
(rational coefficients, degree ≤ 6), `cubic_bezier` (constructible control points), `power_law`
`y = a x^b` (rational `a, b`), under `translate/scale_x/scale_y/rotate`, `restrict`, and `offset`.
Ellipse bases are R1a; `sine` and `exp_two` are R1c.

**Question.** Is there a curve in this class whose arc length is exactly `α·F(φ(T), c) + β`
with **no boundary term**, for some `c ≠ 0`? Here `F(φ,c) = ∫₀^φ dθ/√(1 − c sin²θ)` is the
Legendre first-kind integral.

**Verdict (short).** **No**, for the single-curve route with an *algebraic* reparametrisation.
Every non-degenerate base in scope is an unbounded algebraic curve, and its arc-length
differential `ds` has an unavoidable pole at a point at infinity (or a cusp of the offset) and,
after the abelian-integral decomposition, a non-zero non-first-kind part. The two power-law
families that do reduce to Legendre form (`b = 3`, `b = 5/2` and their relatives) are
first-kind **plus** an explicit boundary term `x√(1+kx^n)`, exactly as in fact F2. The
degree-count obstruction is confirmed, not broken. This is a **useful negative**, not a
breakthrough. Assumptions and loopholes are stated in §5.

All scripts are in `archived files/jacobi-scripts/`. Every identity below is labelled
**[symbolic]** (an exact polynomial/rational identity verified by `sympy`) or **[numeric]** (a
`mpmath` evaluation at ≥ 30 dps; residuals are printed and are at the level of the working
precision, i.e. ≤ ~1e-29).

---

## 0. Notation and the general shape of `ds`

For a parametric curve `γ(t) = (x(t), y(t))`, `v = γ'`, `a = γ''`, `P₀ = |v|²`, `W = v × a =
v_x a_y − v_y a_x`. The offset at signed distance `d` (unit normal `i v/|v|`, as in
`Defs.unitNormal`) has velocity

```
γ_d'(t) = v(t) · (1 − d·W(t)/P₀(t)^{3/2}),                            (0.1)
```

and a subsequent linear map `A` gives

```
speed = |1 − d·W/P₀^{3/2}| · √(P(t)),   P(t) = |A v(t)|².             (0.2)
```

For the bases in scope, `v` is polynomial (degree ≤ 5 for a degree-6 graph, 2 for a cubic
Bézier, rational for a power law), so `P` and `P₀` are polynomials (a quartic for a cubic
Bézier) and `W` is polynomial.

Writing `ds = R(t)·√(P(t)) dt = R'(t) dt / y` on the hyperelliptic curve `y² = P(t)` with
`R' = P·R`:

```
ds is holomorphic first kind  ⟺  R'(t) is a polynomial of degree ≤ g−1,  (g = genus).  (0.3)
```

For a genus-1 quartic `P` the holomorphic differentials are `(α + βt) dt/y`; so we need `P·R`
to be **linear** in `t`. (The brief's phrasing "`P·R` can never be constant" is the special
case of this; both constant and linear are killed by the same degree count.)

---

## 1. Power laws `y = a x^b`

`ds = √(1 + a²b² x^{2b−2}) dx`, a binomial differential with `k = a²b²`. Put `r = 2b − 2 = P/Q`
in lowest terms (`Q > 0`). The substitution `x = u^Q` gives

```
ds = Q u^{Q−1} √(1 + k u^P) du,
```

whose associated algebraic curve is `y² = 1 + k u^P` with genus `g = (|P|−1)/2` (`|P|` odd),
`(|P|−2)/2` (`|P|` even). Chebyshev's theorem (m = Q−1, n = P, p = 1/2) says the integral is
elementary iff `(m+1)/P ∈ ℤ` or `(m+1)/P + 1/2 ∈ ℤ`.

**Enumeration** (script `R1b-01-powerlaws.py`, **[symbolic]** exact rational arithmetic).
With `|num|, den ≤ 12` there are 18 distinct **elliptic** exponents (genus 1 and
non-elementary), grouped by the numerator `|P|` of `2b−2`:

| curve | `j`-invariant | exponents `b` |
|---|---|---|
| `y² = 1 + k u⁴` (lemniscatic) | `j = 1728` | `−1, 1/3, 3/5, 5/7, 7/9, 9/11, 11/9, 9/7, 7/5, 5/3, 3` |
| `y² = 1 + k u³` (equianharmonic) | `j = 0` | `−1/2, 1/4, 5/8, 7/10, 11/8, 7/4, 5/2` |

So although there are 18 exponents, there are only **two underlying elliptic curves**: the
lemniscatic one (`λ = 1/2`, `j = 1728`) and the equianharmonic one (`λ = 1/2 ± i√3/2`, `j = 0`).
The cross-ratio and `j` values were computed exactly with `sympy` in `R1b-02-legendre.py`
(**[symbolic]**); e.g. `1+kt⁴` gives `λ = 1/2`, `j = 1728` for every `k`, and `1+kt³` gives
`j = 0` for every `k`, as it must since scaling `u` is a Möbius reparametrisation.

**Clean representatives (`Q = 1`).**

* `b = 3` (so `n = 4`, `k = 9a²`): **[symbolic]** exact boundary decomposition
  ```
  ∫√(1+kx⁴) dx = (1/3) x√(1+kx⁴) + (2/3) ∫ dx/√(1+kx⁴).              (1.1)
  ```
  Both coefficients are non-zero; at `a = 1` (`k = 9`) this is exactly F2. **[numeric]** residual
  `0` at 30 dps.

  First-kind reduction: with `u = (1−σ²)/(1+σ²)`, `σ = k^{1/4}x`,
  ```
  ∫₀^x dt/√(1+k t⁴) = k^{−1/4} · (1/√2)[ K(−1) − F(arcsin u, −1) ].
  ```
  **[numeric]** residual `1.97e−31` at 30 dps for `k = 9`, `x = 1.3`. The Legendre modulus is
  `m = −1` (`k_leg = i`); equivalently, after a Landen step, the real modulus `m = 1/2`. Verified
  independently by the period ratio `K(1/2)/K'(1/2) = 1` **[numeric]** (lemniscatic fixed point of
  the Landen transformation).

* `b = 5/2` (so `n = 3`, `k = 25a²/4`): **[symbolic]** exact boundary decomposition
  ```
  ∫√(1+kx³) dx = (2/5) x√(1+kx³) + (3/5) ∫ dx/√(1+kx³).              (1.2)
  ```
  **[numeric]** residual `0` at 30 dps. The first-kind part lives on the equianharmonic curve;
  its Legendre modulus is `m₀ = (2+√3)/4 ≈ 0.9330127019` **[numeric]**, verified by the period
  ratio `K'(m₀)/K(m₀) = 1/√3` and by `j = 0` **[symbolic]**.

**`Q > 1` cases.** For `b = 1/3` (`r = −4/3`) one has `x = u³` and `ds = 3√(u⁴ + k) du`: the
same lemniscatic first-kind integral plus the same boundary term. For `b = 1/4` (`r = −3/2`),
`x = u²` gives `ds = 2u^{−1/2}√(u³+k) du`, the equianharmonic integral with a boundary term.
The same integration-by-parts applies to every `Q > 1` case (Chebyshev's reduction), so no
`Q > 1` exponent removes the boundary. **[symbolic]** (substitutions are exact; not re-verified
case by case).

**Step-1 conclusion.** Every elliptic power-law arc length is a fixed first-kind integral on one
of two curves **plus a non-zero algebraic boundary term** — the same "`s − B`" obstruction as F2.
No power law in scope has a pure first-kind arc length.

---

## 2. Pythagorean-hodograph cubic Béziers

A cubic Bézier is PH iff `|γ'|² = σ(t)²` with `σ` a polynomial (here quadratic). Then
`W = γ' × γ'' = σ² θ'` and (0.1) gives, for the offset and a following linear map `A`,

```
ds = √(P(t)) · R(t) dt,   P = |A γ'|²  (quartic),   R = 1 − d·W/σ³.   (2.1)
```

The offset alone (`A = I`) has speed `|σ − dW/σ²| = |σ³ − dW|/σ²`, a **rational** function, so
its arc length is elementary. A *linear image* (`A` ≠ similarity) is where the quartic and the
genus-1 differential enter.

**Concrete check (Tschirnhausen cubic),** script `R1b-03-ph.py`. `γ(t) = (t − t³/3, t²)`,
`γ' = (1−t², 2t)`, `σ = 1+t²`, `W = 2(1+t²)`. With `d = 3/10`,
`A = [[2, 1/5],[1/3, 3/2]]`:

* `P(t) = 37t⁴/9 − 18t³/5 + 211t²/225 + 18t/5 + 37/9` (quartic, not a square) **[symbolic]**;
* `R(t) = ((1+t²)² − 3/5)/(1+t²)² = (5t⁴+10t²+2)/(5(1+t²)²)`, `R(∞) = 1` **[symbolic]**;
* **[numeric]** `speed − |R|√P = 0` (or `≤ 1.6e−30`) at 30 dps, at `t = 0.3, 1.4, 2.7, −1.1`.

**Degree count / pole at infinity.** As `t → ∞`, `P(t) ~ (37/9) t⁴` and `R(t) → 1`, so

```
P(t)·R(t) ~ (37/9) t⁴   at infinity.                                  (2.2)
```

This is degree 4, so `P·R` is **neither constant nor linear**; by (0.3), `ds` is not the
holomorphic differential `(α+βt)dt/y` of its own curve. In local coordinates `u = 1/t` at the
point at infinity, `ds = √P dt ~ −(37/9)^{1/2} u^{−4} du`: an **order-4 second-kind pole**.
Hence the abelian integral `s(T)` has a non-zero second-kind component and cannot be a pure
first-kind `F` under an algebraic reparametrisation. The brief's degree-count argument is
therefore **correct** (with "linear" in place of "constant", which only strengthens it).

**Depth-2 chain** (offset, map, offset, map) `R1b-03-ph.py`. The intermediate curve
`C₁ = A·γ_d` is rational, so the second offset is again rational and the final linear image has
a speed of the form `√(P₂)·R₂` with `P₂` quartic. **[numeric]** the depth-2 speed grows like
`t²` at large `t` (values at `t = 0.5, 2, 6` are `3.25, 14.71, 189.87`), i.e. the same
second-kind pole at infinity. No depth-2 choice removes it.

---

## 3. General cubic Bézier + one offset + one linear map

Script `R1b-04-general.py`, non-PH control points `(0,0), (1,2), (3,−1), (4,1)`, `d = 7/20`,
`A = [[6/5, 1/4],[−1/3, 4/3]]`. Here `v = γ'` is quadratic, `a = γ''` linear, `P₀ = |v|²` and
`P = |Av|²` are quartics, `W = v × a` is quadratic (degree-3 terms cancel for a cubic Bézier).

* `P₀(t) = 936t⁴ − 1872t³ + 1260t² − 324t + 45` **[symbolic]**, no real root in `[0,1]`;
* `P(t) = (176409t⁴ − 352818t³ + 235515t² − 118212t + 7501)/100` **[symbolic]**;
* **[numeric]** `speed − |1 − dW/P₀^{3/2}|√P ≤ 1.3e−29` at 30 dps, `t = 0.2, 0.6, 1.5, −0.8`.

On `y² = P` the differential is `ds = R'(t) dt / y` with

```
R'(t) = P(t)·(P₀(t)³ − d·W(t)) / P₀(t)³.                              (3.1)
```

At infinity `P/t⁴ → 176409/100` and `W/P₀³ → 0`, so `R'(t) ~ (176409/100) t⁴`: a **degree-4**
rational function. By (0.3), `ds` is not first kind; the abelian integral is not a pure `F`.

**Cusps.** If `v(t₀) = 0` (a cusp of the Bézier), then `P₀ ~ |u|²(t−t₀)²`, `P ~ |Au|²(t−t₀)²`
and `W ~ ½(u×z)(t−t₀)²`, where `u = ½v''(t₀)`, `z = v'''(t₀)`. Hence
`1 − dW/P₀^{3/2} ~ −d(u×z)/(2|u|³(t−t₀))` while `√P ~ |Au|·|t−t₀|`, so the **speed stays
finite** at the cusp. Cusps do not create a pole; the only pole is at infinity. (Our example has
no real cusp in `[0,1]`.)

**Answer to the brief's step-3 question.** No parameter choice removes both the exact and the
second-kind part: the exact part is non-zero by (3.1) unless `P·R'` is (degree ≤ 1) polynomial,
and (3.1) is degree 4 at infinity. Even the `d = 0` case (linear image of a PH cubic) gives
`R' = P²`, degree 8. Only a *similarity* `A = λR` makes `P = λ²P₀` a perfect square, dropping to
genus 0 — but then the arc length is elementary (no `F` at all), which is worse for the purpose.

---

## 4. Pole at infinity, bounded sub-arcs, and non-algebraic φ

Script `R1b-05-pole.py`.

**(4.1) Unbounded bases have a pole at infinity.** For `poly_graph y = p(x)` of degree `d ≥ 2`,
`ds = √(1+p'(x)²) dx`; at infinity `√(1+p'(x)²) ~ |lead(p')| x^{d−1}`. For `y = x⁶` this is
`~ 6x⁵ dx`; with `w = 1/x` (so `ds = y dx` on `y²=1+36x^{10}`), `ds ~ −6 w^{−7} dw`: an
**order-7 second-kind pole** **[symbolic]**. The tail integral `∫_N^{2N}√(1+9x⁴)dx ~ 7N³`
**[numeric]** (`/N³ = 7.000008, 7.0000000008, 7.0` for `N = 10, 100, 1000`). For a power law
`b = 5/2`, at the branch point at infinity (`x = 1/w²`, `y = 1/w³`) `ds = y dx ~ −2 w^{−6} dw`,
while the first-kind form `dx/y ~ −2 dw` is holomorphic: `ds` is genuinely **not** first kind
**[symbolic]**.

**(4.2) The second-kind part can be *exact* — that is the boundary term.** For `y = x³`,
```
√(1+9x⁴) dx = (2/3) dx/√(1+9x⁴) + d[ x√(1+9x⁴)/3 ],   fk-coefficient 2/3 ≠ 0,
```
**[symbolic]** residual `0`, **[numeric]** window residual `−3.16e−30`. So the pole at infinity
does *not* by itself prevent `s(T) = αF + (exact)`; the exact part is exactly the boundary term
of F2. What it prevents is a pure `F`: `ds` is not holomorphic, and no exact form can be added
to make it holomorphic without already being the first-kind differential, which (0.3) forbids.

**(4.3) Bounded sub-arcs do not help.** `restrict` changes the domain of integration, not the
differential. The order-4 pole of `√(1+9x⁴)dx` at infinity is a property of the differential on
the curve; integrating over `[0,1]` instead of `[0,∞)` does not remove it from the abelian
integral's class. **[numeric]** the same boundary decomposition holds on any window, e.g.
`[0.3, 2.7]` residual `−3.16e−30`. A bounded arc of an unbounded curve is still governed by the
same non-holomorphic differential.

**(4.4) Non-algebraic φ — the one loophole.** The obstruction in §2–4 uses: `s = αF(φ)+β` with
`φ` **algebraic** in the curve's parameter, so `ds = α dφ/√(1−c sin²φ)` is the pull-back of a
holomorphic 1-form under a morphism of compact curves, hence holomorphic. This fails if `φ` is
not algebraic. The constructors do not supply an arbitrary non-algebraic `φ`: `translate`,
`scale`, `rotate`, `offset` are algebraic, and `arc_of_length` is the *inverse* of an arc-length
function, i.e. it inverts `s` rather than reparametrising another curve by a freely chosen
transcendental map. So within the constructor language the loophole is not realised for the
single-curve route. It is exactly the composition route (integrating/inverting **several**
curves, R3) that this argument does **not** cover.

---

## 5. Verdict, assumptions, loopholes

**Verdict.** No curve built from `poly_graph` (deg ≤ 6), `cubic_bezier`, or `power_law` by
linear maps, translations, `restrict` and `offset` has arc length `α·F(φ,c)+β` with **no
boundary term**, for any `c ≠ 0`, assuming the reparametrisation `φ` is algebraic. This is the
same `s − B` obstruction isolated in F2, and it is generic: it is a pole of the arc-length
differential at a point at infinity (or at an offset cusp), surviving the offset and linear-map
operations.

**Assumptions used.**
1. The curve is the image of a polynomial/rational parametrisation with `v` polynomial of degree
   ≥ 1; so `P₀, P` are polynomials and `ds` is a meromorphic differential on `y² = P`.
2. `P` is not a perfect square (else genus 0, arc length elementary — no `F`).
3. `φ` is algebraic (so the pull-back of the Legendre holomorphic form is holomorphic).
4. `c ≠ 0` (for `c = 0`, `F(φ,0) = φ` and the "first-kind" integral degenerates to an
   elementary one, so the question is vacuous; `c = 0` is constructible by other means).

**Loopholes explicitly not covered.**
* **Non-algebraic reparametrisations** (§4.4). The constructors do not provide one on a single
  curve, but a multi-curve composition (R3) could.
* **Exact cancellation between two different curves.** `inter_x`/`inter_y` combine two curves;
  it is conceivable that the exact (boundary) parts of two different arc lengths cancel and only
  first-kind parts survive. Nothing here rules that out; it is a composition phenomenon.
* **Degenerate images that happen to be bounded conics/ellipses** (a cubic Bézier cannot lie on
  a conic because polynomial parametrisations of a non-degenerate conic do not exist, but
  rational Béziers or ellipse bases can). Ellipse bases and their offsets belong to R1a.
* **The forward direction.** F2/`ellipticF_Pconstructible` already produce `F` *forwards* as
  Bézier arc length minus a multiple of `E` minus a boundary term; nothing here contradicts
  that, and no new forward representation is found.

**No breakthrough.** The single-curve route is closed for this scope. Any positive answer must
come from the composition route (R3) or from a non-algebraic base family (R2's Serret
constructor).

---

## Appendix — scripts and verification ledger

| script | contents | status |
|---|---|---|
| `R1b-01-powerlaws.py` | Chebyshev/genus enumeration of `2b−2 = P/Q`, `|num|,den ≤ 12` | symbolic (exact rationals) |
| `R1b-02-legendre.py` | cross-ratio/`j` of `1+kt⁴` (`j=1728`) and `1+kt³` (`j=0`); boundary decompositions; `P=4` Legendre reduction | symbolic + numeric (residuals 0, `1.97e−31`) |
| `R1b-03-ph.py` | Tschirnhausen PH offset + map; `ds=√P R dt`; degree count; depth-2 growth | symbolic + numeric (residuals ≤ `1.6e−30`) |
| `R1b-04-general.py` | non-PH cubic Bézier + offset + map; speed formula; `R'` degree; cusp analysis; F2 recheck | symbolic + numeric (residuals ≤ `1.3e−29`) |
| `R1b-05-pole.py` | pole orders at infinity for `x⁶` and `b=5/2`; exact boundary on a finite window | symbolic + numeric (residuals ≤ `3.2e−30`) |

Key identities and their status:

| identity | status |
|---|---|
| `∫√(1+kx⁴)dx = (1/3)x√(1+kx⁴) + (2/3)∫dx/√(1+kx⁴)` | symbolic; numeric residual `0` |
| `∫√(1+kx³)dx = (2/5)x√(1+kx³) + (3/5)∫dx/√(1+kx³)` | symbolic; numeric residual `0` |
| `∫₀^x dt/√(1+kt⁴) = k^{−1/4}·(1/√2)[K(−1) − F(arcsin u,−1)]`, `u=(1−σ²)/(1+σ²)` | numeric residual `1.97e−31` |
| `j(1+kt⁴) = 1728`, `j(1+kt³) = 0` for all `k` | symbolic (exact cross-ratio) |
| `K(1/2)=K'(1/2)`, `K'(m₀)/K(m₀)=1/√3`, `m₀=(2+√3)/4` | numeric |
| PH offset+map: `ds = √P·R dt`, `P·R ~ (37/9)t⁴` | symbolic + numeric residual `0` |
| general cubic+offset+map: `ds/dt = |1−dW/P₀^{3/2}|√P` | symbolic + numeric residual ≤ `1.3e−29` |
| `√(1+9x⁴)dx = (2/3)dx/√(1+9x⁴) + d[x√(1+9x⁴)/3]` | symbolic; numeric residual `0` |
| `∫_N^{2N}√(1+9x⁴)dx ~ 7N³` | numeric |
