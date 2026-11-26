# Generalizations: where a specific result is one point of a larger reachable family

Written 2026-11-26. Research note only: no `.lean` file was changed.

Each section takes a result the repo proves for specific targets, names the larger family that
the same mechanism reaches, and says what the Lean statement would need. Labels:
**[Computed, n digits]** means checked numerically in `scripts/generalizations_checks.py` (labels
C1–C10 match the script); **[Proof sketch]** means argued here but not checked;
**[Literature]** means classical and not re-checked; **[Open]** means no route is known.

## 0. Summary

| # | proved today | larger family | what it needs | effort |
|---|---|---|---|---|
| 1 | `Gamma_rat_Pconstructible` (via `ℓ(σ)` at one endpoint) | incomplete Beta `B_T(p,q)`, `p ∈ ℚ>0`, `p+q ∈ ½+ℤ`, any P-constructible `T ∈ [0,1)` | generalize `ArcLength` / `Substitution` to a variable endpoint; contiguity | small–medium |
| 1′ | `hyp_neg_half_arcLength_Pconstructible` (`n ≤ 6`, `\|z\| < 1`) | `₂F₁(−½, p; 1+p; z)` for every rational `p > 0` and every `z ≤ 0` | `power_law` instead of `poly_graph`; Pfaff form outside the disc | small |
| 2 | `arcLengthOf_affineImageGraph_pow_Pconstructible` (a length, unidentified) | Appell `F₁(p; −½, −½; 1+p; ζ, ζ̄)`, a two-parameter family | identify the length; state for rational exponents | medium |
| 3 | `hyp_elliptic_class_…`, `hyp_graphFamily_class_…` (two separate inductions) | one theorem: seed `F`, `F′` ⇒ whole contiguous lattice | generic lattice induction | medium |
| 4 | Clausen at `(¼,¼)`; Goursat at specific seeds | Clausen/Goursat on every reachable `(a, b; a+b+½)` seed, e.g. `₃F₂(1, 2p, p+½; 2p+1, p+1; z)` | Clausen for general `(a, b)` | medium |
| 5 | beyond `p+q ∈ ½+ℤ` | genus-1 incomplete Betas, e.g. `B_T(⅓,⅓)` | reduction of a genus-1 differential to Legendre form | research |
| 6 | Watson/Pólya constants (single numbers) | lattice Green functions `G(t)` at every P-constructible `t` | bcc is one line; sc/fcc need Joyce's formulas | small (bcc) |
| 7 | Dottie, Laplace limit, `W` | Kepler's equation for all `(e, M)`; generalized Lambert `eˣ = (ax+b)/(cx+d)` | packaging `crossing_Pconstructible` | small |

The organizing idea for the hypergeometric track (§3–§4) is a single reachable set
`HypReach ⊆ ℝ⁴` of parameter tuples where `₂F₁` and its derivative are P-constructible, with
closure lemmas (contiguity, Pfaff, Goursat, Clausen) and a short list of seeds (§1′, §2,
elliptic, Gauss at 1). Most hypergeometric files in the repo then become a seed or a closure lemma.

---

## 1. Γ at rationals → incomplete Beta with half-integer total

**Your question, answered.** Yes, it is `₂F₁` at `z = −1`. The arc length the Γ chain measures is

```
ℓ(σ) = ∫₀¹ √(1 + x^σ) dx = ₂F₁(−½, 1/σ; 1 + 1/σ; −1)          [Computed, 40 digits]  (C1)
A(σ) = ∫₀¹ dx/√(1 + x^σ)  = ₂F₁( ½, 1/σ; 1 + 1/σ; −1)          [Computed, 40 digits]  (C6)
```

and `Substitution.lean` turns `A(σ)` into the half-Beta `B_{1/2}(1/σ, ½ − 1/σ)`. So the whole Γ
development uses **one point** (`T = ½`) of a one-parameter family, for each `σ`, and then throws
the family away by summing two halves into a complete Beta.

**The family.** Lay the power law `y = A x^b` (`b = 1 + σ/2`, any P-constructible `A` by
`scale_y`) from the origin to any P-constructible `X > 0`. The far endpoint `(X, A X^b)` is
P-constructible (`rpow_Pconstructible`), so `arc_length` applies, and with `w = A²b²`,
`p = 1/σ`, `U = wX^σ`, `T = U/(1+U)`:

```
∫₀^X √(1 + w x^σ) dx = (1/σ) w^(−p) · B_T(p, −p − ½)              [Computed, 40 digits]  (C2)
                     = X √(1+U) · ₂F₁(−½, 1; 1 + p; T)             (Pfaff form, T ∈ [0,1))
```

C2 includes cases with `U > 1`, which the current `Graphs.lean` statement cannot reach.
Given a target `T ∈ (0,1)`, take `U = T/(1−T)` and `X = (U/w)^{1/σ}`; both are P-constructible.
So:

> **Theorem G1 (proposed).** For rational `p > 0`, rational `q` with `p + q ∈ ½ + ℤ`, and
> P-constructible `T ∈ [0, 1)`, the incomplete Beta integral
> `B_T(p, q) = ∫₀^T t^(p−1) (1−t)^(q−1) dt` is P-constructible.

*Proof sketch.* The arc gives `q = −p − ½`. The integer shifts come from the elementary
contiguity relations, whose boundary terms are `T^p (1−T)^q` (P-constructible by `rpow`):

```
B_T(p+1, q) = (p B_T(p,q) − T^p (1−T)^q) / (p+q)
B_T(p, q)   = B_T(p+1, q) + B_T(p, q+1)
```

(The divisor `p + q` is never 0 here because `p + q ∈ ½ + ℤ`.) Every rational `p > 0` arises
as `1/σ`, since `σ = 1/p` is a positive rational. ∎

In `₂F₁` language, `B_T(p,q) = (T^p/p) ₂F₁(p, 1−q; p+1; T)`, so G1 is the **reducible-monodromy
class** (`c − a ∈ ℤ`) whose other exponent difference at ∞, `b − a`, lies in `½ + ℤ`. That is
the precise sense in which "the Γ strategy, used generally" is a family of `₂F₁` values.

**Lean delta.**

- `GammaRational/ArcLength.lean` fixes the endpoint at `x = 1` and the coefficient at
  `(1 + σ/2)⁻¹`. Make both parameters.
- `Substitution.lean` already does the right change of variables. Generalize its upper limit
  from `½` to `T`, and keep the `integral_image_eq_integral_abs_deriv_smul` route, because the
  integrand is still unbounded at 0.
- Define `incBeta p q T := ∫ t in 0..T, t^(p−1) * (1−t)^(q−1)`; Mathlib has no incomplete Beta.
  `halfBeta` becomes `incBeta · · (1/2)`.
- `Gamma_rat_Pconstructible` then becomes a corollary (`T = ½`, plus reflection), not the
  endpoint.

**Why `½` and only `½`.** Every number `arc_length` returns is `∫ √(x′² + y′²)`, so the only
non-integer exponent the integrand can contain is `½`. On a power law, the radicand is `1 + w u`
in the atom `u = x^σ`. Escaping `p + q ∈ ½ + ℤ` therefore needs a source that is not a single
power-law arc: see §5.

**Also note.** `power_law` takes a rational exponent, and that is the only reason `p` is
rational. Whether any constructible curve has the shape `y = x^b` with `b` irrational is itself
a reachability question **[Open]**. Even with such a curve, `Doubling.lean` uses
`N ∣ 2^φ(N) − 1`, so the passage from Beta products to single Γ values is genuinely
rational-only.

### 1′. The graph family: drop `n ≤ 6` and `|z| < 1`

`Graphs.lean` / `GraphsClass.lean` prove `₂F₁(−½, 1/m; 1+1/m; −b²X^m)` P-constructible only for
`m = 2n−2` with `n ∈ {2..6}` (inherited from `poly_graph`) and `|b²X^m| < 1` (Mathlib's `hyp`
is junk outside the disc). Both restrictions are artefacts:

- `power_law` now includes the origin for positive exponents (the R1 question in
  `archive/PLAN-hypergeometric-00-overview.md` §4 H6 is closed), so every positive rational `m`
  is available, including non-integer `m`.
- Outside the disc, state the result in the Pfaff form `₂F₁(−½, 1; 1+p; T)` with
  `T ∈ [0,1)`. `Pfaff.lean` already proves the transformation on `(−1, ½)`.

> **Theorem G1′ (proposed).** For every rational `p > 0` and P-constructible `z ≤ 0`,
> `₂F₁(−½, p; 1+p; z)` (read through Pfaff when `z ≤ −1`), and its whole contiguous class,
> are P-constructible.

The derivative seed is free, as in `deriv_graphFamily_Pconstructible`: by the FTC it is an
elementary function of the endpoint.

---

## 2. Sheared power laws → Appell F₁ (a two-parameter family)

`arcLengthOf_affineImageGraph_pow_Pconstructible` proves that the length of an affine image
`t ↦ (at + bt^n + e, ct + dt^n + f)` is P-constructible, but it does not say *what* that length
is. The docstring in `Graphs.lean` calls it "a hyperelliptic integral rather than a ₂F₁ value".
That is true, but it can be sharper. The speed is `|z₁ + z₂ u|` with `u = t^s`, `s = n − 1`,
`z₁ = a + ic`, `z₂ = n(b + id)`. With `r = −z₁/z₂`:

```
∫₀^X speed = X |z₁| · F₁(1/s; −½, −½; 1 + 1/s; X^s/r, X^s/r̄)    [Computed, 17 digits]  (C3)
```

The numerical check used `n = 5/2`. Precision is limited by `quad` at the `t^{1/2}` cusp.

When `ad − bc ≠ 0`, `r` is never real: two squares vanish together only on a degenerate map.
So the arguments are always a **conjugate pair**, and the family has two real parameters
(`|X^s/r|` and `arg r`) for each rational `s`, against one for §1′. The `₂F₁` family is the
special case `arg r = π`, where `z₁ ∥ z₂`.

> **Theorem G2 (proposed).** For rational `p > 0` and every `ζ ∈ ℂ \ ℝ` with P-constructible
> real and imaginary parts and `|ζ| < 1`, `Re F₁(p; −½, −½; 1+p; ζ, ζ̄)` is P-constructible.

*Proof sketch.* Take `X = 1`, `z₁ = 1` (`a = 1`, `c = 0`) and `z₂ = −ζ`
(`b = −Re ζ / n`, `d = −Im ζ / n`). Then `r = 1/ζ`, so `X^s/r = ζ`, and the shear is
P-constructible. G2 drops the `n ≤ 6` restriction
for the same reason as §1′. It also needs `F₁` defined as a double series (Mathlib has none);
alternatively, state G2 as the integral and keep `F₁` in the docstring, as `Polya.lean` does
with its named identities.

The same inventory, run across every base curve, gives the **depth-one arc-length dictionary**:

| curve | speed | integral class |
|---|---|---|
| power law, scaled | `√(1 + w u)` | `₂F₁` / incomplete Beta (§1) |
| power law, sheared | `√(Q(u))`, `Q` quadratic with conjugate roots | Appell `F₁` (§2) |
| ellipse, cubic Bézier, `y = sin x` | `√(quartic)` | elliptic F, E, Π (already general: `ThirdKindAll`) |
| `y = 2^x` | `√(1 + c 4^x)` | elementary |
| offset of any of these | `arc − d·Δψ` (`OffsetInversion/Speed`) | same class plus an elementary turning-angle term |

That table is the "inbound" half of the hypergeometric programme. It says which special-function
families a single `arc_length` can produce at all.

---

## 3. One contiguous-closure theorem instead of two inductions

`EllipticClass.lean` (seed `(½, ½; 1)`) and `GraphsClass.lean` (seed `(−½, 1/m; 1+1/m)`) each
run a separate strong induction of several hundred lines over the same lattice
`(a+i, b+j; c+k)`. The one-step engine is already generic
(`hyp_contiguous_neighbours_Pconstructible`). What is missing is its lattice closure:

> **Theorem H (proposed).** Let `a, b, c, z` be P-constructible with `0 < |z| < 1` and generic
> parameters, where generic means none of `a+i, b+j, c+k−a−i, c+k−b−j` is `0` and
> `c + k ∉ −ℕ` along the lattice. If `₂F₁(a,b;c;z)` and `₂F₁′(a,b;c;z)` are P-constructible, then
> so is `₂F₁(a+i, b+j; c+k; z)` for all `i, j ∈ ℤ`, `k ∈ ℕ`.

The degenerate corners are exactly where the two existing files had to special-case: the
`j = k+1` corner in `GraphsClass`, and `c₀ − b₀ = 1`. The generic theorem should carry the
genericity hypothesis and let each instance discharge it. With H:

- §1′ and §2 get their classes for free, because their derivative seeds are elementary (FTC);
- every future arc-length family does too. *Any* family coming from `arc_length` has an
  elementary `F′`, which is a structural fact worth stating once;
- `k` can probably be extended to `ℤ` (`c` downward, DLMF 15.5.16) away from `c ∈ −ℕ`.

Then define

```lean
def HypReach : Set (ℝ × ℝ × ℝ × ℝ) :=
  {x | PConstructible (hyp x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
       PConstructible (deriv (hyp x.1 x.2.1 x.2.2.1) x.2.2.2)}
```

and turn each transformation already in the repo into a closure lemma on `HypReach`. These
include Pfaff (`Pfaff.lean`), general Goursat (`GoursatGeneral.lean`), V7 and, once proved, the
cubic/sextic signatures. The seeds are elliptic (`Elliptic.lean`), power-law (G1′), sheared
(G2), and Gauss/Kummer/Bailey at rational parameters (`GaussRational`, `KummerBailey`, already
general). This gives the "hypergeometric research track" a single object to grow.

---

## 4. Clausen and Goursat on every seed

`Clausen.lean` proves Clausen's identity only at `(¼, ¼)`, by an ODE argument specialized to that
case. The general identity is

```
₂F₁(a, b; a+b+½; z)² = ₃F₂(2a, 2b, a+b; 2a+2b, a+b+½; z)        [Literature]
```

The power-law class of §1 contains `c = a + b + ½` seeds: `(½, p; p+1)` is the inverse-square-root
member, `A(σ)` itself. This gives new families at once:

```
₂F₁(½, p; p+1; z)² = ₃F₂(1, 2p, p+½; 2p+1, p+1; z)             [Computed, 40 digits]  (C5)
₂F₁(1, 2p; p+1; z) = ₂F₁(½, p; p+1; 4z(1−z)),  z < ½              [Computed, 40 digits]  (C8)
```

The first is a `₃F₂` family over all rational `p`; the second is Goursat on the same seed. The
existing `GoursatGeneral.lean` covers C8 already, so it is a one-line corollary of G1′. A general
Clausen would need the third-order ODE of the symmetric square for general `(a, b)`. `Clausen.lean`'s
`qG_ode` is the `(¼, ¼)` instance, so the pattern exists.

---

## 5. Beyond the half-integer total: genus-1 incomplete Betas

G1 cannot reach `B_T(⅓, ⅓)`, because the total is `⅔`. But
`t^{−2/3}(1−t)^{−2/3} dt` is `3 dt / (3w²)` on the plane cubic `w³ = t(1−t)`, and that is the
holomorphic differential of a smooth cubic of genus 1. So `B_T(⅓, ⅓)` is an **incomplete elliptic
integral of the first kind** between the rational point `(0, 0)` and `(T, (T(1−T))^{1/3})`.
**[Proof sketch]**

To make that a P-constructibility statement:

1. Move to Weierstrass form, a rational change of variables over ℚ (there is a rational point).
2. Move to Legendre form. This needs the roots of a cubic, which are P-constructible (degree ≤ 8).
3. Apply `ellipticF_Pconstructible`, which is already proved at every P-constructible modulus
   and amplitude.

The general criterion is the genus of the cyclic cover `y^N = t^α (1−t)^β` (`N` the common
denominator):

```
g = 1 + (N − gcd(N, α) − gcd(N, β) − gcd(N, α+β)) / 2
```

Whenever `g ≤ 1`, or the differential factors through an elliptic quotient, the same
three-step argument applies. The quadratic map `u = 4t(1−t)` links the cases:

```
B_T(p, p) = 2^{1−2p} · ½ · B_{4T(1−T)}(p, ½),   T ≤ ½               [Computed, 40 digits]  (C9)
```

So `B_T(⅓, ⅓)` and `B_T(⅓, ½)` (genus 1 by the formula: `N = 6`, gcds `2, 3, 1`) stand or fall
together.

> **Question B.** Characterize `𝓑 = {(p, q) ∈ ℚ² : B_T(p,q) ∈ P for every P-constructible
> T ∈ (0,1)}`.

Known lower bound: the Chebyshev-elementary pairs (`p`, `q` or `p+q ∈ ℤ`), the half-integer-total
pairs (G1), and the genus-≤1 pairs. That set is closed under integer shifts, `(p,q) ↦ (q,p)`
(via `T ↦ 1−T` and the complete Beta, which is always available), and C9. An upper bound is
**[Open]**. A route-level negative, in the style of `reachability/R9`, might show that depth-one
arc lengths reach no other pair. It would not cover deeper constructions.

---

## 6. Lattice constants → lattice Green functions

`Polya.lean` proves P-constructibility of single numbers: `u(3)`, `u_bcc`, `u_fcc`. Each is the
value at `t = 1` of a lattice Green function. For bcc the whole function is elliptic:

```
G_bcc(t) = π⁻³ ∭ dθ / (1 − t cos θ₁ cos θ₂ cos θ₃) = (2K(k)/π)²,
k² = (1 − √(1 − t²))/2                                            [Computed, 21 digits]  (C10)
```

At `t = 1` this is `k² = ½`, and `(2K/π)² = Γ(¼)⁴/(4π³) = bccReturn3`. So
`G_bcc(t) ∈ P` for every P-constructible `t ∈ [0, 1]` is a one-line corollary of
`ellipticF_pi_div_two_Pconstructible`. It does not need the Γ route at all.

For sc and fcc, Joyce's formulas write `G(t)` as products of two `K`s whose moduli are algebraic
in `t` of low degree. Each Green function is then P-constructible on its whole real range
**[Literature: Joyce's closed forms for the sc and fcc Green functions; not re-checked]**. For
`t < 1`, `G(t)` is the expected number of visits to the origin of a walk that is killed with
probability `1 − t` at each step. So the theorem covers that whole family of walks, not just
the one constant.

---

## 7. Named roots → equation families

`dottie_Pconstructible`, `laplaceRoot_Pconstructible` and `lambertW_Pconstructible` are each one
crossing, proved by hand. The general engine is already in place: `crossing_Pconstructible`
needs only finiteness of the root set, not a window. Packaged families worth stating:

- **Kepler's equation.** For P-constructible `e`, `M`, every real solution of `E − e sin E = M`
  is P-constructible. It is the crossing of `sine` (scaled by `e`) with the line `y = x − M`. The
  root set is finite on any bounded window when `e ≠ 0`; for `|e| < 1` the solution is unique. The
  Laplace-limit docstring already motivates this, but the theorem itself is not in the repo. The
  Dottie number is a phase-shifted instance: `cos x = x`, i.e. `x − sin(x + π/2) = 0`.
- **Generalized Lambert W.** For P-constructible `a, b, c, d`, every real solution of
  `eˣ = (ax + b)/(cx + d)` is P-constructible. It is the crossing of `exp_PConstructibleCurve` with
  a translated hyperbola, exactly the Laplace-limit construction. This is the "r-Lambert" /
  rational-Lambert family of the literature (Mező, Baricz). `W` is `(a,b,c,d) = (0,x,1,0)`; the
  Laplace limit is `(1, 4, e², 0)`.
- **Mixed families** from `notes/warp/sheared-sine-intersections.md` §1: `Q(x, sin(x+φ)) = 0`,
  `Q(x, 2^x) = 0` for `Q` of the shape a drawable curve gives. These are reachable today; none
  has a name.

`BoxGraph`'s three named abscissas (`parabolaHalfArcAbscissa`, …) are illustrations of the
already-general `graphArcLength_inverse_Pconstructible`, so nothing to do there.

---

## 8. Where the specific result is already the frontier

For completeness, these are places where the specific statement is *not* an under-generalization:

- **Jacobi amplitude.** `am` is P-constructible on the `ℤ[½]`-module generated by the `F(φ)`, and
  `jacobiAm_Pconstructible_iff_epsilon` shows the general case is exactly as hard as Jacobi's
  `ℰ(u)`. **[Open]**
- **Third-kind integrals, AGM, Gauss/Kummer/Bailey at rationals, inverse trig, `rpow`.** These are
  already stated at full generality (every P-constructible / rational parameter).
- **Algebraic degree.** Degree ≤ 8 over P is general. Degree 9 is tracked in
  `algebraic/PLAN-degree9.md`.
- **Γ at irrational arguments.** No route (§1, last paragraph).

## 9. Suggested order

1. **G1 + G1′** (§1). Smallest Lean delta, biggest conceptual payoff: it turns the Γ theorem
   into a corollary and removes `n ≤ 6` from the graph family.
2. **Kepler / generalized Lambert / `G_bcc`** (§6–7). Each is a short file on existing engines.
3. **Theorem H and `HypReach`** (§3). A refactor that makes §4 and every later seed cheap.
4. **G2** (§2). Needs an `F₁` definition, or an integral-form statement.
5. **Question B** (§5). Research: write the genus-1 reduction for `B_T(⅓,⅓)` first as the
   positive control.
