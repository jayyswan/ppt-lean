# Sheared sines: the third-kind family, and where else shearing helps

Written 2026-11-26. Research note only: no `.lean` file was changed. Companion to
`GENERALIZATIONS.md`. Labels as there: **[Computed]** = `scripts/sheared_sine_checks.py`
(labels S1–S9), **[Lean]**, **[Proof]**, **[Proof sketch]**, **[Cited]** (from memory, not
re-checked), **[Heuristic]**, **[Open]**.

Builds on `notes/warp/sheared-sine-inversion.md` (normal form, inversion, residues),
`notes/warp/sheared-sine-intersections.md` (crossings), `notes/offset-inversion/SUMMARY.md`
(offsets, chains) and `notes/algebraic/C1.md` (Engine S).

## 0. What shearing bought, and what it leaves

`ThirdKindAll/Circular.lean` gets the incomplete third-kind integral `Π(n, φ | c)` at `n < 0`
from the arc length of the sheared sine `(−bt + sin t, at)`. DLMF transformations then carry it
to every real `(c, n, Φ)` (`ellipticPiInc_Pconstructible`, `ThirdKindAll/Main.lean`) **[Lean]**.

Consequence: every **forward** arc length of a sheared sine, between P-constructible endpoints,
is a combination of `F`, `E`, `Π` at real P-constructible arguments plus elementary terms
(sheared-sine-inversion §2). That direction is closed. A family of *new* numbers from sheared
sines has to come from the other operations: **inverting** the length, **offsetting**, and
**crossing**. §1–§2 set up coordinates in which all of these are one family; §3 lists the
family; §4 is where else to look.

## 1. One parameter for shear: `r ∈ ℂ`

Trace a graph `y = g(x)` as `t ↦ (t, g(t))` and apply an affine map with linear part
`M = [[m₁₁, m₁₂], [m₂₁, m₂₂]]`. Read velocities as complex numbers: with
`z₁ = m₁₁ + i m₂₁`, `z₂ = m₁₂ + i m₂₂`, the velocity is `z₁ + z₂ g′(t)`, so

```
speed = |z₂| · |g′(t) − r|,        r = −z₁/z₂                       [Computed]  (S6)
```

(checked for `g = sin`, `2^x`, `x^{5/2}`). `r` is real exactly when `det M = 0`. So up to the
factor `|z₂|`, **the arc lengths of all affine images of one graph are**

```
𝓛_g(r; t₀, t₁) = ∫_{t₀}^{t₁} |g′(t) − r| dt,      r ∈ ℂ ∖ ℝ.
```

Scaling moves `Im r`; **shearing moves `Re r`**. Unsheared scaled graphs are `Re r = 0`, i.e.
`∫ √(g′² + s²)`, which is what the repo used before `Circular.lean`. This is the whole content
of "shearing" for arc lengths, and it is the same for every base graph.

## 2. The sine instance

For `g = sin`, `r = b + ia` (`b ≥ 0`, `a > 0` after reflections), this is the curve of
`Circular.lean` with the explicit dictionary of sheared-sine-inversion §1:

```
S = √((1 + a² + b²)² − 4b²),   n = −(1 + a² + b² − S)/(2S),   c = (1 − a² − b² + S)/(2S),
a = √(c(1−c))/(c−n),   b = √((1−n)(−n))/(c−n)                      [Computed]  (S7)
```

and `∫₀^{T(θ)} |cos t − r| dt = circG(c, n, θ)` **[Computed, 150 digits]** (S7), with
`T(θ) = 2 arctan(k tan(θ/2))`. So `Re r = 0 ⇔ n = 0`: the shear *is* the characteristic.

### Lean shape

```lean
/-- Arc length of the affine images of the sine graph, in shear coordinates. -/
noncomputable def shearedSineLength (r : ℂ) (t₀ t₁ : ℝ) : ℝ :=
  ∫ t in t₀..t₁, Complex.abs ((Real.cos t : ℂ) - r)

-- Forward (packaging): `arc_length` on `affineMap` of `sine`. Already implicit in Circular.
theorem shearedSineLength_Pconstructible {r : ℂ} (hr : r.im ≠ 0)
    (hre : PConstructible r.re) (him : PConstructible r.im)
    (h₀ : PConstructible t₀) (h₁ : PConstructible t₁) :
    PConstructible (shearedSineLength r t₀ t₁)

-- Inverse (new in Lean; [Proof] in sheared-sine-inversion §3).
theorem shearedSineLength_inverse_Pconstructible {r : ℂ} (hr : r.im ≠ 0)
    (hre : PConstructible r.re) (him : PConstructible r.im)
    (h₀ : PConstructible t₀) (hσ : PConstructible σ)
    (h : shearedSineLength r t₀ t₁ = σ) : PConstructible t₁
```

*Proof of the inverse.* Draw `t ↦ (sin t − (Re r)t, −(Im r)t)` (`linearMap` of `sine`), lay
`σ` from the P-constructible point at `t₀` with `arc_of_length`, and read the far end with
`arc_yendpoint_Pconstructible`. The y-coordinate `−(Im r)t` is strictly monotone **for all
`t`**, so unlike `ellipticEAm_Pconstructible_via_sine` (`BoxSine.lean`, the case `r = i`) no
`[0, π/2]` window is needed. ∎

This generalizes the `BoxSine` theorem from the single point `r = i` to the whole open
half-plane. Example: `r = 0.9 + 0.7i`, `σ = 1` gives `t₁ = 1.3281…`, with no integer relation of
degree ≤ 8 [Computed] (S8). What is *proved* about these inverses (sheared-sine-inversion §4):
for `Re r ≠ 0` they are never `am`, and never the inverse of any `αF + βE + const`, because
`|cos t − r| dt` has a double pole and residues `±i·Re r` at the two points over `cos t = ∞`.

## 3. The family, as a list of operations

Call a number a **sheared-sine number** if it is obtained from P-constructible data by the
operations below. Each row says what is new.

| operation on a sheared sine `r` | output | new? | status |
|---|---|---|---|
| length between P endpoints | `F, E, Π(n ≤ 0)` + elementary | no | **[Lean]** (`ThirdKindAll`) |
| inverse length `Λ_r⁻¹(σ)` | 2-parameter inverse functions | **yes** for `Re r ≠ 0` (`Re r = 0` is `E⁻¹`) | [Proof]; Lean-feasible (§2) |
| offset by `d`, then length | `Λ_r − d·Δψ`, `ψ = arg(cos t − r)` | no | [Lean] (`OffsetInversion/Speed`) |
| offset, then inverse length | `(Λ_r − dψ)⁻¹(σ)`, 3 parameters | **yes** | [Proof] (offset-inversion catalogue, "sheared sine" row) |
| bounding box | `cos t` = const: elementary | no | [Proof] (intersections §3a) |
| crossing with a line / algebraic curve / `exp_two` | Kepler-type and `Q(t, sin t) = 0` families | yes | [Proof] (intersections §1) |
| crossing with another sheared sine | two-tone and Engine S, §4.3 | yes | [Proof] |
| chains of the above | triangular: no new equation shapes | — | [Proof] (offset-inversion R4, R6) |

The triangularity result means the family has a clean normal form **[Proof sketch, from
R4/R6]**: every sheared-sine number is a root of **one** equation

```
Λ_r(t) − d·ψ_r(t) = σ            (inversion stratum), or
two-tone crossing equation        (crossing stratum, §4.3),
```

whose data `(r, d, σ, …)` lie in a field generated by earlier sheared-sine numbers. So the
family is parametrized by three continuous parameters `(Re r, Im r, d)` for inversion, plus the
crossing data, and depth only enlarges the field of parameters.

## 4. Where else to look

### 4.1 Shear on other base graphs: when does it make a third-kind term?

`𝓛_g(r)` makes sense for every drawable graph. Near `g′ = ∞`,
`|g′ − r| = g′ − Re r + O(1/g′)`, so

```
|g′ − r| dt = dg − (Re r) dt + (holomorphic there).
```

The shear contributes `−(Re r) dt`. It produces a **logarithmic (third-kind) term exactly when
`dt` has a simple pole at a point over `g′ = ∞`**, i.e. when `t` is a logarithm of an algebraic
function of `g′` **[Proof sketch]**:

| `g` | `t` as a function of `u = g′` | does shear add a log term? | class of `𝓛_g` | class of `𝓛_g⁻¹` |
|---|---|---|---|---|
| `sin` | `arccos u` (log of algebraic) | **yes**: residue `±i·Re r` | elliptic, `Π` | new 2-parameter family (§2) |
| `2^x` | `log₂(u/ln 2)` | **yes** | elementary (genus 0) | elementary-transcendental equations: `√Q(u) + α·asinh(…) + β·log u = σ` |
| `x^p` | `(u/p)^{1/(p−1)}` (algebraic) | **no** | Appell `F₁` at a conjugate pair (`GENERALIZATIONS.md` §2) | inverse of an `F₁` |
| polynomial deg 3 | algebraic | no | elliptic (it is a cubic Bézier) | already in P's elliptic class |
| polynomial deg 4–6 | algebraic | no | hyperelliptic, genus 2–4 | formally new, no tools |

So among drawable graphs, **sine and `exp_two` are the only ones where shearing changes the
kind of integral**. This agrees with `notes/archive/NOTES-jacobi-R1c.md`, which found for both
bases that the log part has coefficient `q₁` (`speed² = q₂u² + q₁u + q₀`, and `q₁ = −2|z₂|² Re r`)
and vanishes for orthogonal-row maps, i.e. exactly when `Re r = 0`. For the sine that change was exactly what reached `Π`. For `exp_two` it
stays elementary, but the inverse equations are a new and untouched family (the offset
catalogue covers offsets of `exp_two`; I found no note on its sheared arc-length inverse). That is the cheapest
next family to write down: a sheared exponential, an arc of given length, and the endpoint read
off a box.

### 4.2 Genus one is closed: every elliptic integral with P data

`ThirdKindAll` proves `F`, `E`, `Π` P-constructible at every real `(c, n, Φ)`. Those are three
*functions*. An "elliptic integral" in general is `∫ R(x, √f(x)) dx`, with `f` a cubic or quartic
and `R` rational. The classical theorem that every such integral is `F`, `E`, `Π` plus elementary
terms uses `Π` at the characteristics where `R` has poles, and those can be **complex**. So
"we have `Π` for all real parameters" and "we have all elliptic integrals" differ by exactly one
lemma, which turns out to be true:

> **Lemma Π_ℂ [Computed, 30 digits, three test points] (S9).** For `0 < m < 1`, non-real `ν`
> and real `φ`, `Re Π(ν, φ | m)` and `Im Π(ν, φ | m)` are explicit combinations of
> `Π(n₁, φ | m)`, `Π(n₂, φ | m)`, `F(φ | m)` and elementary functions, with **real**
> characteristics `n₁ ∈ (0, m)` and `n₂ < 0`, algebraic in `(ν, m)`.

*Proof sketch.* Write `ν = m sn²a` with `a` complex, `u = F(φ)`, and use Jacobi's form
`Π_J(u, b) = (cn b dn b / sn b)(Π(m sn²b, φ) − F(φ))`, so that `Π(ν, φ) = F + (sn a /(cn a dn a)) Π_J(u, a)`.
Jacobi's addition theorem in the parameter (sign fitted and checked numerically):

```
Π_J(u,a) + Π_J(u,b) − Π_J(u,a+b) = m sn a sn b sn(a+b)·u
     + ½ log[(1 + m sn a sn b sn u sn(u−a−b)) / (1 + m sn a sn b sn u sn(u+a+b))].
```

Apply it with `b = ā` and `b = −ā`, and average:
`Π_J(u, a) = ½[Π_J(u, a+ā) + Π_J(u, a−ā)] + elementary`.
`a + ā` is real, so `n₁ = m sn²(a+ā) ∈ (0, m)`. `a − ā` is imaginary, so `sn(a−ā)` is imaginary
and `n₂ = m sn²(a−ā) < 0`. Explicitly, with `s = sn a = √(ν/m)`, `c = √(1−s²)`, `d = √(1−ms²)`,

```
n₁,₂ = m (s c̄ d̄ ± s̄ c d)² / (1 − m|s|⁴)²,
```

so `n₁, n₂` and every coefficient are P whenever `ν` and `m` are: only complex square roots
and field operations. The log term is the log of a P-algebraic function of `sin φ, cos φ, Δ(φ)`,
so its real and imaginary parts are a `log` and an `arctan` (with the branch followed along the
path, which changes it by multiples of `π`). Both characteristics are pole-free, so
`ellipticPiInc_Pconstructible` applies with no side conditions. ∎

With the lemma, the theorem has no hypothesis on the poles:

> **Theorem A1 (proposed).** Let `f` be a real cubic or quartic and `R(x, y)` a real rational
> function, both with P-constructible coefficients. For P-constructible `x₀, x₁` such that
> `f ≥ 0` on `[x₀, x₁]` and the integrand is finite there,
> `∫_{x₀}^{x₁} R(x, √f(x)) dx` is P-constructible.

*Proof sketch.* (1) The roots of `f` are P (degree ≤ 4). (2) A real Möbius map and a
`sn`-substitution put `f` in Legendre form with real `m ∈ (0, 1)`; the endpoints become
P-constructible amplitudes, since `arcsin` and `arctan` of P numbers are P. (3) Write
`R(x, y) = R₁(x) + R₂(x)/y`. The `R₁` part is elementary. Partial fractions of `R₂` in `sn²` give
`F`, `E`, elementary terms, and one `Π(ν)` per pole `ν` of `R₂`; real poles give real `ν`, and
conjugate pairs give `2 Re Π(ν)` (Lemma Π_ℂ). Every piece is P. ∎

**Answering the question "don't we have all elliptic integrals already?"** Yes, for every integral
the repo's curves actually produce. Sheared sines, Bézier curves, ellipses and their offsets all
have length elements whose only poles are at real points: shearing moves the **zeros** `r, r̄` of
the speed off the real axis, not its poles, and the curvature factor of an offset puts its
singularities at branch points. So Lemma Π_ℂ is not needed for any existing construction. What A1
adds is a **classification**: an elliptic integral (genus 1, real path, P data) can never be a new
number. That has two uses:

- **Negative.** A route whose answer is an elliptic integral of this kind adds nothing to P,
  without anyone having to find the specific substitution. That covers the `arc_length` reading
  of every genus-1 curve in the drawable list, and the third kind of every offset tower.
- **Where the frontier is.** New numbers from lengths need genus ≥ 2 (quartic–sextic graphs,
  power laws with `num(p − 1) ≥ 3`), the two-variable Appell family of `GENERALIZATIONS.md` §2, or
  an *inverse*: the inversion stratum of §3 is outside A1 because `Λ_r⁻¹` is an inverse function,
  not an integral.

**Lean cost.** Lemma Π_ℂ can avoid complex Jacobi functions entirely, since Mathlib has none: state
it as an identity between real functions of `φ` with the explicit `n₁, n₂` above, and prove it by
differentiating, as `Circular.lean` does for `circG`. The Legendre reduction in A1 is the large
part: a case split on the real-root pattern of `f`, with one substitution per case (Byrd–Friedman
tabulate them), each proved the same way.

### 4.3 Crossings: the two-tone family

Crossing two sheared sines that are graphs over a common axis gives

```
A₁ sin(ω₁x + φ₁) + A₂ sin(ω₂x + φ₂) + λx + μ = 0,      λ = difference of the two shears.
```

The general crossing (`m₁₂ ≠ 0` in S1) is "Kepler inside Kepler",
`sin(m₁₁s + m₁₂ sin s + v₁) = m₂₁s + m₂₂ sin s + v₂` [Computed] (S1). Strata:

| stratum | condition | output | example |
|---|---|---|---|
| **Chebyshev** (Engine S, C1) | `λ = 0`, `ω₁/ω₂ ∈ ℚ` | `cos θ` algebraic; totally real `S_n` for all `n` | `cos 5θ + cos 2θ/3 + 1/7 = 0` ⇒ `336x⁵ − 420x³ + 14x² + 105x − 4 = 0`, `x = cos θ` [Computed] (S2) |
| incommensurable | `λ = 0`, `ω₁/ω₂ ∉ ℚ` | transcendental-looking **[Open]** | `sin t = sin(√2 t)/2 + 1/3`: no relation for `cos t` [Computed] (S3) |
| two-tone Kepler | `λ ≠ 0` | Kepler, Dottie as one-tone cases | `cos 2t + cos t/3 + t/5 = 1/7`: no relation [Computed] (S4) |

Equal shears cancel, and that is why `λ = 0` is the algebraic stratum. The Chebyshev stratum is
a torsor under `θ ↦ θ + φ` [Computed] (S5), so its five coefficients carry three essential
parameters. Lean shape: one theorem `twoTone_root_Pconstructible` with the hypothesis
"not identically zero" (all zeros then isolated, by analyticity), from which Engine S, Kepler for
all `(e, M)` and Dottie are corollaries. The same theorem with `exp_two` in place of `sine` gives
the hyperbolic Kepler equation `e sinh H − H = M` and `cosh x = kx`.

**Why the sine is special here too [Cited: Ritt 1922].** Two copies of one transcendental graph
with commensurable frequencies give an algebraic equation only if the function has an algebraic
multiplication theorem: exponential (trinomial engine), trigonometric (Engine S), or elliptic.
An elliptic-function graph is not drawable; it is the Jacobi-amplitude frontier
(`jacobiAm_Pconstructible_iff_epsilon`).

## 5. Suggested order

1. `shearedSineLength_inverse_Pconstructible` (§2). Small: the curve, `arc_of_length` and
   `arc_yendpoint_Pconstructible` all exist, and the monotone y-coordinate removes the window
   argument. It is the first Lean theorem whose output is a genuinely new function.
2. The sheared-`exp_two` inverse (§4.1): same proof, and its equation class is untouched.
3. `twoTone_root_Pconstructible` (§4.3), with Engine S and hyperbolic Kepler as corollaries.
4. Lemma Π_ℂ (§4.2): medium, a real identity proved by differentiation. Then Theorem A1:
   medium-large, a Legendre-reduction library on top of `ThirdKindAll`.
5. Research: whether the inverse family of §2 meets any classical function.
