# Sheared sines as a family, and the principle behind them

Written 2026-11-26. Research note only: no `.lean` file was changed. Companion to
`GENERALIZATIONS.md`. Labels as there: **[Computed]** = `scripts/sheared_sine_checks.py`
(labels S1–S7), **[Proof]**, **[Proof sketch]**, **[Cited]** (from memory, not re-checked),
**[Open]**.

## 0. Where shearing actually entered

Two different shears are in play, and it is worth keeping them apart.

- **Octic roots.** `root_Pconstructible_deg8_coeffs` uses no sine. Its last crossing is
  `Y = X⁸` against a **sheared quartic graph** (`quarticGraph_PConstructibleCurve`: a rational
  `poly_graph` of `X⁴ ± X²`, scaled, sheared by `bz`, translated). The shear is what turns a
  rational graph into one with P-coefficients. §5 generalizes this.
- **Sine × sine.** `notes/algebraic/C1.md` (Engine S) crosses two sine graphs that carry the
  **same** shear and commensurable frequencies. The shears cancel, `cos θ` comes out
  algebraic, and P gets totally real `S_n` numbers of every degree. §1–§4 formalize this as one
  member of a larger family.

The common idea: a shear is a free P-parameter, so it either fills a coefficient you need
(octic) or cancels between two curves and leaves an algebraic equation (Engine S).

## 1. The master family

Every sheared sine is an affine image of `sine`. Crossing two of them is, after applying the
inverse of one affine map, a crossing of `y = sin x` with an affine image
`(s, sin s) ↦ M(s, sin s) + v` of it. A point is on both exactly when

```
sin(m₁₁ s + m₁₂ sin s + v₁) = m₂₁ s + m₂₂ sin s + v₂               [Computed]  (S1)
```

> **Theorem SS (proposed).** For P-constructible `M` (invertible) and `v`, every real `s`
> solving this equation, other than in the degenerate case where both sides agree
> identically, is P-constructible, and so is the crossing point.

*Proof sketch.* `sine` and `affineMap_PConstructibleCurve` draw both curves. Along
`Γ(s) = (s, sin s)` the defining function of the image curve is real-analytic and not
identically zero, so its zeros are isolated; `restrict` to a rational window around the
chosen zero and apply `crossing_Pconstructible`. ∎

This is a 6-parameter family, and it splits into strata by two invariants: the
**nesting coefficient** `m₁₂` and, when `m₁₂ = 0`, the **shear difference** `λ` and the
**frequency ratio** `ρ`.

When `m₁₂ = 0` the image is again a graph over the x-axis, `y = A sin(ωx + φ) + λx + μ`, and
the equation becomes the **two-tone equation**

```
sin x − A sin(ωx + φ) − λx − μ = 0.
```

Before normalizing, both curves can carry a shear, `y = Aᵢ sin(ωᵢx + φᵢ) + λᵢx + μᵢ`; only the
difference `λ = λ₁ − λ₂` survives. That is why "the same shear" is the algebraic case.

| stratum | condition | equation | output | example |
|---|---|---|---|---|
| **L0 Chebyshev** | `m₁₂ = 0`, `λ = 0`, `ρ ∈ ℚ` | `A cos pθ + B sin pθ + C cos qθ + D sin qθ + E = 0` | `cos θ` algebraic (Engine S) | `cos 5θ + cos 2θ/3 + 1/7`: `cos θ` has min. poly `336x⁵ − 420x³ + 14x² + 105x − 4` [Computed] (S2) |
| **L1 incommensurable** | `m₁₂ = 0`, `λ = 0`, `ρ ∉ ℚ` | `sin x = A sin(ωx + φ) + μ` | transcendental-looking **[Open]** | `sin t = sin(√2 t)/2 + 1/3`: no integer relation of degree ≤ 10, height ≤ 10⁶ for `cos t` [Computed] (S3) |
| **L2 two-tone Kepler** | `m₁₂ = 0`, `λ ≠ 0` | `λx + (two tones) + μ = 0` | Kepler, Dottie, Laplace-type | `cos 2t + cos t/3 + t/5 = 1/7`: no relation for `t` or `cos t` [Computed] (S4) |
| **L3 nested** | `m₁₂ ≠ 0` | `sin(as + b sin s + v₁) = cs + d sin s + v₂` | "Kepler inside Kepler" | none named |

L0 is the only stratum whose outputs are algebraic for *all* algebraic parameters
**[Proof sketch]** (other strata can hit algebraic values by accident, e.g. at `θ = 0`): with `λ ≠ 0` or `m₁₂ ≠ 0` the
unknown appears outside a trigonometric function, and with `ρ ∉ ℚ` the two tones are
algebraically independent functions; in each case a standard Lindemann–Weierstrass /
Gelfond–Schneider-type argument is needed to make that precise, and I have not done so.

## 2. Lean shape of the family

```lean
/-- The graph of `x ↦ A sin(ω x + φ) + λ x + μ`: a sheared sinusoid. -/
def shearedSinusoid (A ω φ λ μ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 = A * Real.sin (ω * p.1 + φ) + λ * p.1 + μ}

theorem shearedSinusoid_PConstructibleCurve (A ω φ λ μ all PConstructible) :
    PConstructibleCurve (shearedSinusoid A ω φ λ μ)
-- sine; scale_x 1/ω; translate_x; scale_y A; shear_PConstructibleCurve λ (after a swap);
-- translate_y μ. Every step exists.

/-- Two-tone trigonometric-linear function. -/
def twoTone (A₁ ω₁ φ₁ A₂ ω₂ φ₂ λ μ : ℝ) (x : ℝ) : ℝ :=
  A₁ * Real.sin (ω₁ * x + φ₁) + A₂ * Real.sin (ω₂ * x + φ₂) + λ * x + μ

theorem twoTone_root_Pconstructible (all eight PConstructible)
    (hnz : ¬ ∀ x, twoTone … x = 0) (hx : twoTone … x = 0) : PConstructible x
```

`hnz` is the right non-degeneracy hypothesis: it is what the identity theorem for analytic
functions needs to make zeros isolated, and it handles `ω₁ = ω₂` (where the tones merge) with
no special case.

Corollaries, each a few lines:

- `dottie_Pconstructible`, Kepler for all `(e, M)` (`GENERALIZATIONS.md` §7) — one tone, `λ ≠ 0`.
- **Engine S.** For integers `p > q ≥ 1` and P-constructible `A … E` not all zero, every real
  `θ` with `A cos pθ + B sin pθ + C cos qθ + D sin qθ + E = 0` is P-constructible, hence so
  are `cos θ`, `sin θ` (`cos_sin_Pconstructible`).
- **Chebyshev trinomial roots.** Every root in `[−1, 1]` of `T_p + a·T_q + c` (`a, c` P) is
  P-constructible. Stated with Mathlib's `Polynomial.Chebyshev.T`.
- **Theorem C1** for one explicit `n ≥ 13` (`T_n + x/3 + 1/7`), giving totally real `S_n`
  numbers beyond anything degree-≤ 8 machinery can reach.

## 3. The algebraic stratum as a set

> **Definition.** `𝒯_{p,q}` is the set of `cos θ` for real `θ` solving a nontrivial
> `A cos pθ + B sin pθ + C cos qθ + D sin qθ + E = 0` with `A … E ∈ P`.
> `𝒯 = ⋃ 𝒯_{p,q}`.

Equivalent descriptions [Proof, C1 §1.2]:

- `𝒯_{p,q}` = real parts of the **unimodular** roots of self-inversive pentanomials
  `α u^{2p} + β u^{p+q} + E u^p + β̄ u^{p−q} + ᾱ`, `α, β ∈ P + iP`, `E ∈ P`.
- With `B = D = 0`: roots in `[−1, 1]` of Chebyshev trinomials `T_p + a T_q + c`.

Structure worth stating once:

- **Rotation torsor** [Computed] (S5). `θ ↦ θ + φ` with `φ ∈ P` maps the five-term family to
  itself. So the 5 coefficients carry 3 essential parameters (minus scale, minus rotation),
  matching C1 §5's count.
- **Chebyshev towers.** `T_{pk} = T_p ∘ T_k`, and `cos(θ/k)` is P whenever `cos θ` is
  (`arccos` then divide). So `𝒯` is closed under `T_k⁻¹`, the trigonometric analogue of
  taking radicals. This is the casus-irreducibilis mechanism in P's language.
- **Full symmetric group, all roots real.** C1 §1.3–1.4. This is the one property the
  monomial-basis engines (trinomials, power laws) cannot have.

**Question T.** `𝒯 ⊆ F = P ∩ ℝ_alg` by construction. The open direction is the converse for a
*given* field: which real number fields `K` contain an element of `𝒯` (over a tower of
degree-≤ 8 steps) that generates them? That is C1's (SR′), an F-point on a general-type
variety **[Open]**.

## 4. Where else to look: the commensurable-crossing principle

Engine S is one instance of a pattern that also produced the trinomial engine (W3):

> Cross **two copies of one transcendental graph** `y = g(x)`, with commensurable
> frequencies and **equal shear**. If `g(px)` and `g(qx)` are algebraically dependent, the
> crossing equation becomes algebraic in `g(x)`, and its real roots land in `F`.

| `g` | drawable as | multiplication law | engine |
|---|---|---|---|
| `x^r`, polynomials | `power_law`, `poly_graph` | trivial | power-law crossings (already the main algebraic tool) |
| `2^x` | `exp_two` | `u^p` | power trinomials `a u^p + b u^q + c` (W3, Theorem X) |
| `sin x` | `sine` | Chebyshev `T_p` | Engine S (C1) |
| elliptic `sn x` | **not drawable** | division polynomials | would give elliptic division engines |

**Why the list stops there [Cited].** Ritt (1922) classified periodic meromorphic functions
with an algebraic multiplication theorem `f(kx) = R(f(x))`: up to change of variables they are
exponential, trigonometric or elliptic. With Weierstrass's addition-theorem classification,
this says the drawable transcendental shapes give **every** non-elliptic engine of this type,
and the only remaining one needs the graph of an elliptic function. That is precisely the
Jacobi-amplitude frontier of `GENERALIZATIONS.md` §8 (`jacobiAm_Pconstructible_iff_epsilon`).
Even if it opened, H4 says elliptic division values give only `A₅` and `PSL(2, p)` groups, so
it would not beat Engine S for `S_n`. [Proof sketch for the last sentence, via H4.]

**Mixed pairs** (different `g`) are the transcendental side of the same table. Two
immediately useful corollaries of a two-tone theorem with `exp_two` in place of `sine`
[Proof, assuming the two-tone theorem]:

- **Hyperbolic Kepler.** `e sinh H − H = M` for `e > 1` is
  `(e/2)·e^H = (e/2)·e^{−H} + H + M`: one exponential graph against a reflected, sheared,
  translated one (`exp_PConstructibleCurve` is already in `Basic.lean`). The difference is
  strictly increasing, so the root is unique and needs no window argument.
- **Catenary equations.** `cosh x = kx` is `e^x/2 = kx − e^{−x}/2`, same construction.

So the right general statement is not about sines at all:

> **Theorem 2T (proposed).** Let `g₁, g₂` each be `sin`, `exp`, or a `power_law` shape, and let
> `f(x) = a₁ g₁(ω₁x + φ₁) + a₂ g₂(ω₂x + φ₂) + λx + μ` with P-constructible parameters,
> `f ≢ 0` on the relevant domain. Every real zero of `f` is P-constructible.

It subsumes Dottie, Kepler (elliptic and hyperbolic), Lambert `W` (`eˣ = ax + b`), Engine S
and the trinomial engine. (The Laplace limit and generalized Lambert need a hyperbola, so they
stay with `GENERALIZATIONS.md` §7.) The algebraic outputs are exactly the
same-`g`, commensurable, `λ = 0` cells.

## 5. The octic side: shear orbits of polynomial graphs

The octic engine needs a quartic graph with arbitrary P-coefficients. The affine maps that keep
a graph a graph (x-translate, x-scale, y-scale, shear, y-translate) form a 5-dimensional group,
so from a rational `poly_graph` of degree `d` they reach a 5-dimensional orbit, against `d + 1`
coefficients. Depressing (`x`-translate), killing the linear term (shear), the constant
(`y`-translate), and normalizing the leading and `x^{d−2}` coefficients (the two scalings)
leaves `d − 4` **shear-orbit invariants** that must be rational:

| `d` | invariants (depressed, monic, `a = coeff x^{d−2} ≠ 0`) | consequence |
|---|---|---|
| ≤ 4 | none | every P-quartic graph is drawable (this is `quarticGraph_general_PConstructibleCurve`) |
| 5 | `b/(±a)^{3/2}` with `b = coeff x²`, sign making the base positive | P-quintic graphs form a ℚ-indexed set of 4-parameter families [Computed] (S6) |
| 6 | `b/a^{3/2}`, `c/a²` | two rational invariants [Computed] (S7) |

[Proof for "rational invariants ⇒ drawable"; the converse holds for this route only, since
Bézier and other curves could reach more.]

Two generalizations follow directly:

- **Any exponent.** `powerLaw_quartic_root_PConstructible` is stated for `β⁸` only. The same
  proof should give `βⁿ = quartic(β)` for every natural `n > 4`, and for `β > 0` every rational
  exponent `r` (`power_law 1 r`). That is the 5-parameter engine
  "`X^r` × P-quartic" for all `r`, of which the octic resolvent uses `r = 8`. **[Proof sketch]**
- **Degree-5/6 engines with rational moduli.** `X^n` against a quintic or sextic graph whose
  shear-orbit invariants are rational gives engines with 4 + (rational data) parameters. This is
  where the bookkeeping law (`notes/algebraic` H1) loses `d − 4` free parameters, and it explains
  why quartic graphs, not sextic ones, are the workhorse of the degree-8 proof.

## 6. Suggested order

1. `shearedSinusoid_PConstructibleCurve` and `twoTone_root_Pconstructible`: small, and every
   later item is a corollary.
2. Engine S and the Chebyshev-trinomial corollary, then Theorem C1 at one explicit `n ≥ 13`.
3. `powerLaw_quartic_root` for general exponent (§5): mechanical.
4. Theorem 2T with `exp_two`, plus hyperbolic Kepler as the showcase.
5. Research: L1 vs L0 transcendence (§1), and Question T / (SR′) (§3).
