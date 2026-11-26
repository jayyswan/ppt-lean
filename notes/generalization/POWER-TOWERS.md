# Power-law towers: what affine maps, offsets, `arc_length` and `arc_of_length` reach

Written 2026-11-26. Research note only: no `.lean` file was changed. Companion to
`GENERALIZATIONS.md` (§1, §1′, §2) and `SHEARED-SINES.md` (§1, §4.1). Labels as there:
**[Computed, n digits]** = `scripts/power_tower_checks.py` (labels T1–T3),
**[Proof]**, **[Proof sketch]**, **[Heuristic]**, **[Open]**.

The question: start from `power_law` `y = x^p` (`p ∈ ℚ`) and apply affine maps, offsets,
`restrict`, `arc_length` and `arc_of_length` in any order, as often as you like. Can we say
exactly which numbers come out?

Short answer: yes, up to one open question. A tower of any depth **collapses to one affine
image plus a sum of ellipse arcs** (§1). That reduces everything to one explicit family of
one-variable integrals (§2), whose kind is decided by the numerator of `p − 1` (§3). The new
numbers come only from inverting those integrals (§4). §5 states the closure exactly, and §6
says what is left open.

---

## 1. The collapse theorem (affine Steiner formula)

A **tower** over a regular C² curve `γ` is any composite
`A_k ∘ Off_{d_k} ∘ ⋯ ∘ A_1 ∘ Off_{d_1} ∘ A_0 (γ)`. Here each `A_i` is affine and `Off_d` is the
`offset` constructor. Two facts drive the theorem:

- `deriv_offsetParam` (`OffsetInversion/Speed.lean`): an offset multiplies the velocity by the
  **real** scalar `1 − dκ`. It changes the speed, but the tangent direction stays the same.
- A linear map acts linearly on velocities.

So the final velocity is `λ(t) · N T(t)`, where `T` is the base velocity, `N` the composite
linear part and `λ` a real scalar. Write `N_j` for the linear part composed **before** the
`j`-th offset, and `M_j = N N_j⁻¹` for the part composed after it. The final curve is

```
Γ(t) = N γ(t) + Σ_j d_j · M_j n_j(t) + const,      n_j = unit normal of N_j γ,
```

and every summand has velocity parallel to `N T` (because `n_j′ ∥ N_j T`). Parallel velocities
add lengths, so:

> **Theorem T (affine Steiner) [Proof; Computed, 28 digits (T1, T2)].** Assume no cusps on
> `[t₀, t₁]` (every `1 − d_j κ_j > 0`) and `det N_j > 0` (a reflection only flips the sign of
> `d_j`). Then
> ```
> L(Γ; t₀, t₁) = L(Nγ; t₀, t₁) − Σ_j d_j · ℰ_{M_j}(ψ_j(t₀), ψ_j(t₁)),
> ℰ_M(θ₀, θ₁) = ∫_{θ₀}^{θ₁} |M e^{iθ}| dθ,
> ```
> where `ψ_j` is the tangent angle of `N_j γ`. `ℰ_M` is the arc length of the ellipse
> `M(S¹)` between the points `M e^{i(θ₀−π/2)}` and `M e^{i(θ₁−π/2)}`.

In the slope coordinate `v = γ′₂/γ′₁` (for a graph, `v = g′(t)`), with
`q_j(v) = |N_j(1, v)|²` and `q₀(v) = |N(1, v)|²`, the length element is

```
ds = √q₀(v) dt − Σ_j d_j det N_j · √q₀(v) / q_j(v)^{3/2} dv        [Computed, 28 digits]  (T1)
```

T1 and T2 use a test tower `A₂ ∘ Off ∘ A₁ ∘ Off` over `y = x^{5/2}` with two different
sheared linear parts. The correction terms are about 0.019 there, so the agreement is not
trivial.

**Consequences.**

1. **Offsets add no new forward lengths, over any base.** Every correction term is an ellipse
   arc between P-constructible points. The direction `N_j(1, v)/|N_j(1, v)|` is P whenever `v`
   is, and an ellipse is a base curve, so `ellipse` + `linearMap_PConstructibleCurve` +
   `arc_length` already make each term P. No Legendre reduction is needed. The repo's
   `arcLengthOf_offsetParam` (`arc − d·Δψ`) is the special case `N_j = N`, where `M_j = I`
   and the ellipse is the unit circle.
2. **A tower's length data is finite and explicit:** the base curve, the positive-definite
   quadratic `q₀`, and pairs `(q_j, c_j)` with `c_j = d_j det N_j`. Conversely, every such list
   is realized: take `N_j` with `|N_j(1, v)|² = q_j` by Cholesky (square roots of P numbers),
   and choose `d_j` freely. So the shape of the length form does not depend on depth.
3. **Every correction is the same universal elliptic form,** `√(q₀ q_j)/q_j² dv`: the square
   root of a quartic with two conjugate root pairs. Its poles sit at branch points, and since
   the differential is odd under `y ↦ −y`, it has zero residue there. So these terms are
   second kind only: `F`, `E` and algebraic terms, with no `Π`. They are elementary exactly
   when `q_j ∝ q₀`, i.e. when `M_j` is a similarity.
4. Cute check: the ellipse is itself a tower (an affine image of the offset of a point), and
   its length element is exactly the correction term.

**Caveat (cusps).** If the arc passes through a cusp of some offset (`1 − d_j κ_j = 0`), the
`|·|` splits the integral at the cusp parameter. That parameter is a root of an algebraic
equation in `t` and need not be P. The tower length is still P (the `arc_length` rule gives
it directly), but Consequence 1 only identifies it as a combination when the cusp is P.

## 2. The base term for `y = x^p`

Put `s = p − 1`, `v = p t^s`, so `dt ∝ v^{α} dv` with `α = 1/s − 1`. The affine part of the
length is, up to a constant factor,

```
𝔅_p(r; v₀, v₁) = ∫_{v₀}^{v₁} v^{α} √((v − r)(v − r̄)) dv,        r = −z₁/z₂ ∈ ℂ ∖ ℝ
```

in the shear coordinate of `SHEARED-SINES.md` §1. So a power-law tower length is

```
L = c₀ 𝔅_p(r; v₀, v₁) + Σ_j c_j ℰ_j(v₀, v₁),
```

with `ℰ_j` the universal elliptic terms of §1. Two strata:

- **Unsheared** (`Re r = 0`, an orthogonal-row linear part): `q₀` is even in `v`, the quotient
  `v ↦ v²` takes the 4-point integrand to a 3-point one, and `𝔅_p` is the incomplete Beta
  `B_T(1/s, −1/s − ½)`. This is `GENERALIZATIONS.md` G1/G1′.
- **Sheared** (`Re r ≠ 0`): no such quotient. `𝔅_p` is `F₁(1/s; −½, −½; 1 + 1/s; ζ, ζ̄)`, which
  is G2.

## 3. Which kind of integral: decided by the numerator of `p − 1`

Write `p − 1 = n′/m′` in lowest terms and let `n = |n′|`. Then `α` has denominator `n`. The
integrand `v^α √((v − r)(v − r̄))` lives on a cyclic cover of ℙ¹, branched over `0, r, r̄, ∞`
with local exponents `(α, ½, ½, −α)`. Riemann–Hurwitz with `N = lcm(2, n)` gives
**[Proof sketch]**

```
g = 1 + N/2 − N/n.
```

| `n` | `p` (examples) | genus | sheared base term `𝔅_p` | its inverse |
|---|---|---|---|---|
| 1 | `2, 3/2, 4/3, …; 1/2, 2/3, …` (`p = 1 ± 1/m`) | 0 | elementary (algebraic + `log`/`asinh`) | elementary-transcendental equations (as `graphArcLength_inverse_Pconstructible`) |
| 2 | `3, 5/3, 7/5, …; −1, 1/3, 3/5, …` (`p = 1 ± 2/m`, `m` odd) | 1 | elliptic, via `v = w²` [Computed, 30 digits] (T3) | inverses of `αF + βE +` algebraic: the Jacobi frontier |
| 3 | `4, 5/2, −2, −1/2, …` | 2 | genus 2 | new |
| 4 | `5, 7/3, …` | 2 | genus 2 | new |
| `n ≥ 3` | — | `n − 1` (`n` odd), `n/2` (`n` even) | genus ≥ 2 | new |

Checks against known cases: `p = 3` (a sheared cubic, i.e. a Bézier) and `p = −1` (a
hyperbola) are elliptic; `p = 2` (a parabola) is elementary; `x⁴, x⁵, x⁶` give genus 2, 2, 4,
matching the "hyperelliptic, genus 2–4" row of `SHEARED-SINES.md` §4.1. The table is symmetric
under `p ↔ 1/p` (swapping the axes), as it must be: `1/p − 1 = −n′/(n′ + m′)` has the same
numerator.

**Shear adds no third-kind term for power laws.** For `n = 2` the substitution `v = w²` gives
`w^{2α+1} · 2√(quartic(w)) dw`. Its only poles are at `w = 0` and at `∞`, both over real
points. So Theorem A1 of `SHEARED-SINES.md` applies, and it does not need Lemma Π_ℂ. This
agrees with the §4.1 table there: `t(v)` is algebraic, so there is no logarithmic residue.

**So, for forward lengths:** for `n ≤ 2` (`2/(p − 1) ∈ ℤ`) every power-law tower length is an
`F/E/Π` combination, so it is not a new number. For `n ≥ 3` and sheared, it is a two-parameter
family of genus-≥2 periods (the `F₁` of G2). That family is P by the `arc_length` rule and is
not known to be anything classical.

## 4. Inversion is where new numbers come from

`arc_of_length` from a P point `v₀` with P length `σ` defines `v₁` by

```
Φ(v₁) := c₀ 𝔅_p(r; v₀, v₁) + Σ_j c_j ℰ_j(v₀, v₁) = σ.        (★)
```

The endpoint is read off with `box_xmax`/`box_ymax` or `arc_yendpoint_Pconstructible` when a
coordinate is monotone; otherwise, with a crossing. `t₁ = (v₁/p)^{1/s}` is then P.

Parameter count for a fixed `p`: `r` (2 real) plus 3 real parameters per offset (`q_j` up to
scale, and `c_j`). Even for `n = 1`, where `𝔅_p` is elementary, (★) with one offset is "an
elementary function plus an incomplete elliptic `E`-type term = σ", and no repo note covers
it. **[Heuristic]**: for generic data, (★) with `k + 1` terms on `k + 1` different curves
(the cover of §3 and `k` elliptic curves `y² = q₀ q_j`) is not reducible to fewer terms, so
each offset genuinely enlarges the inverse family. Two exceptions: an offset placed *after*
the last affine map contributes only `d·Δψ` (the existing offset-inversion catalogue), and so
does any offset whose `M_j` is a similarity.

## 5. The closure, stated exactly

**Curves.** Starting from one `power_law` and using {affine, offset, `restrict`,
`arc_of_length`}, every curve reached is a sub-arc of a tower, and its endpoints have
parameters in the field generated so far. The reason: `arc_of_length` and `restrict` return
sub-arcs, and an offset of a sub-arc is a sub-arc of the offset. **[Proof sketch]**

**Numbers.** Let `K` be the smallest subfield of ℝ containing ℚ and closed under:

1. **(F)** `Φ(v₀, v₁)` for data `(r, q_j, c_j, v₀, v₁)` in `K` (forward lengths, by Theorem T);
2. **(I)** solutions `v₁` of (★) with data in `K`;
3. **(B)** box readouts. These add nothing: the extremes are endpoints, or points where
   `N(1, v)` is axis-parallel, which is linear in `v`;
4. **(X)** crossing coordinates. With a line or with another tower, a crossing is an algebraic
   equation in `w = t^{1/n}` and `√q_j(v)`, with coefficients in `K`.

Then `K ⊆ P`, and `K` is exactly what the power-law towers produce. Combined with the
triangularity results of `offset-inversion` (R4/R6), every element of `K` has a **normal form**:
a finite triangular sequence of steps, each one instance of (F), (I) or (X), whose data lie in
the field generated by the earlier steps. Depth only enlarges the field of parameters; it never
creates a new equation shape. **[Proof sketch]**

Several base curves at once (power laws with different `p`, `exp_two`, `sine`) give the same
statement with `𝔅_p` replaced by the base term of each. Theorem T is base-independent:

| base | `dt` in the slope `v` | base term `√q₀ dt` | kind |
|---|---|---|---|
| `x^p` | `v^{α} dv` | §2–3 | by the numerator of `p − 1` |
| `2^x` | `dv / (v ln 2)` | `√q₀ / v` | genus 0, with a log term when `Re r ≠ 0` |
| `sin` | `−dv / √(1 − v²)` | `√(q₀ / (1 − v²))` | elliptic, with `Π` when `Re r ≠ 0` (`Circular.lean`) |
| point (circle) | — | the `ℰ` term itself | elliptic, second kind |

## 6. What this leaves open

- **[Open] Upper bound.** Is `K` (or its several-base version) all of P? Probably not: P also
  has Bézier curves, text outlines and AGM-type constructions. But no invariant is known that
  separates them.
- **[Open] Special shears for `n ≥ 3`.** Does `𝔅_p` reduce to genus ≤ 1 for special `r`? The
  involution `v ↦ |r|²/v` swaps `0 ↔ ∞` and `r ↔ r̄`, but it conjugates the character, so it
  does not split the eigenspace. A CM / isogeny check on the Jacobian would settle it.
- **[Open] Crossings (X).** Offsets of power laws are algebraic curves of growing degree
  (degree 6 already for the parabola), so (X) may produce algebraic numbers of high degree.
  Whether this gives anything for the degree-9 programme (`algebraic/PLAN-degree9.md`) is worth
  one check.

## 7. Lean shape and order

1. **`arcLengthOf_tower`** (Theorem T). Define `towerParam` as a list of `(N_i, d_i)` steps
   folded with `linearMap` and `offsetParam`. The proof is an induction on the list:
   `deriv_offsetParam` for the offset step, linearity of `deriv` for the affine step, and the
   identity `|λ N T| = λ |N T|` for `λ > 0`. It needs a C² hypothesis at each stage, which is
   how `offset` already states its own hypotheses. This is small: it is `arcLengthOf_offsetParam`
   with one more induction.
2. **Corollary: P ellipse arcs absorb offsets.** This is the statement of Consequence 1,
   proved by exhibiting each correction as `arc_length` on `linearMap` of `ellipse`.
3. **`towerLength_inverse_Pconstructible`.** (★) for one offset under a monotone coordinate:
   `arc_of_length` + `arc_yendpoint_Pconstructible`, as in `SHEARED-SINES.md` §2.
4. **The genus table (§3)** as a docstring classification. In Lean it is just the statement of
   G1/G2 over rational `p`. The genus is not a Lean object, and nothing needs it to be.
