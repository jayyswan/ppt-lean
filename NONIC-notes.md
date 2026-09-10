# Degrees 7, 8 and 9: what the Bézout ceiling of the Bézier actually is

Investigation for issue #1. Everything below is about the plane-curve geometry that sits
behind `crossing_Pconstructible`; the conclusions are then formalised in
`Pptc/Basic.lean`, section *Nonics*.

## The setup that `crossing_Pconstructible` imposes

A root construction is a choice of

* a drawable curve `S` with a parametrisation `Γ` covering it,
* a drawable curve `T` and a function `F` vanishing on `T`,

together with the identity `p t = F (Γ t)`. The degree bought is the degree of
`t ↦ F (Γ t)`, and Bézout says it cannot beat `deg Γ · deg F`.

With **P-constructible** parameters throughout, the drawable curves are:

| family | implicit degree | parametric degree | parameters |
|---|---|---|---|
| ellipse / hyperbola / parabola, and all affine images | 2 | 2 (rational) | P-constructible |
| cubic Bézier, and all affine images | 3 | 3 (polynomial) | P-constructible |
| `poly_graph`, `power_law`, `exp_two`, `sine` | up to 6 / any | — | **rational only** |

`offset` and `arc_of_length` draw further curves with P-constructible parameters, but not
ones with a usable implicit equation, so they are out of scope here. Among the rest,
`3 × 3 = 9` is the ceiling, and reaching it needs *both* curves to be cubic Béziers.

## Fact 1: a Bézier cubic meets the line at infinity at one point, triply

A cubic Bézier is a pair of cubics `(x t, y t)`. Its projective parametrisation is

    [s : w]  ↦  [x*(s,w) : y*(s,w) : w³]

with `x*`, `y*` the degree-3 homogenisations. The last coordinate vanishes only at
`w = 0`, and to order `3`. So the closure `C` meets `Z = 0` at the single point
`[x₃ : y₃ : 0]` with multiplicity `3`, and the leading form of the implicit equation of
`C` is a perfect cube of a linear form. `C` is also singular, being rational.

Two consequences, and both contradict the plan in the issue.

## Fact 2: a shared point at infinity costs **three**, not one

If the two Béziers share their point at infinity `Q`, both have contact of order `3` with
`Z = 0` there, so `I_Q(S, T) ≥ 3` and only `9 - 3 = 6` intersections are left in the
plane. Concretely: `F`'s leading form is `c·(αX + βY)³`, so

    p t = c·(α x t + β y t)³ + (terms of degree ≤ 2 in X, Y),

and a shared point at infinity is exactly `α x₃ + β y₃ = 0`, which drops the cube to
degree `≤ 6` while the tail is already `≤ 6`.

**So `deg p ∈ {9} ∪ {0,…,6}`: 7 and 8 are never the degree of a crossing polynomial.**
The issue's reading — "degree 8 = one shared point at infinity, degree 7 = two" — does not
survive: a cubic Bézier has only *one* point at infinity to share, and sharing it costs
three.

That does **not** put degrees 7 and 8 out of reach. `crossing_Pconstructible` asks only
that `β` be a root of `p`, so `p` may be a proper multiple of the target polynomial. See
"the corrected route" below.

## Fact 3: the reachable nonics form a hypersurface, not everything

Up to an affine change of the plane, a plane cubic that is singular and meets the line at
infinity in one triple point is either

* `Y² = X³ - λX²` — Weierstrass: crunode for `λ < 0`, acnode for `λ > 0`, cusp at `λ = 0`;
  drawn by the cubic pair `s ↦ (s² + λ, s³ + λs)`; or
* `Y = X³` — the degenerate case, whose singularity is the cusp at infinity.

Proof sketch: the triple point `Q` at infinity is either a smooth point of `C`, in which
case `Z = 0` is its inflectional tangent and `C` is in Weierstrass form; or `Q` is the
singular point, in which case it must be a cusp — a node has two parameter preimages,
which cannot both sit at the single parameter `s = ∞` — and `C` is `Y = X³`.

Feeding the first through an arbitrary Bézier `Γ t = (u t, v t)` gives exactly

    p = c·(v² - u³ + λu²),   u, v cubics,

i.e. monically **`p = M³ + λM² + v²` with `M` monic cubic and `v` cubic**: `3 + 1 + 4 = 8`
parameters against the `9` coefficients of a monic nonic. The second family is smaller
still (`p = M³ + v`, codimension 2). So the reachable nonics are a hypersurface.

Two independent counts agree:

* *Parameters.* `(x, y)`: 8. Drawable cubics `F`: `10 - 2` (leading form a perfect cube)
  `- 1` (singular) `= 7`. Affine redundancy: `6`. Total `8 + 7 - 6 = 9`, against `10` for
  a nonic with scale. Codimension `1`.
* *Cohomology.* Restriction `H⁰(ℙ², O(3)) → H⁰(ℙ¹, O(9))` is `10 → 10` with a
  one-dimensional kernel (the equation of `C` itself), so its image is `9`-dimensional.
  The missing linear condition is readable off: if `C` is nodal with node parameters
  `t₁ ≠ t₂`, the image is exactly `{p : p t₁ = p t₂}`.

The count in the issue (`8 + 9 - 6 - 1 = 10`) omits the "leading form is a perfect cube"
condition, which is codimension `2`; with it the count is `8 + 9 - 2 - 1 - 6 = 8`, plus
scale, `9`. **That is why every hand attempt came out exactly one coefficient short: the
shortfall is intrinsic, not an artefact of the substitution chosen.**

The cuspidal cubic named in the issue as "the cheapest candidate" is worse than the nodal
one, not better: `λ = 0` loses a parameter and leaves codimension `3`.

## What is formalised

`nonicVal_root_Pconstructible` in `Pptc/Basic.lean`: every real root of

    M(t)³ + λ·M(t)² + v(t)²   (M monic cubic, v cubic, all coefficients P-constructible)

is P-constructible. This is the exact reachable family — the honest content of "degree 9"
— and it is proved the way the sextic is: cross `Γ t = (-M t, v t)` against
`Δ s = (s² + λ, s³ + λs)`, read `M β` off the crossing, and finish with the cubic
`M t - M β`.

One case escapes the crossing. When `λ > 0` the origin is an **acnode** of
`Y² = X³ - λX²`: a real solution of the equation that the real parametrisation misses (it
would need `s² = -λ`). It occurs exactly when `M β = 0`, and then `β` is a root of a monic
cubic with P-constructible coefficients and is P-constructible outright. That is why the
proof splits on `M β = 0`.

## The corrected route to 7, 8 and 9 — and where it stops

Since `p` need only *vanish* at `β`, a target `P` may be multiplied up to degree 9:

| target | multiplier | unknowns | equations |
|---|---|---|---|
| `deg P = 7` | monic quadratic `t² + bt + c` (no reality condition needed) | `8 + 2 = 10` | 9 |
| `deg P = 8` | `t - r` | `8 + 1 = 9` | 9 |
| `deg P = 9` | none; instead a Tschirnhaus shift `t ↦ t + s` | `8 + 1 = 9` | 9 |

In each case the requirement is `P · g = M³ + λM² + v²`, and the counts are square or
better, so a solution exists generically. Writing `M = t³ + m₂t² + m₁t + m₀`, the top two
equations are triangular (`m₂`, then `m₁`, in closed form), but the remaining seven — in
`m₀, λ, v₃, v₂, v₁, v₀` and the multiplier's parameter — are genuinely coupled and
quadratic. **No triangular closed form for them was found.** The sextic's charm, each
substitution absorbing exactly one coefficient, does not reproduce: at degree `9` the
ordinate is squared *and* cubed, so `v` and `M` contest the same equations.

That is the open problem this investigation leaves. It is not the problem the issue posed
("find the right substitution"); it is a definite system of `7` equations in `7` unknowns
whose solvability by field operations plus roots of degree `≤ 6` — and whose *real*
solvability — is what degrees `7`, `8` and `9` now turn on.

Two remarks on that system:

* The `b`, `c` of the degree-7 multiplier are **unconstrained**: the extra roots of
  `P · (t² + bt + c)` are cropped away by the isolation box, so the multiplier is allowed
  real roots. That is one more degree of freedom than a naive reading suggests.
* Depressing `P` first buys the same `m₂ = 0` normalisation it buys at degree `6`, and no
  more: the `t⁶` coefficient is contested by `m₀`, `λ` and `v₃²` at once, which is exactly
  where triangularity breaks.

## Answers to the issue's checklist

- [x] *Degree 7 — explicit pair whose leading terms cancel twice.* No such pair exists: a
      Bézier cubic has one point at infinity, and sharing it drops the degree to `6`.
- [x] *Degree 8 — same with one cancellation.* Likewise impossible. `7` and `8` are not
      cancellation cases, they are divisibility cases.
- [x] *Degree 9 — cuspidal or nodal?* **Nodal.** The cusp is codimension `3`, the node
      codimension `1`, and the node is what `nonicVal_root_Pconstructible` uses. Real
      solvability is not automatic: the acnode branch is genuinely missed by the real
      parametrisation and needs the case split.
- [x] *Does depressing help?* Only for the top two coefficients; see above.
- [ ] *Does 9 subsume `root_Pconstructible_le_eight`?* Not yet; that needs the `7 × 7`
      system solved.
- [x] *Sign/branch conditions.* Exactly one: `M β ≠ 0` at the wanted crossing. It is a
      case split, and the escaping case is trivial.
