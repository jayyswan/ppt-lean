# Sheared sines: what intersections reach

A follow-up to `sheared-sine-inversion.md`, taking the open item "intersections of sheared sines
with each other and with other curves".

I chose this direction over the other open items because it is the only one with a realistic
chance of a *positive* result, such as a new classical constant:

- "Are the inverse values new numbers?" cannot be settled without transcendence theory.
- "Two-step compositions" re-runs a collapse argument we already have.

Labels:

- **[Proof]**: a complete argument on paper, not formalized.
- **[Wolfram]**: checked in Wolfram Language.
- **[Heuristic]**: a natural route has been ruled out, not every route.

## 1. The one-trig-function constraint [Proof]

A sheared sine is a linear image of the sine graph, plus a translation. Its coordinates are
affine combinations of `1`, `t` and `sin t`. Phase shifts are allowed, but the phase only
moves `t` too, so each curve carries **one** trigonometric function of its parameter,
`sin(t + φ)`, never `sin t` and `cos t` together.

So intersecting a sheared sine with another curve gives exactly one of these equations, in the
single unknown `t`. Here `s = sin(t+φ)` and `L₁, L₂` are affine in `(t, s)`.

| Other curve | Equation solved | Examples |
|---|---|---|
| line | `L₁(t, s) = 0` | Kepler, Laplace limit, Dottie (all in `Basic.lean`) |
| algebraic curve `P = 0`: ellipse, polynomial graph, Bézier (implicitly cubic), rational power law | `P(L₁(t,s), L₂(t,s)) = 0`, a polynomial relation `Q(t, sin(t+φ)) = 0` | `t sin t = k` (hyperbola `xy = k`), `sin t = t²` |
| `exp_two` | `L₁(t,s) = 2^{L₂(t,s)}` | `sin t = 2^{−t}` |
| another sheared sine | `sin(L₁(t,s) + φ') = L₂(t,s)` | `sin(t + k sin t) = …`, nested Kepler |

**Offsets.** Offsetting a sheared sine adds `d·(normal)`, whose components are
`(affine in cos t) / √q(cos t)`. So offset curves are the only drawable way to get `sin t` and
`cos t` into the same equation, and they always come with the `1/√q` factor.

I know of no classical constant in rows 2–4. Each row is a family of reachable transcendental
numbers, but none corresponds to a named problem.

## 2. The near miss: `tan x = x`

`tan x = x` has first positive root `x ≈ 4.4934` [Wolfram]. It is the eigenvalue equation for:

- the zeros of the spherical Bessel function `j₁`;
- clamped-hinged beams;
- the bound states of a finite spherical well.

It needs `sin` and `cos` of the same argument, which is exactly what §1 says one curve cannot
supply. The question is how close we can get.

**Reduction 1, to one quartic [Proof + Wolfram].** Square `sin t = t cos t` and use
`cos² = 1 − sin²`:

  `tan t = ±t`  ⟺  `(1 + t²) sin²t = t²`.

This is the polynomial form `Q(t, sin t) = 0` from row 2, with `Q(x, y) = (1 + x²) y² − x²`.
So the roots of `tan t = t` are the intersections of the plain sine graph with the quartic curve

  `y = x / √(1 + x²)`  (equivalently `y = sin(arctan x)`).

The extra roots of `tan t = −t` (the first is `≈ 2.0288`) are cut away with `restrict`.
[Wolfram: `Q(t, sin t)` vanishes at both roots to 28 digits.]

**So if `y = x/√(1+x²)` were drawable, `tan x = x` would follow at once.** The curve is not
among the current constructors:

- It is not a polynomial graph.
- It is not an affine image of a rational power law. Those have the shape `Yᵠ = k Xᵖ`, with a
  cusp or a smooth point at the vertex. The quartic instead has a **node** at the origin, with
  tangents `y = ±x`, and **two** horizontal asymptotes `y = ±1`.
- It is not a cubic Bézier, since it has degree 4.
- Offsets of conics have degree 6 or 8.

**Reduction 2, the circle involute [Proof + Wolfram].** The involute of the unit circle is

  `I(θ) = (cos θ + θ sin θ, sin θ − θ cos θ)`.

Its y-coordinate vanishes exactly when `tan θ = θ`, so the roots are where the involute
crosses the x-axis [Wolfram: `I(4.4934…)` has y-coordinate 0 to 28 digits]. The involute is the
curve traced by unwinding a taut string from the circle. It is not an offset (offset distances
are constant), so it is not drawable either.

**Reduction 3, the quadratrix of Hippias.** In suitable units the quadratrix is
`x = y cot y`. Its intersection with the line `x = 1` is exactly `tan y = y`. This is the
classical curve the Greeks used to square the circle. It is not drawable here.

**Status [Heuristic].** Each of these is a natural route to `tan x = x`, and each needs a curve
we cannot draw. That is not a proof that `tan x = x` is out of reach. A sufficiently clever
combination of offsets, the `1/√q` factor in their normals, or bounding boxes of other curves
might still produce the equation. What *is* proved (§1) is that no single intersection of an
un-offset sheared sine with a line, a power law or `exp_two` gives it. One whose other curve is
the quartic above does give it, so the whole question becomes whether that quartic is drawable.

## 3. Offsets of sheared sines (follow-up 2, done)

**Setup.** Use the normal form `γ(t) = (−bt + sin t, at)`, with `a > 0`. Write

- `r = √((cos t − b)² + a²)` for the speed;
- `ν = (−a, cos t − b)/r` for the unit normal;
- `P_d(t) = γ(t) + d ν(t)` for the offset curve.

Similarities commute with offsets, so this normal form loses nothing.

**Key identity.** `γ · ν = a (t cos t − sin t) / r`, independent of `b`. So `tan t = t` says
exactly that the tangent line at `γ(t)` passes through the origin.

**Convention ("uniform").** A construction "gives `tan x = x`" if one fixed configuration of
curves yields the roots `t*` for infinitely many `k`, changing only the `restrict` window.
Parameters cannot depend on the unknown root.

### 3a. Bounding boxes of offsets give nothing new [Proof]

`P_d' = (1 − dκ) γ'`. So `ℓ · P_d(t)` is stationary only where:

- `ℓ · γ' = 0`, i.e. `cos t` is a fixed constant; or
- `κ = 1/d`, at a cusp of the offset, where `κ = a sin t / r³`.

Both conditions are algebraic in `(sin t, cos t)`, so `t*` is an inverse trig function of an
algebraic number. The extreme coordinate is then linear in `t*` plus algebraic terms:
elementary, and never `tan t = t`.

### 3b. The reduction for algebraic partners [Proof]

Let `K` be the field of functions algebraic in `sin θ, cos θ, r`. These are all `2π`-periodic.
For an algebraic curve `Q = 0`, the function `f(t) = Q(P_d(t))` is a polynomial in `t` with
coefficients in `K`, because both coordinates of `γ` are linear in `t`.

Let `R(θ) = f` evaluated with `t := tan θ`. Then:

1. `R ∈ K(1/cos θ)`.
2. `R(t*) = f(t*) = 0` at every root of `tan t = t`.
3. Under the uniform convention, those roots, reduced mod `2π`, accumulate at `π/2`.
4. Multiplying by a power of `cos θ` clears the poles. The result is analytic near `π/2` with
   accumulating zeros, so it vanishes identically. Hence **`R ≡ 0`**.

That is, the partner curve must contain the whole parametrized curve

  `Γ_{a,b,d}(θ) = (−b tan θ + sin θ − d a / r,  a tan θ + d (cos θ − b) / r)`.

Conversely, if it does, every root is an intersection point. So:

> **Uniformly, `tan x = x` comes from an offset sheared sine meeting an algebraic curve if and
> only if that curve contains some `Γ_{a,b,d}`.**

Lines are the degree-1 case, and are therefore excluded too.

### 3c. What `Γ_{a,b,d}` looks like [Proof + Wolfram]

**Degree** [Wolfram: Gröbner elimination; each sample irreducible over ℚ]:

| `d` | Degree of `Γ` | Samples |
|---|---|---|
| `d = 0` | 4 | `(1,0,0)` gives `X² − Y² + X²Y² = 0`, the quartic of §2; also `(1, ½, 0)` |
| `d ≠ 0` | 12 | `(1,0,⅓)`, `(2,½,⅓)`, `(1,1,1)` |

**Asymptotes.** As `θ → ±π/2`, `Γ` runs to infinity along `(−b, a)` and approaches the two
**distinct parallel** lines

  `aX + bY = a − dρ`  and  `aX + bY = −a − dρ`,  where `ρ = √(a² + b²)`.

### 3d. Which drawable curves are excluded [Proof]

The parametrizing curve `{s² + c² = 1, r² = (c−b)² + a²}` is irreducible, so the Zariski
closure of `Γ` is irreducible. A drawn arc containing a piece of `Γ` must therefore lie on that
closure. Every **base** algebraic curve fails on asymptotes:

| Base curve | Real asymptotes |
|---|---|
| ellipse | none |
| polynomial graph of degree ≥ 2 | none |
| cubic Bézier | none (polynomial parametrization: one parabolic branch) |
| affine image of a power law `Yᵠ = kXᵖ` | none, or two *non-parallel* ones |

None has two parallel asymptotes. So **no** sheared sine, offset or not, meets a base algebraic
curve to give `tan x = x` uniformly. In particular this settles the question for every
`d ≠ 0`: offsetting the sine does not help against base curves.

### 3e. Still open

- **Offsets and affine images of offsets of base curves.** These are algebraic and *can* have
  parallel asymptotes. Offsetting a hyperbola by `±d` gives two pairs of them. So 3d does not
  rule them out.
  - Degree is the obvious first filter. Known offset degrees: parabola 6, ellipse 8, cubic
    graph and cubic Bézier about 10. None has an irreducible degree-4 component.
  - Degree 12 is not excluded by this.
  - Settling this needs a check of whether some `Γ_{a,b,d}` (degree 12) is an affine image of
    an offset of a drawable curve.
- **Non-algebraic partners:** `exp_two`, other sheared sines, and their offsets. Here `R` gets
  an essential singularity at `π/2`, and the 3b argument breaks.
- **Non-uniform constructions,** which use the root's location to place curves. These are
  excluded by convention only.

## 4. Suggested follow-ups

1. **Probe PowerPoint for `y = x/√(1+x²)`**, or any affine image of it. If some UI route draws
   this one quartic (a chart type, a trendline, a smoothing setting), `tan x = x`, the `j₁`
   zeros and the beam eigenvalues all become P-constructible.
2. **Offsets of sheared sines** are the only existing way to put `sin t` and `cos t` in one
   equation. Classify what their intersections and bounding boxes solve, keeping track of the
   `1/√q` factor. This is the only place a route to `tan x = x` could still hide among the
   current constructors.
3. Rows 2–4 of the table give families of new reachable roots, but none matches a named
   problem that I know of. A literature search for transcendental equations of the shape
   `Q(t, sin t) = 0` with small-degree `Q` might turn up applications.
