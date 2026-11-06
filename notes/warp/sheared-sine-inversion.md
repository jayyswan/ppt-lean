# Sheared sines: what arc length and its inverse reach

What can be obtained from linear images of the sine graph by `arc_length`, and by
`arc_of_length` followed by reading off the far endpoint?

Every claim is labelled:

- **[Lean]**: proved in the repo.
- **[Proof]**: a complete argument on paper, not formalized.
- **[Wolfram]**: checked numerically or symbolically. Each check below was run in Wolfram
  Language, not Python.
- **[Open]**: not settled.

## 1. Normal form [Proof + Wolfram]

A general linear image of the sine graph is

  `γ(t) = (αt + β sin t, γt + δ sin t)`, plus a translation.

Write `a = (α, γ)` and `b = (β, δ)` for the two coefficient vectors. Then:

- **`b = 0`:** a line.
- **`a ∥ b`, including `a = 0`:** the curve lies on a line, and every arc length is
  elementary.
- **Otherwise:** apply four moves, each of which keeps everything P-constructible.
  1. Rotate `b` onto the positive x-axis. The angle is `atan2(δ, β)`, and every
     P-constructible angle is reachable.
  2. Scale by `1/|b|`. Arc lengths scale by `|b|`.
  3. Reflect in one or both axes.
  4. If needed, shift `t ↦ t + π`, which flips the sign of the shear.

  The curve becomes

  `γ̃(t) = (−b t + sin t, a t)`, with `b ≥ 0`, `a > 0`, and speed `√((cos t − b)² + a²)`.

**Unshifted (`b = 0`):** speed² = `a² + cos²t = (1 + a²)(1 − c sin²t)` with `c = 1/(1 + a²)`.
So the arc length is `√(1+a²) E(t, c)`: the sine wave's arc length is the second-kind
integral.

**Sheared (`b > 0`):** this is exactly the curve of `ThirdKindAll/Circular.lean`.
- That file takes `b = √((1−n)(−n))/(c−n)` and `a = √(c(1−c))/(c−n)`, with `n < 0` and
  `0 < c < 1`.
- The correspondence `(a, b) ↔ (n, c)` is a bijection, with the explicit inverse

  `S = √((1 + a² + b²)² − 4b²)`,
  `n = −(1 + a² + b² − S) / (2S)`,
  `c = (1 − a² − b² + S) / (2S)`,
  `c − n = 1/S`.

  [Wolfram: `FullSimplify` reduces both defining equations and `c − n = 1/S` to 0.]
- On 20 000 random points `(a, b) ∈ (0, 50)²`, this branch gave `n < 0` and `0 < c < 1` every
  time [Wolfram]. The other real branch never did.
- `b = 0` gives `n = 0`, `c = 1/(1+a²)`, matching the unshifted case above.
- Only square roots appear, so `(n, c)` is P-constructible whenever `(a, b)` is.

**Consequence.** Up to similarity, *every* sheared sine is a member of the single two-parameter
family `(n, c) ∈ (−∞, 0] × (0, 1)` that the third-kind proof already uses.

## 2. Forward arc lengths: nothing new [Lean + Proof]

`ThirdKindAll/Circular.lean` proves that `circG` is the arc length in the substituted variable
`θ`, where `t = T(θ) = 2 arctan(k tan(θ/2))`. Writing `Λ = √(c − n) · circG`:

  `Λ(θ) = E(θ) − F(θ) + (1 − n) Π(n, θ) + R(θ)`,

where every function has modulus `c`, and `R` is elementary: rational in `sin θ, cos θ, Δ`,
plus one `arctan`. [Wolfram: the derivative of my transcription of `circG` matches the speed
formula to 73 digits.]

A P-constructible endpoint gives a P-constructible `t` (from the y-coordinate `a t`), and so a
P-constructible `θ`. So every arc length of a sheared sine between P-constructible endpoints
is already a combination of `F`, `E`, `Π` at P-constructible arguments, plus elementary terms.
These are all available from `ThirdKindAll/Main`. Not formalized as one theorem, but each step
exists.

## 3. Inversion: the new functions [Proof]

Lay off a P-constructible length `σ` from the point at `θ = 0`. Starting anywhere else only
shifts `σ` by a constant that is already P-constructible. The y-coordinate `a t` is monotone,
so `box_ymax` reads off the endpoint, and `t`, hence `θ`, comes out P-constructible.

So the numbers obtained are

  `θ = Λ_{n,c}⁻¹(σ)`  for all `n ≤ 0`, `0 < c < 1`, and P-constructible `σ`.

This is a two-parameter family of inverse functions.
- At `n = 0` it is `E⁻¹`, which the ellipse already gives.
- For `n < 0` these are new functions. No previous analysis covered them.

**Offsets.** Offsetting by `d` adds `d·ψ(t)` to the arc length, where `ψ` is the tangent
angle. That enlarges the family to three parameters: `Λ + dψ`.

## 4. What the inverses provably are not [Proof + Wolfram]

Put `u = cos t` and `q(u) = (u − b)² + a²`. The arc-length differential is

  `ds = q(u) du / W`,  where `W² = (1 − u²) q(u)`,

on an elliptic curve. At the two points over `u = ∞`,

  `ds = ∓i (1 + B/u + O(u⁻²)) du`,  with `B = −b`

[Wolfram: series at `u = ∞`]. So `ds` has, at each of those points:
- a **double pole**, whose leading coefficient `∓i` never vanishes; and
- **residue** `±iB`.

(a) **Never the Jacobi amplitude.** Suppose `s = αF(θ') + const`, where `θ'` is any algebraic
function of `θ` (for instance a Landen transform). Then `ds` would be the pullback of a
holomorphic differential, hence holomorphic. The double pole rules that out. So no single
inversion along a sheared sine, or along its offsets (whose added `dψ` has no pole at `∞±`),
yields `am`.

(b) **Never a pure F/E combination when `b ≠ 0`.** `dF` and `dE` have zero residues, but
`ds` has residues `±iB ≠ 0`.
- So the inverse is never that of `αF + βE + const`.
- In particular it is never the inverse of the Jacobi Zeta function `E − (E/K)F`, nor of
  Heuman's Lambda as a function of `φ`.
- The Π part cannot be removed.
- Consistent with this: at `n = −√c`, the interchange relation
  `Π(n) + Π(c/n) = F + elementary` (DLMF 19.7.9) gives `Π(−√c) = ½F + elementary`.
  [Wolfram: the relation holds to about 76 digits at three test points.]
  The remaining `Λ − (E − ((1−√c)/2)F)` is a nonzero elementary function.
  [Wolfram: nonzero at `θ = 0.3, 0.7, 1.3, 2`, for `c = 2/5`.]

(c) **Offsets.** `ψ = arg L(u)` with `L(u) = (α + iγ) + (β + iδ)u`.
- `dψ` has zero residue at `∞±`, and its poles sit at the roots of `q`, where `ds` vanishes.
- So offsetting keeps the double poles and the residues `±iB` at infinity, and only adds new
  logarithmic terms elsewhere.
- (a) and (b) hold for the whole three-parameter family.

## 5. Open

- **Are the numbers `Λ_{n,c}⁻¹(σ)` new?** Showing that they are not P-constructible by some
  other route would need transcendence results that are out of reach. What *is* settled: they
  are not values of `am` or of the inverse of any pure `F`/`E` combination, by §4.
- **Two-step compositions**, where later parameters depend on earlier outputs. The earlier
  "parameters computed from u" analysis of `αF + βE + R` argued that this collapses: at fixed
  parameters, the output satisfies one equation of the form above. I expect the same
  argument to go through with the `Π` term added, but have not re-checked it.
- **Intersections** of sheared sines with each other or with other curves are not analysed
  here. Intersections with lines give the Kepler family, already in `Basic.lean`.
- **Named functions with residues.** I know of no classical inverse function whose
  differential has residues (as `Λ` does) that might coincide with some `Λ_{n,c}`. Not
  searched systematically.
- **Lean.** The normal form (§1) is pure algebra and easy to formalize. §4 needs differentials
  on an elliptic curve and would be a large project; the argument is classical.
