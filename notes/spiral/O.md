# O: the offset spiral as a curve, and offset inversion along it

Stream O of `pptc/PLAN-spiral.md`. No Lean, no Defs change. Backend: Wolfram MCP for every identity and number
(40-70 digit working precision); no Python. Labels: [Proof] [Wolfram] [Heuristic] [Open]. E/R/N/? as in plan §1.
Unit spiral `γ(ψ) = ψ e^{iψ}`; a warp arc is `C + λe^{iκ}·γ` (possibly mirrored), `λ` P-constructible (it contains `1/π`).

## Findings summary

1. **Closed form [Wolfram, residual 0].** With the Defs normal `ν = (-y', x')/speed` (left of travel; for the
   counterclockwise spiral, left = toward the centre, so `d>0` moves inward, `d<0` outward):
   `P_d(ψ) = e^{iψ}[ ψ(1 − d/c) + i d/c ]`, `c = √(1+ψ²)`; `ν = i e^{iφ}`, `φ = ψ + arctan ψ` (tangent angle).
   `speed γ = c`, `κ = (ψ²+2)/c³` (even, positive, `κ(0)=2`, decreasing), `P_d' = (1 − dκ)γ'`, `κ_d = κ/(1−dκ)`.
   `|P_d|² = ψ² + d² − 2dψ²/c` (algebraic) [Wolfram, 0]. Asymptotically `r ≈ ψ − d` [Heuristic].
2. **Cusps/folds [Proof + Wolfram].** `c³/(ψ²+2)` increases strictly from `1/2` to `∞` on `ψ ≥ 0`. So `d ≤ 1/2`: no cusp
   (`d = 1/2`: cusp only at ψ = 0); `d > 1/2`: exactly one cusp per side at `ψ_c(d)`, root of `d²(ψ²+2)² = (1+ψ²)³` (E,
   algebraic): `ψ_c(1) = 1.07140050200883672818…`, `ψ_c(2) = 2.13689395386928814816…` [Wolfram]. `d < 0`: never a cusp.
   For `ψ < ψ_c` the offset runs backward (swallowtail); beyond `ψ_c`, `1−dκ>0` again.
3. **Arc length [Proof + Wolfram].** On any window with `1−dκ>0`: `L = G_d(ψ₂) − G_d(ψ₁)`,
   `G_d(ψ) = ½(ψc + asinh ψ) − d(ψ + arctan ψ)`. Checked against numerical integration of the speed of the explicit offset
   curve for `d ∈ {1/5, −2, 2/5}`, windows `[1,3]`, `[2,7]`: residual 0 to ≥43 digits. Across a cusp the length is a sum of
   `|…|` pieces. With `ψ = sinh u`: `G_d = ½(sinh u cosh u + u) − d(sinh u + gd u)`: M.md's formula and sign convention are
   confirmed (`arctan sinh u = gd u`). Class **R** (`log`, `arctan` are P-constructible).
4. **Box of the offset spiral [Proof + Wolfram]: M.md is right; exact content.** Stationary points of `ℓ·P_d` are the spiral's
   `θ tan(θ−β) = 1` (same θ) or the cusp `ψ_c`. At a regular stationary θ the tangent is ⟂ ℓ, so `ℓ·ν = ±1` and the
   **box value is `V_spiral ± d`** [Wolfram: β=0.7, θ=4.08184774705857890126…, shift exactly 0.2 = d, φ−β = 3π/2]. At a cusp
   the extremum is `ℓ·P_d(ψ_c)`, trig of an algebraic angle (**R**). Nothing new: **E/R**. (A box of a *partial* arc reads the
   far endpoint: that is what inversion uses, §3.)
5. **Intersections [forms Proof; classes Heuristic].** With `w(ψ) = ψ − d(ψ − i)/c`, `P_d = e^{iψ}w`:
   - line: `ψ(1−d/c)cos(ψ−β) − (d/c) sin(ψ−β) = k`;
   - any conic: the I1 master equation with `θ, θ²` replaced by `w, w², |w|²`: `Re(A e^{2iψ}w² + B e^{iψ}w) + m|w|² + f = 0`.
   - **E:** circle centred at the spiral centre (`ψ²+d²−2dψ²/c = r²`), and `d = 0`.
   - The line through the centre is no longer E: `ψ + arctan(d/(ψ(c−d))) ≡ α (mod π)`.
   - **Everything else: ? [Heuristic].** One harmonic with weights algebraic in `(ψ, √(1+ψ²))`; eliminating `c` and `cos` gives
     an algebraic partner in `(ψ, sin(ψ−β))` of higher degree, not a drawable graph a priori. The I1/F3 reductions need weights
     `θ^p`, so they do not apply. Not proved irreducible (F4 left offset partners open).
6. **Legitimacy under the new `offset` [Proof, conditional on a spiral constructor].** For a warp arc `S₀ = γ_w''[a,b]` (a<b,
   window `ψ ∈ [2πq₁,2πq₂]`, never the origin): `himg` tautological; `hinj` (radius strictly increasing); `hseam` vacuous
   (`γ b ≠ γ a`); `hdiff`/`hC1` (smooth); `hreg` (speed `λc ≥ λ > 0`). All satisfiable, also for connected `restrict` or
   `arc_of_length` pieces. Offsetting a similarity image by `d` is the unit-spiral offset by `d/λ`; a mirror flips the sign of
   `d`; so every P-constructible `d` is available. Caveat: the two-sided window `ψ ∈ [−π/2, π/2]` is NOT injective
   (`z(π/2) = z(−π/2)`); use one-sided windows (the warp gives them). The spiral constructor is Stream D's decision.

## 2. The literal route (arc on the spiral, then offset it) is R and gives nothing
`arc_of_length` along the *spiral* fixes `A(ψ₁) − A(ψ₀) = x`, `A = ½(ψc + asinh ψ)`: the parabola arc length, so ψ₁ is already
the parabola-inversion value (R). Offsetting that arc and boxing reads `ℓ·P_d(ψ₁) = ψ₁cos(ψ₁−β) − d sin(φ₁−β)`, a
P-constructible function of a P-constructible ψ₁. No `d`-dependent equation is solved. [Proof] **R.**

## 3. The real route: offset the whole arc FIRST, then `arc_of_length` along the offset curve
(This is also task 3: `arc_of_length` directly on the offset spiral. It is legitimate and it is the only version that solves anything.)
1. `S₀` = warp arc; `S_d = offset S₀` with tracing `P_d` on `[a,b]` (item 6).
2. `arc_of_length` on `S_d`, tracing `P_d` on `[ψ₀, ψ₁] ⊂ [a,b]`: injective on the window ([Heuristic] for general d; holds for
   turn ≤ 1 revolution and cusp-free), differentiable, speed integrable (cusps allowed: only differentiability is asked),
   start `P_d(ψ₀)` P-constructible, length `x = ∫|1−dκ|c`.
3. The far end ψ₁ is unnamed; read it with two boxes. Let `Δφ = φ(ψ₁) − φ(ψ₀)`. On a cusp-free window `ℓ·P_d` increases iff the
   tangent angle `φ ∈ (β−π/2, β+π/2)` [Proof from `P_d' = (1−dκ)γ'`]. The endpoint maximizes `ℓ·P_d` for every direction
   `β ∈ [φ₁−π/2, φ₀+π/2]`, a cone of width `π − Δφ`.
   - **Δφ < π:** the cone holds two non-parallel P-constructible directions, hence the boxes give both coordinates of the endpoint
     `Q` (rotation by a P-constructible angle comes from the affine-image closure).
   - **Δφ ≤ π/2:** plain `box_xmax`/`box_ymax` in one frame.
   - **Δφ ≥ π:** fails (no direction has the end as its extreme).
   Since `φ = ψ + arctan ψ`, the window is `Δψ < π − Δarctan`, a bit under half a turn of the spiral.
4. From `Q` recover ψ₁ algebraically. With `r² = |Q − centre|²`, `c₁ = √(1+ψ₁²)`:
   `c₁³ − 2d c₁² − (1 − d² + r²) c₁ + 2d = 0` [Wolfram: residual 0 to 66 digits at five parameter sets]. A root of a
   P-constructible cubic isolated by `restrict` is reachable, so ψ₁ is P-constructible [Proof modulo root selection; `r²(ψ)` monotone on the window].

**Result.** For P-constructible `d`, `c`, a real root of

  **(OI-S)  `½(ψ√(1+ψ²) + asinh ψ) − d(ψ + arctan ψ) = c`**   (equivalently `½(sinh u cosh u + u) − d(sinh u + gd u) = c`, ψ = sinh u)

is P-constructible whenever it lies in a window `ψ₀ ≤ ψ < ψ₀ + (π − Δarctan)` that starts at a P-constructible point of a
drawn offset-spiral arc, with `1−dκ>0` on it. `c = x + G_d(ψ₀)` ranges over all P-constructible numbers because `x` does.
Any P-constructible ψ₀ gives a P-constructible start point (`cos ψ₀`, `sin ψ₀` are), not only the vertex; the point must still
lie on the drawn `S_d`, i.e. ψ₀ in the underlying warp window (F2: windows cover `[0.055, 4π]` for pure rows, `[0.76, 47]` with
mixed heights). Handed to B: non-vertex starts.

**Examples [Wolfram, 70-digit solve, 36 digits shown; ψ₀ = start, x = length, Δφ = tangent turn; cubic residual 0 in every row]:**

| d | ψ₀ | x | root ψ₁ | Δφ |
|---|---|---|---|---|
| 1/5 | 2π | 2 | 6.59994034420046837352680139670790837 | 0.3242 |
| −3/2 | 2π | 3 | 6.65443992909825102506851216102058… | 0.3799 |
| 1/3 | π | 1 | 3.46519900725043719326279976278… | 0.3508 |
| −1 | 3π | 1/2 | 9.47234080474610127437300492814… | 0.0481 |
| 1/2 | 4 | 1 | 4.26839879836767488968761463216… | 0.2832 |

(The longer printout in the session gave all roots to 36 digits; the truncated rows above agree with it.)

**Parameters reachable.**
- Cusp-free: all `d < 0`; `0 ≤ d ≤ 1/2` from any ψ₀ > 0; `d > 1/2` only for windows with `ψ₀ ≥ ψ_c(d)`. A start *at* the cusp point is a
  P-constructible point (ψ_c algebraic), so cusp-start arcs exist for every `d > 1/2`.
- Windows: ψ inside the warp window, and Δφ < π. Roots farther than about π above every available start cannot be reached in one step;
  choosing a closer P-constructible start (non-vertex) fixes this when the underlying window contains it.
- Uniformity in `(d, x)`: yes, same construction for all P-constructible `d`, `x`. The only `d`-dependence in the constraints is the cusp.

## 4. Reduction of (OI-S): ? [Heuristic], with anchors
- `d = 0`: parabola arc inversion, **R**.
- Dropping `−dψ` gives the parabola-offset equation `A − d arctan = x`, already reachable by the offset tower. (OI-S) is that minus
  `d ψ = d sinh u`, i.e. minus `d` times a catenary arc length (S(u) = cosh u). A curve realizing it would have
  `ds/du = cosh²u − d(cosh u + sech u)`, i.e. `(sinh u − d u, ½cosh²u − d cosh u)`-type, a trochoid-like curve that is no base curve and
  not an offset of one uniformly in d.
- Intersections give equations in `u` with one of `eᵘ` or trig (tangent-angle note §2), so a `u`-`gd u`-`sinh u` mix lies outside them.
- Non-uniform scaling of the parabola only rescales the A-part against the `gd` part; it never makes the `sinh u` term.
- **Verdict: ? (new, unnamed, not proved irreducible).** No tan-type reduction found; it does not reach T1, T2 or T6.

## 5. What failing routes give
- Literal route: only R.
- Arc across a cusp: legal for `arc_of_length` but no coordinate is monotone, so the endpoint cannot be read. It still gives the cusp
  point and cusp-start arcs.
- One box only with Δφ ≥ π/2: gives `ℓ·Q = ψ₁cos(ψ₁−β) − d sin(φ₁−β)`, transcendental in ψ₁; ψ₁ cannot be extracted without a second direction.
- Box of the whole offset spiral: `V ± d` plus cusp coordinates (item 4).

## Other things noticed
- Offsetting turns the line through the centre from E into a nontrivial one-harmonic equation, so the offset spiral differs from the
  spiral for intersections even though the box is unchanged.
- `d ↦ ψ_c(d)` is an algebraic family of P-constructible points on the offset spiral, usable as `arc_of_length` starts for all `d > 1/2`
  (the `d = 5` FindRoot run failed numerically; no claim made there).
- κ of the unit spiral is even and positive on the whole two-sided curve (κ(0) = 2).
- Not checked: injectivity of `P_d` for windows longer than one revolution, and large `d > 0`.
- Open: prove (OI-S) not reducible (F4-style, offset partners); look for hidden collapses of item 5 at special `d` (1/2, 1).
