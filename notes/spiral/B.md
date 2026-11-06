# B: read-outs beyond the basic spiral box

Stream B of `pptc/PLAN-spiral.md` (wave 3). Pure mathematics; PowerPoint not opened; no Lean, no `Defs.lean`
change, nothing committed. Backend: **Wolfram MCP** for every identity and every number below (30-40 digit working
precision); **no Python**. Labels: [Proof] paper argument, [Wolfram] checked in Wolfram Language,
[Heuristic], [Open]. Classes E / R / N / ? as in plan §1. Inputs read: PLAN, W, O, I1, I2, I3, I4, F2, F3, F4, L,
`ppt-curves/M.md` (§1.1, §2 dictionary T1-T6, §3.1), `sheared-sine-intersections.md` (§1, §3a, §3b),
`offset-inversion-tangent-angle.md`, `Defs.lean`, `Basic.lean`/`Box.lean`/`BoxGraph.lean` (statements only).

Notation. Unit spiral `γ(ψ) = ψ e^{iψ}` (counter-clockwise; a warp arc is `C + λ e^{iκ} γ` over a window
`[ψ_a, ψ_b]`, possibly mirrored). `c = √(1+ψ²)`, `A(ψ) = ½(ψc + asinh ψ)` (arc length), `φ = ψ + arctan ψ`
(tangent angle), `κ = (ψ²+2)/c³`. `ℓ = (cos β, sin β)`. `d` is measured toward the centre of curvature
(left normal of the Defs `unitNormal`; O).

## Findings summary

| # | read-out (new curve, then what is read) | equation | class | reachable roots |
|---|---|---|---|---|
| 1 | box of a spiral window (or of its non-uniform image `M·γ`), interior extremum | `θ tan(θ−β) = 1`, value `|Mᵀℓ| θ²/√(1+θ²)`, `β` = direction of `Mᵀℓ` | **N** (T3 `tan y + y = k`, and `(x+β)tan x = 1`, i.e. T2 with `λ = 1`) | every `θ ∈ [0.055, ≈47)` that lies in a drawn window; the global-extremum condition of F2 §6 is **removed** by item 9 |
| 2 | same, at a window end | end coordinates | E | all P-constructible `ψ_a, ψ_b` |
| 3 | box of a whole-arc offset, `d ≤ 1/2` or `d < 0`, either sign | `V ∓ d` (max: `V − d`, min: `V + d`, for `d` toward the centre of curvature) | **N** (= row 1, shifted by a P-constructible `d`) | as row 1 |
| 4 | box of the offset **uniform** spiral at its cusp, `d > 1/2` | `c³ = d(c²+1)`, `c = √(1+ψ_c²)`; value `ℓ·P_d(ψ_c)` | **E/R**: `c²` = abscissa of (semicubical `y = x^{3/2}`) ∩ (line of slope `d` through `(−1, 0)`); value is trig of an algebraic angle | `d ∈ (d(ψ_a), d(ψ_b))`, `d(ψ) = c³/(c²+1)`; for `d = 1`, `c` = supergolden ratio 1.46557123…, `ψ_c = 1.0714005020…` |
| 5 | box of the offset of a **non-uniform** image, at its cusp | `d κ_M(ψ) = 1`, `κ_M = s_x s_y(ψ²+2)/speed_M³`; i.e. `d² s_x² s_y² (ψ²+2)² = speed_M⁶`, `speed_M²` = polynomial-times-`{1, cos 2ψ, sin 2ψ}` | **?** [Heuristic] (new numbers, unnamed, not proved irreducible) | several cusps per turn for suitable `(d, s_x/s_y)`; `diag(2,1)`, `d = 1`: `ψ_c = 0.45099…, 1.14774…` |
| 6 | box of a **restricted** piece (`restrict` to P-constructible window) | max over {interior stationary points} ∪ {`S ∩` window edges} ∪ {ends of `S`} | reduces to rows 1, 2 and to "spiral ∩ line" (R, I1) | — |
| 7 | `restrict` to a **degenerate** window (a line `x = k`), then `box_ymax` | the extreme (largest / smallest) crossing of `S` with a line | same classes as `S ∩ line`; **no isolation needed** | all crossings (selector) |
| 8 | box in a direction `β` taken from a spiral number | angle must be P-constructible (cos, sin, tan all P-constructible); every spiral number is | depth-2: `θ tan(θ − β₁) = 1` with `β₁` a row-1 root | e.g. `β₁ = 2.02875…`: `θ = 2.42053345642…` (max) |
| 9 | **sub-window** by `arc_of_length` from a non-vertex P-constructible start, then box | row 1 on `[ψ₀, ψ₁]`, `ψ₀, ψ₁` P-constructible | **N** (= row 1) | removes the "window ends before `R(θ)`" restriction; answers W's open "isolate one sub-arc" |
| 10 | `arc_of_length` along the **uniform spiral** from any P-constructible `ψ₀`, endpoint read | `A(ψ₁) − A(ψ₀) = x`, i.e. `A(ψ₁) = c`, `c` any P-constructible | **R** (parabola arc inversion, `BoxGraph.lean`) | all |
| 11 | `arc_of_length` along the **offset** uniform spiral, endpoint read | `A(ψ₁) − d(ψ₁ + arctan ψ₁) = c` (O's OI-S) | **?** (O) | window `Δφ < π`, cusp-free (`ψ₀` any P-constructible, not only the vertex) |
| 12 | `arc_of_length` along a **non-uniform** image, endpoint read by two boxes | `Λ_M(ψ₁) − Λ_M(ψ₀) = x`, `Λ_M = ∫ speed_M dψ` (not elementary) | **?** [Heuristic] | `Δφ_M < π`; e.g. `diag(2,1)`, `ψ₀ = 2π`, `x = 3`: `ψ₁ = 6.72513904792829459260…` |
| 13 | same, along the **offset** of a non-uniform image | `Λ_M(ψ₁) − d φ_M(ψ₁) = c` | **?** [Heuristic] | `Δφ_M < π`, cusp-free |
| 14 | `arc_length` of the uniform spiral between intersection points (roots of I1-I4) | `λ[A(ψ_b) − A(ψ_a)]` | **R** (an elementary function of P-constructible `ψ`; no new equation) | any pair of roots with both points P-constructible |
| 15 | `arc_length` on the offset spiral between intersection points | `G_d(ψ_b) − G_d(ψ_a)`, `G_d = A − d(ψ + arctan ψ)` (cusp-free) | **R** | as 14 |
| 16 | `arc_length` of a non-uniform image between P-constructible points | `∫ speed_M` | **?** [Heuristic] (non-elementary integral at P-constructible limits) | any |
| 17 | arc lengths of **other** curves (circle, ellipse, sine, …) between spiral-intersection points | `f(root)` with `f` an existing arc-length function | depth-2 (stream C): a new number only because the root is | — |

Headline results.

1. **No new equation class comes from boxing the plain spiral, however it is restricted, offset or imaged
   uniformly.** Every box value is a T3/T2 number (row 1), a P-constructible shift of one (row 3), an end
   coordinate (row 2), a spiral-meets-line coordinate (row 6) or a trig-of-algebraic cusp value (row 4).
2. **Non-uniform scaling is invisible to the box but visible to offsets and arc length.** `ℓ·(Mγ) = (Mᵀℓ)·γ`
   keeps the box on the old family (W), but offset and arc length are not affine-equivariant. The offset's cusp
   equation (row 5) and the arc-length integral (rows 12, 13, 16) are genuinely new, with unnamed classes.
   This corrects the impression (W §6) that non-uniform images add nothing: that is true for the box and for
   intersections only.
3. **`arc_of_length` isolates any sub-arc with P-constructible ends** (row 9), and so fixes the window caveat
   of F2 §6 and the open point of W §2. It does so for every curve, not only the spiral.
4. **The spiral's own arc length is a dead end for new numbers** (rows 10, 14, 15): it is the parabola's.
5. **Directions are not a restriction** (row 8): every number the spiral produces is itself a legal angle.
6. No B read-out reaches T1, T2 (with `λ ≠ 1`) or T6 [Proof for rows 1-4, 6-10, 14-15; rows 5, 12, 13, 16 are
   [Open]].

## 0. Hypothesis audit (the constructors as they stand in `Defs.lean`)

- **`box_xmax/ymax`** need `PConstructibleCurve A`, `IsCompact A`, `A.Nonempty`.
  - Warp arc: continuous image of `Icc` ⇒ compact. Non-empty.
  - `restrict`: `S ∩ closed rectangle` is compact when `S` is; non-empty only if the window really meets `S`. This
    has to be argued case by case (the window bound is P-constructible but the crossing is not known in
    advance; pick rational bounds from the numerics).
  - `arc_of_length`: `γ '' Icc a b`, compact and non-empty by definition.
  - `offset`: `offsetParam γ d '' Icc a b` with `γ` C¹ and regular, so the normal is continuous and the
    image is compact [Proof].
- **`arc_of_length`** on a spiral sub-window `[ψ₀, ψ₁]`: `hsub` ⇔ window inside the drawn window; `hinj` ✓
  (radius `λψ` is strictly increasing; the same holds for any invertible linear image); `hdiff`, `hint` ✓;
  `hx₀, hy₀`: the start point `C + λe^{iκ}ψ₀e^{−iψ₀}` is P-constructible iff `ψ₀` is
  (`cos_Pconstructible`, `sin_Pconstructible`, and `ψ₀ = |z − C|/λ` conversely, W §5). `b` is free; `γ`
  may run in either direction. So **the available start points are exactly the P-constructible `ψ₀` in the drawn
  window, not only the vertex.**
- **`offset`** on a warp arc or on a sub-arc made a curve by `arc_of_length`: `a < b`, `himg` tautological,
  `hinj` ✓, `hseam` vacuous (`γ b ≠ γ a`), `hdiff`/`hC1` ✓, `hreg`: speed of the image is
  `λ c > 0` (uniform) or `speed_M > 0` (non-uniform, since `(cos − ψ sin, sin + ψ cos)` has modulus `c ≥ 1`
  and `s_x, s_y ≠ 0`). The cusp of the *offset* does not violate `hreg`, which concerns `γ`, not `P_d`
  [Proof, consistent with O §1.6].
- **`arc_length`**: both plane endpoints P-constructible (I-streams give this for every root that is isolated);
  `hinj`, `hdiff`, `hint` as above.

## 1. Boxes of the curves that I1-I4 and O produce

### 1.1 General principle for `restrict` + box [Proof]

Let `K = S ∩ Window` be compact, `ℓ` a direction. A maximiser `z*` of `ℓ·z` on `K` is one of
(a) an interior point of `S ∩ int(Window)` where `S` is smooth: then `ℓ·γ' = 0`, a stationary point of `S`
itself; (b) a non-smooth point of `S`, e.g. an end of the arc or a cusp of an offset; (c) a point of
`S ∩ ∂Window`, i.e. a point of `S ∩ line` for one of the four window lines.
Case (a) gives row 1 for the spiral (and the same `θ` for its offset, O §1.4). Case (c) gives a coordinate
of a spiral-meets-line point, which `inter_x/inter_y` already reads. Case (b) is E or the cusp rows. Hence
**boxing a restricted spiral piece reads nothing that the unrestricted box and the line intersections do not**. The
only new thing is a *selection*: `sSup` picks the largest of finitely many candidates. Window edges in the
box direction (`x = x_max` for `box_xmax`) just return the P-constructible bound.

Examples. (i) Spiral window with a window that cuts the cap: `box_xmax` returns `x_max` (the bound) or the
crossing's coordinate. (ii) Offset-spiral piece cut by `y ≥ y₀`: the piece's box reads either `V ∓ d` or the
coordinate where `P_d` crosses `y = y₀` (class **?**, O §1.5), which `inter_x` gives directly.

### 1.2 The degenerate window: the extreme crossing of a curve with a line [Proof from the constructors, Wolfram example]

`restrict` takes `xmin xmax` without an ordering hypothesis, so `xmin = xmax = k` is legal and
`S ∩ {x = k}` is a finite compact set. `box_ymax` of it is the y of the **highest** crossing, with no window
chosen to isolate one root. For the unit spiral on `[2π, 4π]` and `x = 1`
(`ψ cos ψ = 1`): crossings `ψ = 7.7241531923964114330044838…` and `11.0859017287717858110215396…`, with
`y = ψ sin ψ = 7.6591476379299331362050700…` and `−11.0407072753508535947291334…`
[Wolfram, 30 digits]. `box_ymax` returns 7.659…, `box_ymin` the second. This is a selector for the extreme
roots of line-meets-curve equations, useful where isolation by a rectangle is hard (F2: the fold at
`A = 2.95359…`, near-coincident roots). Class: the same as the line intersection (R for the spiral, I1).
It is not spiral-specific [Heuristic: worth a Lean lemma check, the statement is a direct use of `restrict` and
`box_ymax`].

### 1.3 The offset spiral, whole-arc, both signs of `d`

Formulas (O, re-verified): `P_d = e^{iψ}[ψ(1 − d/c) + i d/c]`, `P_d' = (1 − dκ)γ'`. Three cases, with
`d_c(ψ) = c³/(c²+1)` increasing from 1/2 to ∞.

- **`d < 0`, or `0 ≤ d ≤ 1/2` (or `d < d_c(ψ_a)`):** no cusp. Stationary points of `ℓ·P_d` are the spiral's
  (`θ tan(θ−β) = 1`). At such a point the tangent is ⟂ ℓ and the normal is `∓ℓ`:
  **max: `V − d`, min: `V_min + d`** (positive `d` toward the centre of curvature)
  [Wolfram: β = 7/10, d = 1/5: max at θ = 7.1226703818927907970, `ℓ·P_d − V = −0.2000…0`; min at θ = 4.0818…,
  `ℓ·P_d − V_min = +0.2000…0`, 28 digits]. A mirror flips the sign of `d` (O). Class **N** (row 1 shifted).
- **`d_c(ψ_a) < d < d_c(ψ_b)`:** one cusp at `ψ_c`. `ℓ·P_d` has a local extremum there when
  `ℓ·γ'(ψ_c) ≠ 0` (the factor `1 − dκ` changes sign). Max if `ℓ·γ'(ψ_c) < 0`. The cusp coordinate competes with
  the regular stationary values and the end values; a short sub-window (item 9) around `ψ_c` makes the cusp
  the global extremum.
  - Cusp equation: `dκ = 1` with `κ c³ = ψ²+2 = c²+1`, i.e. **`c³ = d(c²+1)`** [Wolfram, `True`]. Put
    `X = c², Y = c³`: `Y = d(X+1)` meets `y = x^{3/2}` (`power_law`, rational exponent), so `c` and
    `ψ_c = √(c²−1)` are P-constructible (R/E).
  - `d = 1`: `c³ = c² + 1`, `c` = **supergolden ratio** 1.4655712318767680266567312252…, `ψ_c =
    1.0714005020088367281846470878…`; `d = 2`: `ψ_c = 2.1368939538692881481661759904…` [Wolfram].
  - Box value, `d = 1`, `β = 0` (max since `ℓ·γ' < 0`): `ℓ·P_d(ψ_c) = −0.43600253215850141069663651902338…`;
    `NMaximize` on `[9/10, 13/10]` agrees to 28 digits [Wolfram]. Trig of the algebraic angle `ψ_c`: **R**
    (`cos_Pconstructible`). Nothing new.
- **`d > d_c(ψ_b)`:** `1 − dκ < 0` on the whole window; the offset runs backward, no cusp, same stationary
  points, same values `V ∓ d`.

So the box of an offset **uniform** spiral is E/R/N and adds nothing beyond row 1.

### 1.4 Non-uniform images: box invisible, offset not [Proof + Wolfram]

Box: `ℓ·(Mγ) = (Mᵀℓ)·γ`, so the stationary points and the value are the unit-spiral ones with direction
`β = arg Mᵀℓ` and a P-constructible positive factor `|Mᵀℓ|` (W §6). Because every P-constructible `β` is
available by a uniform rotation, `M` gives nothing new here. The same holds for its offset at a regular
stationary point: `V_M ∓ d` (the identity `P_d' = (1 − dκ_M)γ_M'` holds for every regular curve).

But offset and arc length are not equivariant under `M`. For `M = diag(s_x, s_y)`, `γ_M = (s_x ψ cos ψ, s_y ψ sin ψ)`:

- numerator of the curvature: `x'y'' − y'x'' = s_x s_y(ψ² + 2)` [Wolfram, residual 0], so `κ_M > 0` always and
  `κ_M = s_x s_y (ψ²+2)/speed_M³`;
- `speed_M² = ½[(s_x²+s_y²)(1+ψ²) + (s_x²−s_y²)((1−ψ²)cos 2ψ − 2ψ sin 2ψ)]` [Wolfram, residual 0];
- unlike the uniform case (`κ` strictly decreasing, `c³/(ψ²+2)` monotone), `κ_M` **oscillates**:
  `diag(2,1)`: `κ_M` = 0.5, 1.159, 1.752, 0.297, 0.134, 0.344, 0.182, 0.0514, 0.173 at
  ψ = 0, 0.5, 1, 1.5, 2, 3, 4, 5, 6, with maxima 2.4266 (ψ = 0.8222) and 0.6072 (ψ = 3.3958) [Wolfram].
  So a given `d` can produce several cusps, two or more per turn.
- **Cusp reading (row 5).** `M = diag(2,1)`, `d = 1`: cusps at `ψ = 0.45099092282950630243948926563` and
  `1.14774226994581721565119530732` [Wolfram, 30 digits]. With `ℓ = (1,0)`, `ℓ·γ_M'(1.1477…) = −1.272 < 0`, so a
  local maximum: `box_xmax` of the offset of the sub-arc `ψ ∈ [1, 13/10]` is
  **`0.20637303672853549430756984829376…`**, attained at `ψ = 1.147742269945817215645…` (cusp)
  [Wolfram, `NMaximize` 40 digits, endpoints lower]. This number is `x_M(ψ_c) − d·y_M'/speed_M` at the root of
  `d² s_x² s_y² (ψ²+2)² = speed_M⁶`, an equation in `ψ` and `cos 2ψ, sin 2ψ` with polynomial
  coefficients. No algebraic or single-harmonic collapse, unlike the uniform `c³ = d(c²+1)`.
  Class **?** [Heuristic: not proved irreducible; no F4-type argument was attempted].
  Contrast with `sheared-sine-intersections.md` §3a, where the cusp equation is algebraic in `(sin t, cos t)` and
  the cusp box value is "inverse trig of an algebraic number"; here it is not.
- Parameters: `(d, s_x/s_y)` free (two P-constructible parameters). Hypotheses ✓ (§0).

### 1.5 `arc_of_length` pieces

- **Along the spiral:** a piece `[ψ₀, ψ₁]` with `ψ₀` P-constructible and `A(ψ₁) = A(ψ₀) + x/λ`.
  `ψ₁` is P-constructible (item 4 below). Box of the piece: row 1 or row 2. Nothing new.
- **Along the offset spiral:** O's route; box reads either the far end (monotone window, `Δφ < π`) or the cusp.
  See §4.
- **Boxes of the arc's far end are exact reads of `ψ₁`:** for the uniform spiral `ψ₁` is already a P-constructible
  number, for the offset and for the non-uniform image it is new (§4).

## 2. Boxes in a direction that is not a P-constructible angle

- **What the constructors allow.** `rotate` is by whole degrees, but `rotate_PConstructibleCurve` gives
  rotation by **any P-constructible angle** (`ψ`, matrix `(cos ψ, −sin ψ; sin ψ, cos ψ)`), and
  `affineMap_PConstructibleCurve` gives every P-constructible invertible matrix. A box direction is only ever a
  direction `Mᵀℓ` with P-constructible entries. Conversely a direction with P-constructible `tan β` has
  P-constructible `β` (`arctan_Pconstructible`). So the reachable directions are exactly those with
  `β ∈ P`; **a direction with non-P-constructible angle is not reachable** [Proof from Basic.lean].
- **What this includes now.** Every number produced by the spiral is P-constructible by definition of the class, so it
  is a legal angle in radians: a T3 root `β₁`, a line-meets-spiral root, a cusp `ψ_c`, and also derived angles
  such as the tangent angle `φ(ψ) = ψ + arctan ψ` at any P-constructible `ψ`. There is no need for "scale
  tricks" with a root-dependent parameter; `rotate_PConstructibleCurve` consumes `β₁` directly. Plan §2's "tan x = x is not
  in the family because β would depend on the root" is unaffected: the *family parameter* must be fixed in
  advance, a previously obtained root is allowed.
- **Depth-2 examples [Wolfram, 40 digits].** `β₁ = 2.0287578381104342235769711247347…` (root of `tan x = −x`,
  a box output). Box of the unit spiral in direction `β₁`: `θ tan(θ − β₁) = 1`:
  `θ = 2.4205334564220098737006199697287…` (max, `θ − β₁ = 0.392 ∈ (0, π/2)`), value
  `θ²/√(1+θ²) = 2.2371357668283428899686577…`; and the min-type root `θ = 5.3549665950046224248894817193…`
  (`θ − β₁ = 3.326 ∈ (π, 3π/2)`). Note `tan β₁ = −β₁`, so the direction vector is `(1, −β₁)`: P-constructible
  without trigonometry. Class **N** at each level (a row-1 equation with a P-constructible `β` that is itself a
  row-1 root). The closure of this tower is stream C's question.
- **Reachability.** Roots with `θ ∈ [0.055, ≈47)` that lie in some drawn window (F2). With item 9 the
  global-extremum condition drops.

## 3. Arc lengths between intersection points

- **Uniform spiral, line/conic/other roots (rows 14, 17).** For roots `ψ_a < ψ_b` of any I1-I4 equation with
  both points isolated (so P-constructible), `arc_length` gives `λ[A(ψ_b) − A(ψ_a)]`,
  `A(ψ) = ½(ψ√(1+ψ²) + asinh ψ)`. `asinh` is `log` of a P-constructible number (`log_Pconstructible`,
  `sqrt_Pconstructible`), so the value is an elementary function of already-P-constructible numbers:
  **R, no new equation class** [Proof]. Example: roots of `ψ sin ψ = 1`: `1.1141571408719300873005…` and
  `2.7726047082659912339535…`; arc length (unit) `3.64408725686332702546588964133088…`; next pair
  `2.7726… → 6.4391172384172464617245…`: `17.30236822037935053818241095479…` [Wolfram, 25 digits; matches
  `NIntegrate` of `√(1+ψ²)` to 25 digits].
- **Offset spiral (row 15).** Cusp-free window: length `G_d(ψ_b) − G_d(ψ_a)`,
  `G_d = A − d(ψ + arctan ψ)` (O). With the intersections of `P_d` itself with `y = 1`, `d = 1/5`:
  roots `1.1806997814681873175687550…, 2.7058824430784362209604453…`; length
  `2.973454506113498460878542777870…`, equal to `NIntegrate` of `|1 − dκ|c` to 30 digits [Wolfram]. Across a cusp the
  length is a sum of pieces, still elementary. **R.**
- **Other curves between spiral roots (row 17).** `arc_length` of a circle, ellipse, sine, … between two points that
  the spiral delivered is `f(root)` with `f` the existing arc-length function (an elliptic integral for the
  ellipse and the sine). New numbers only if the roots are; no new equation. Stream C.
- **Non-uniform image (row 16).** `Λ_M(ψ_b) − Λ_M(ψ_a) = ∫ speed_M dψ` with
  `speed_M² = ½[(s_x²+s_y²)(1+ψ²) + (s_x²−s_y²)((1−ψ²)cos 2ψ − 2ψ sin 2ψ)]`. For `s_x = s_y` this is `s c`
  and the integral is `A`. Otherwise the radicand is polynomial-in-`ψ` times `{1, cos 2ψ, sin 2ψ}` and
  Wolfram's `Integrate` for `diag(2,1)` returned no closed form within 8 s (a longer try hit a gateway
  timeout) [Wolfram, negative evidence only]. Class **?** [Heuristic]. The values at P-constructible
  limits are numbers of the form "integral of the root of a trig polynomial": no known name.
- **Offset of the non-uniform image:** length `Λ_M − d Δφ_M` on a cusp-free window, `φ_M = atan2(s_y(sin ψ + ψ cos ψ),
  s_x(cos ψ − ψ sin ψ))` [Wolfram: `diag(2,1)`, `d = 1/5`, window `[2π, 6.72513904792829459260]`:
  `Λ = 3.0000000000000000000`, `Δφ_M = 0.85320060483173803975841…`, `NIntegrate |1−dκ|speed` minus
  `Λ − dΔφ_M` = `8·10⁻¹⁹`, limited only by the truncated endpoint].

## 4. `arc_of_length` from a non-vertex start, then box

All of these use a P-constructible start `ψ₀` in the drawn window and a P-constructible `x`.

- **Uniform spiral (row 10).** `A(ψ₁) − A(ψ₀) = x/λ`. Put `c = x/λ + A(ψ₀)`; `A(ψ₀)` is P-constructible, so `c`
  ranges over all of `P` as `x` does. The equation `A(ψ₁) = c` is solved by the parabola: `arc_of_length`
  along `y = x²/2` from the vertex, `box_xmax` reads the slope `ψ₁` (`BoxGraph.lean`,
  `arc_xendpoint_Pconstructible`). Class **R** [Proof]. A non-vertex start adds nothing; neither does a start
  at a spiral∩line root (the start point is P-constructible, hence so is `ψ₀`). The two-box read-out of
  `Q = γ(ψ₁)` on a spiral window with `Δφ < π` is not even needed.
- **Offset uniform spiral (row 11).** `G_d(ψ₁) − G_d(ψ₀) = x/λ'`, with `G_d(ψ₀)` P-constructible, so
  `½(ψ c + asinh ψ) − d(ψ + arctan ψ) = c` for all P-constructible `c`: O's OI-S, class **?**, window
  `ψ₁ − ψ₀ < π − Δarctan` and `1 − dκ > 0`. Starting at the cusp point `ψ_c(d)` (P-constructible by §1.3) is
  allowed; so is any non-vertex `ψ₀` in the drawn window. Examples in O §3.
- **Non-uniform image (row 12).** `Λ_M(ψ₁) − Λ_M(ψ₀) = x'` with `x' = x/λ` (the factor `λ` is a P-constructible
  scale). Window condition: the tangent angle `φ_M` turns by `< π`, so that two non-parallel P-constructible
  directions have the arc's endpoint as their extreme; then two `box` calls give `Q`, and `ψ₁` follows from
  `ψ₁ = |M⁻¹(Q − C)|/λ` (algebraic in the P-constructible coordinates). Example [Wolfram, 35 digits]:
  `diag(2,1)`, `ψ₀ = 2π`, `Λ_M(ψ₁) − Λ_M(2π) = 3`: **`ψ₁ = 6.7251390479282945926040533051757…`**,
  `Δφ_M = φ_M(ψ₁) − φ_M(2π) = 0.853 < π` ✓. Class **?** [Heuristic: the inverse of a non-elementary
  integral; not compared against the Jacobi/elliptic inverses in `Jacobi.lean`].
- **Offset of the non-uniform image (row 13).** `Λ_M(ψ₁) − d φ_M(ψ₁) = c`: the analogue of OI-S; class **?**.

Why none of this is T1-T6. `T1/T2` (`tan x = λx + μ`, `(λx+μ)tan x = 1`) need `sin x` and `cos x` of the same
argument against a line; the spiral enters only through `ψ`, `cos ψ`, `sin ψ` inside `ℓ·γ`, and the box fixes
`λ = 1` (`ℓ·(Mγ)` is always the unit-spiral coordinate). `T6` needs a power spiral. [Proof for the box rows.]

## 5. Anything else that reads a number off a spiral-derived curve

- **Box of a union.** No constructor; `sup` of a union is the larger of two sups, which is already one of the two
  read-outs. A whole warped glyph (spiral edge + circle + radial segment) is a union in PowerPoint but not a
  single `PConstructibleCurve`; nothing is lost. [Proof]
- **`box_width/height` (`Box.lean`).** `x_max − x_min`: a difference of two row-1/2 values. Nothing new.
- **Self-crossings of the offset.** The swallowtail crossing of `P_d` with a later turn is an `inter_x/inter_y`
  of two sub-arcs of one offset curve. `d = 1`: `P_d(ψ_a) = P_d(ψ_b)` at `(ψ_a, ψ_b) =
  (0.93580904817158550024203…, 3.5345452863374720031686138…)` [Wolfram, 30 digits]. A two-unknown equation;
  class **?** [Heuristic]. Not in O or I4.
- **The offset of an offset.** For cusp-free windows `P_{d₁}` offset by `d₂` is `P_{d₁+d₂}` (same normals): nothing
  new. When the first offset has a cusp, `hreg` fails and the second offset is not allowed.
- **Closed glyph outline offset.** PowerPoint offsets an outline with joins; `offset` needs `C¹` velocity, so a
  warped ◢ with its corners is not directly covered. [Open: depends on whether the user wants an `offset`
  with joins in `Defs.lean`.]

## Hypothesis checklist per row (compact)

| row | compact | non-empty | injective / regular | other |
|---|---|---|---|---|
| 1, 2 | warp arc | ✓ | n/a | window contains `θ` |
| 3, 4 | `offsetParam γ d '' Icc` | ✓ | `γ` regular, injective | cusp inside the window for 4 |
| 5 | same | ✓ | `speed_M > 0` | `ℓ·γ_M'(ψ_c) < 0` for a max |
| 6, 7 | `S ∩` closed window | argue per case | n/a | rational window bounds |
| 9 | `γ '' Icc` | ✓ | strictly increasing radius | ends P-constructible, inside the drawn window |
| 10-13 | as 9 | ✓ | as 9; offset: [Heuristic] for general `d` | `Δφ < π` to read the endpoint |
| 14-16 | arc | ✓ | injective | both plane endpoints P-constructible |

## Item 9 in detail: sub-windows and the "global extremum" condition [Proof + Wolfram]

F2 §6 requires the drawn window to end before `R(θ)`, the next return of the value `θ²/√(1+θ²)` in direction `β`.
Reason: `f(ψ) = ψ cos(ψ − β)` has local maxima of growing height, so earlier maxima are lower than `V` and later ones are
higher. The only obstruction is the upper end. **With `arc_of_length`:** start at a P-constructible point just above
`θ` (any rational `q ∈ (θ, R(θ))` inside the drawn window) and run backward to the window start (both ends
P-constructible), or start at any P-constructible `ψ₀ ≤ θ` and run to `q`. The piece is a curve in its own
right, compact, and `box_xmax` reads `V` exactly. Example [Wolfram]: `β = 343/50`, `θ = 7.0018598669481901779…`,
`V = 6.93152444886142411264…`, but on the full window `[2π, 4π]` the maximum is the end value
`4π cos(343/50)` (MaxValue), since `R(θ) = 12.1779074763519816… < 4π`. On `[13/2, 15/2]` the maximum is `V` to 28 digits.
`restrict` can also isolate the cap by a small rational rectangle around it, because adjacent turns are `2πλ` apart. So the
condition becomes "θ ∈ a drawn window", and the F2 list of "fragile" roots no longer needs mixed rows for the
box families (the other families are unaffected).

## Other things noticed

- **Non-uniform images are not "just placement" for offsets and arc length.** W §6 and I1 say a non-uniform
  spiral adds nothing beyond "spiral ∩ affine partner"; that is right for intersections and for the box, wrong for
  offset (cusp equation, row 5) and for arc length (rows 12, 13, 16). This enlarges the scope gap of I2/F3
  (general position) to include offset and arc-length read-outs.
- **Supergolden ratio.** The unit-spiral cusp at `d = 1` is `c = 1.4655712318767680266…`, the real root of
  `c³ = c² + 1` (a small, well-known algebraic constant); `ψ_c(1) = √(c²−1)`.
- **Degenerate-window selector (§1.2)** works for any compact curve and any direction: it deserves a one-line check
  in Lean; if sound it simplifies several isolation arguments (F2's fold cases).
- **Cusp counts.** For `diag(2,1)` and `d = 1` there are two cusps with `ψ ≤ 3`; more may appear at larger
  `ψ` (the scan used start points 0.3-3.8 only) [Open].
- **Reflection of the Defs normal.** For a clockwise (mirrored) arc, `d > 0` moves outward, and cusps then occur
  for `d < −1/2` in the sign convention of `unitNormal`; O's convention is for the counter-clockwise spiral. Any
  Lean statement should be phrased with `|d|` or with the orientation made explicit.
- **Open:** (a) non-irreducibility of rows 5, 12, 13, 16 (an F4-style argument for offset and integral partners);
  (b) injectivity of `P_d` for windows longer than one revolution, needed for `arc_of_length` on long offset arcs;
  (c) whether a Lean lemma for `restrict` to a line + `box` should be added (§1.2); (d) PowerPoint routes for
  rows 5, 12 are the same warp arcs with a `scale_x ≠ scale_y` step, so no new UI claim, but they have not been tested.
