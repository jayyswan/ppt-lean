# W: windows and normal form of the reachable spiral arcs

Stream W of `pptc/PLAN-spiral.md`. Pure mathematics plus font files; PowerPoint was not opened.
Backends: **Wolfram MCP** for the symbolic identity and every 20-digit number marked [Wolfram];
**Python (fontTools, `fractions`)** for glyph outlines and the exact rational window tables marked
[Measured-font] (exact rational arithmetic on integer font coordinates, no floating-point claims).
Scripts: `...\scratchpad\W\{fonts,edges,cover,scan}.py`.
Labels: [Proof] [Wolfram] [Measured-font] [Heuristic] [Open].

## Findings summary

1. **Edge law [Proof + Wolfram].** A straight glyph edge with ink-box data
   `u = u₁ + a·s`, `v = v₀ + h·s` (`s ∈ [0,1]`, `a = Δu > 0`, `h = |Δv|`, `v₀ = lowest v on the edge`)
   goes under Warped Circle (`C` centre, `R = W/2`, `ρ = R/2`, clockwise from 9 o'clock) to
   exactly
   `z(ψ) = C + λ·e^{iκ}·ψ·e^{-iψ}`, `ψ ∈ [2πq₁, 2πq₂]`,
   `q₁ = a(1+v₀)/h`, `q₂ = q₁ + a`, `λ = R·h/(4πa)`, `κ = 2π(q₁ − u₁) − π`.
   (Wolfram: `Simplify` of `Z(s) − rhs(s)` is `0`; `ψ(1) − ψ(0) = 2πa`; `ψ(1)/ψ(0) = 1 + h/(1+v₀)`.)
   So every reachable arc is **a window of the single curve `ψ e^{∓iψ}` (`r = ψ`), mirrored and
   similarity-transformed** (rotation `κ`, scale `λ`, mirror = `scale_x(−1)`). The general `r = A + Bθ`
   is the same window up to a rotation by `A/B` (here `A/B = ρ/B`-type constant absorbed in `κ`), so
   `A` carries no extra information. A *falling* edge (v decreasing with u) is the mirror image.
2. **Window constraints [Proof].** `q₂ − q₁ = a ≤ 1` (one arc never turns more than one revolution:
   the angular span is `2πa ≤ 2π`), and `ψ₂/ψ₁ = 1 + h/(1+v₀) ≤ 2` (the band `r ∈ [R/2, R]` has ratio 2,
   fixed because the inner ratio stays at the default 50 %). Hence the **`[θ₀, 2θ₀]` claim in plan §0 is
   only the special case `v₀ = 0, h = 1`**; in general the window is `[2π a(1+v₀)/h, +2πa]`.
   For the ideal glyph (any rational `(a, h, v₀)`) the reachable windows are exactly
   `{[2πq₁, 2πq₂] : q₁ < q₂ ∈ ℚ, q₂ − q₁ ≤ 1, q₂ ≤ 2q₁}`
   (take `v₀ = 0`, `h = (q₂−q₁)/q₁`). The real fonts give a finite subset of this (§1).
3. **The "windows cover (0, 4π]" claim is false as stated and true in a weaker form [Measured-font].**
   - A fixed font and glyph has *discrete* `a`, so the windows `[2πa, 4πa]` do not tile. Example:
     Segoe UI Symbol ◢ row `n=1` gives `[2π, 4π]`, `n=2` gives `[2.8174…, 5.6348…]`
     (`a = 239/533`); gap `(5.6348, 6.2832)`, width `0.648358708996017366` rad [Wolfram].
     Other glyphs fill gaps: ▲ (`a = 1/2`, windows `[π, 2π]`).
   - Union over {◢ ▲ ╱ / in Segoe UI Symbol, Cascadia, Consolas, Arial} × rows `n ≤ 6`: no interior
     gap above `ψ = 2π·0.0614 = 0.386` (156 windows); the smallest `ψ₁` is `2π·0.06145 = 0.386`
     (`n = 6`). Larger `n` reaches smaller `ψ`; `ψ → 0` only as `n → ∞` (never the origin).
   - **Not unlimited sup 4π for these glyphs**: for `v₀ = 0, h = 1` the top is `4πa ≤ 4π`.
4. **Beyond 4π: yes, [Measured-font] and [Proof] (`q₂ ≤ 2a/h`).** Need `a > h` (an edge flatter than the
   ink-box diagonal) or a high-lying edge.
   - Text rotated 90° / 270° (Text Direction) swaps the roles: `(a, h, v₀) → (h, a, u₀ or 1−u₀−a)`
     [Heuristic: P1 saw the slope change; ink-box normalisation under rotation not measured, **[Open]**].
     Then Consolas ╱ gives `[2π·1.1656, 2π·2.1656]` (`ψ₂ = 13.6`), Segoe UI Symbol `/`
     `[2π·1.2224, 2π·2.2224]`, and the tiny stub edges of rotated ╱ reach `q₂ = 32.55` (`ψ₂ ≈ 204`).
   - Unrotated, flat slanted edges exist in the polygon-only glyph sets (exact rationals):
     Cascadia U+23A `a=.1225,h=.01173,v₀=.988`, `q₂ = 20.89` (`ψ₂ ≈ 131`);
     Arial U+05A7 `q₂ = 19.53`; Cascadia U+20AE `a=.844,h=.1056`, `q₂ = 11.6 to 13.4` (`ψ ≈ 73–84`).
     (Scan of 2402/527/712/703/594 polygon-only glyphs; a few top entries are near-degenerate slivers,
     e.g. `h = 6·10⁻⁴`, which are theoretical rather than usable.) At large ψ the arc is nearly a circle
     of radius ψ, so these are essentially "circle arcs with a tiny pitch".
   - **Mixed font sizes / baseline shift / character spacing in one text box** change the ink box
     (`Wtot, Htot`) while the glyph keeps its own size: `a = w/Wtot`, `h = H/Htot` independently,
     so `a/h` is unbounded (a huge tall `|` next to a small ◢ makes `h ≈ 1/k`, `ψ₁ ≈ πk`). [Heuristic;
     needs ink box of the whole text; **[Open]**]. With typed character spacing `s ∈ ℚ`,
     `a = w/((n−1)(adv+s)+w)` takes rational values densely in `(0,1)`, so the union of
     `[2πa, 4πa]` over rational `a` *is* all of `(0, 4π]` (each ψ lies in a window with `a ∈ [ψ/4π, ψ/2π]`).
   - **Multiple turns of one arc: no.** `u ∈ [0,1]` maps to at most 360°; the spiral never passes the
     seam twice. Concatenating edges does not continue the spiral (v resets from 1 to 0 at the next
     glyph). The reverse warp direction is just the mirror image, covered by `scale_x(−1)`.
   - **Other presets, not circle pour [Spec + Heuristic, spiral exactness unmeasured].**
     `textArchUpPour` (default `adj1 = 180°`, `adj2 = 50 %`): arcs sweep +180°, so window length `πa`
     and `ψ₁ = πa(1+v₀)/h`, ratio ≤ 2. **`textArchDownPour` has default `adj2 = 25000`** (read from
     `pw.xml`; sweep −180°): `ρ = R/4`, ratio ≤ 4, `ψ₁ = πa(1+3v₀)/(3h)`, so ◢-type edge gives
     `[π/3, 4π/3]`, reaching close to the origin and a longer ratio than circle pour. Worth a probe.
5. **Endpoints are P-constructible [Proof, via existing lemmas].** `q₁, q₂ ∈ ℚ`, `π` is P-constructible
   (`pi_Pconstructible`), so `ψ₁, ψ₂` are. `cos`, `sin` of a P-constructible argument are P-constructible
   (`cos_Pconstructible`, `sin_Pconstructible`, `Basic.lean` 2652/2657), and `λ, κ`-rotation are built from
   `R`, `h/a`, rationals times π. Hence both plane endpoints
   `C + λ e^{iκ} ψ_j e^{-iψ_j}` are P-constructible. Injective (ψ>0, `r = ψ` strictly increasing),
   differentiable and integrable on the compact window, so the `arc_length` / `arc_of_length` hypotheses
   hold for the full-edge parametrisation. Window length `½(ψ√(1+ψ²) + asinh ψ)|` is the parabola arc length
   (M.md §3.1). **Sub-windows from `restrict`**: a cut point whose plane coordinates are P-constructible has
   `ψ = |z − C|/λ` P-constructible too (ψ is the distance to the centre), conversely every P-constructible
   `ψ* ∈ window` is cuttable by the line `x = ψ* cos(ψ*−β)` (P-constructible). Isolating exactly
   `[ψ₁, ψ*]` by one rectangle needs a rectangle meeting the arc once in the right pieces: [Heuristic],
   not always possible for a full-turn window. The spiral never reaches the centre (`ψ₁ ≥ 2πa > 0`; `adj2 = 0`
   drops the warp, P1).
6. **Non-uniform images [Proof].** `M ∈ GL₂(P)` (any matrix is `R·D·R'` with P-constructible parts):
   - Box: `ℓ·(Mγ) = (Mᵀℓ)·γ` is exact linear algebra, so M.md §1.1 is right; only the **direction** of
     `Mᵀℓ` and a positive factor change. Stationary condition `ψ tan(ψ−β) = 1`
     (β = direction of `Mᵀℓ`), value `ψ²/√(1+ψ²)`. [Wolfram, 25 digits: `M = [[2,1],[1/2,3]]`, window `[6,11]`:
     `max (Mγ)_x = 15.248892797257035957…`, `max (Mᵀe₁)·γ` equal, difference `0` to 23 digits.]
     Every direction with P-constructible `tan β` is reachable by a *uniform* image (rotation by a
     P-constructible angle, which Lean itself derives from `scale_x/scale_y`), so the diagonal `scale_x ≠ scale_y`
     adds **no new read-out values**. Which `β` has an *interior* extremum: those with
     `β = ψ₀ − arctan(1/ψ₀)` for some `ψ₀` in the window (maximum) or `+π` (minimum), a set of angular
     size `≈ 2πa` each; windows with `a ≥ 1/2` see max or min in every direction.
   - Intersections: lines map to lines, so `Mγ ∩ L = M(γ ∩ M⁻¹L)` is again line-spiral; for a circle the
     preimage is a P-ellipse of arbitrary axis ratio and tilt, and for another spiral the relative matrix
     `M₁⁻¹M₂` is general. So non-uniform images matter only *as a way to place the partner* (circle becomes
     ellipse), not as new equation classes beyond "spiral ∩ general P-ellipse" and "spiral ∩ affine spiral",
     i.e. I1 / I4 must treat ellipses and general GL₂ pairs, and a non-uniform spiral alone adds nothing.
   - Shape: with `ξ = x/s_x`, `η = y/s_y`: `√(ξ²+η²) = atan2(η,ξ) − β + 2πk` (Archimedean in the stretched
     coordinates); polar form `r(φ) = ψ·√(s_x²cos²(ψ+β) + s_y²sin²(ψ+β))`, `tan φ = (s_y/s_x) tan(ψ+β)`,
     which is not Archimedean (not a similarity) [Proof sketch: for large ψ it is nearly an ellipse of fixed
     eccentricity ≠ circle, while an Archimedean spiral becomes circular]. A non-square box gives the same
     class (affine image, P1 finding 5).
7. **Exact by-products of each warped glyph [Proof from the map; corners Measured by P1/P1b].**
   - Horizontal edge at height `v` → circular arc of radius `(R/2)(1+v)` about `C`, angular width
     `2π·(edge width / ink width)`. Full circle if the edge spans the whole ink width.
   - Vertical edge at `u` → radial segment on the ray at angle `π + 2πu` (clockwise from 9 o'clock)
     from radius `(R/2)(1+v_lo)` to `(R/2)(1+v_hi)`.
   - ◢ ◣ (Segoe UI Symbol, Cascadia): one spiral window `[2π, 4π]` (rising ◢, falling ◣ = mirror), the
     bottom edge = **full circle radius R/2**, and the vertical edge = **radial seam segment**
     `[C−(R,0), C−(R/2,0)]` (the 9 o'clock ray, from `R/2` to `R`). The spiral's ends are exactly the
     two ends of that segment. ◤ ◥ give a **full circle of radius R** instead of R/2. ■ (rectangle) gives
     both circles and the seam segment.
   - ▲ (all four fonts): bottom edge = full circle `R/2`; two spiral edges, `u ∈ [0,½]` rising and
     `[½,1]` falling, windows `[π, 2π]` each, mirror images in the 9–3 o'clock axis, meeting at the apex
     `C + (R, 0)` (radius R at angle 2π) and at the 9 o'clock point `C − (R/2, 0)`. Exact for Arial
     (apex `x = 1014`, `(1014 − 304)/1420 = 1/2`) and others.
   - ╱ Consolas: parallelogram `(0,−514),(966,1884),(1126,1884),(160,−514)`; both long edges have
     `a = 483/563`, `h = v-extent 1`, **the same window `[2π·483/563, 4π·483/563]`** and are rotations of
     each other by `2π·160/1126` (a rational angle); bottom stub = arc of radius R/2 of angle
     `2π·160/1126`, top stub = arc radius R of the same angle. Arial `/` is similar with `a = 425/569` and `424/569`,
     rotated relative to each other by `2π·145/569`. Cascadia ╱ has 6 vertices: long edges
     `a = h = 43/48` with `v₀ = 5/48·…` and `0` (`q₁ = 20855/20856` i.e. 0.99995, and `15351/13904`),
     plus short vertical radial segments at `u = 0` and `u = 1`.
   - A glyph with several horizontal edges at rational heights (═, ☰, ⊟) gives **concentric circles of radii
     `(R/2)(1+v)`, v rational**; glyphs with several vertical edges (⦙, ▥) give **rays at rational
     fractions of a turn**, i.e. exact angles `2π·rational` (cyclotomic).
   - Use for I4: spiral ∩ these circles occurs only at the spiral's end points (`r` runs monotonically from
     one band edge to the other), so the circles/segments are anchors rather than cutting curves, except for
     windows with `v₀ > 0`, whose ends lie on circles `(R/2)(1+v₀)` and `(R/2)(1+v₀+h)` that the glyph can
     also draw.
8. **Idealization category.** Everything above is the ideal map (category (b) for the interior of the arc,
   exact corner anchors); I added no new measurement. The only new empirical assumptions are flagged:
   ink box of the *whole* row (taken from P1, measured for `HELLO`), ink-box rule under rotated text, and
   the 360° / 352.64° span rule (choose a box size from the P1b list).

## 1. Windows from installed fonts [Measured-font, exact rationals]

Window `[2πq₁, 2πq₂]`; rows of `n` identical glyphs, ink box = from the first ink left to the last ink right,
no kerning, edge on the first glyph. `a = w/((n−1)·adv + w)` (w = glyph ink width, adv = advance).

| font, glyph | n | a | q₁ | window (rad) |
|---|---|---|---|---|
| Segoe UI Symbol ◢ | 1 | 1 | 1 | [6.2832, 12.5664] |
| Segoe UI Symbol ◢ | 2 | 239/533 | 239/533 | [2.8174, 5.6348] |
| Segoe UI Symbol ◢ | 3 | 239/827 | 239/827 | [1.8158, 3.6316] |
| Cascadia ◢ | 2 / 3 / 4 | 7/15, 7/23, 7/31 | = a | [2.9322, 5.8643], [1.9123, 3.8246], [1.4188, 2.8376] |
| ▲ Segoe / Consolas / Arial / Cascadia | 1 | 1/2 | 1/2 | [π, 2π] (two mirror edges) |
| ▲ Consolas, Cascadia | 2 | 1/4 | 1/4 | [π/2, π] |
| ▲ Segoe UI Symbol | 2 | 401/1684 | = a | [1.4962, 2.9924] |
| ▲ Arial | 2 | 710/3447 | = a | [1.2942, 2.5884] |
| ╱ Consolas | 1 | 483/563 | = a | [5.3904, 10.7807] |
| ╱ Segoe UI Symbol | 1 | 1851/1946 | 3592791/3592316 | [6.2840, 12.2605] and v₀=0.0484 edge [6.5848, 12.5612] |
| ╱ Cascadia | 1 | 43/48 | 20855/20856 and 15351/13904 | [6.2829, 11.9116], [6.9371, 12.5658] |
| / Arial | 1 | 425/569, 424/569 | = a | [4.6931, 9.3861], [4.6820, 9.3640] |
| / Consolas | 1 | 343/426 | = a | [5.0590, 10.1180] |
| / Segoe UI Symbol | 1 | 688/841, 686/841 | = a | [5.1401, 10.2802], [5.1252, 10.2503] |
| / Cascadia | 1 | 201/254 | = a | [4.9721, 9.9443] |

Note Segoe UI Symbol ╱ has `a` far from the nominal because the outline has chamfered corner stubs.
Wolfram values to 20 digits: Arial `/`: `[4.69306459675100923145, 9.38612919350201846289]`;
Consolas ╱: `[5.39037034345957418891, 10.78074068691914837782]`.
Pure ◢/◣ ▲ windows are the only ones with `q₁ = a` (so the edge begins at the band's inner circle).

## 2. Open points

- [Open] Ink-box normalisation for a row of unequal glyphs (the numbers above assume the whole-row bbox).
- [Open] Ink box under 90° / 270° text direction, character spacing and mixed sizes; each would add whole
  families of `(a, h, v₀)` (see §Findings 4). One PowerPoint probe each would settle them.
- [Open] Whether the arch pour presets map the same way (spiral exactness, default inner ratios 50 % / 25 %).
- [Open] `restrict` isolating a single sub-arc of a full-turn window with one rectangle.
- [Open] Rounding of advance widths in multi-glyph rows (P1: effective scale quantised to ≈ 0.1–0.25 % at
  large sizes) would perturb `a` slightly for rows, not for a single glyph.

## Other things noticed

- `q₁ = a` exactly iff the edge starts at the inner circle with full height; this is the case for ◢ ◣ ▲ and
  slashes with `v₀ = 0`, and is why a single glyph's spiral always begins on circle `R/2` and ends on `R`.
- A bug-prone point for D: the spiral drawn has `ψ` shifted by `κ`, and the "natural" parameter is
  `|z − C|/λ` not the angle, so the constructor should be parametrised by the distance (ψ) of its end
  points, with `ψ_i = 2π q_i`.
- The two long edges of a parallelogram glyph (╱, /) are the same spiral window rotated by a rational turn,
  so a single glyph can give a **rotated pair of congruent spirals**, handy for spiral ∩ rotated spiral (I4).
- ◣ (falling edge) and ◢ (rising) give both chiralities without any mirroring, so `scale_x(−1)` is not
  needed to get a counter-clockwise spiral.
- Circle pour with `adj2` clamped at 100000 degenerates to concentric circles; with default handle the band
  ratio is exactly 2.
