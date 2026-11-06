# D: draft constructor and decision packet for the Archimedean spiral

Stream D of `pptc/PLAN-spiral.md`. A decision packet for the user, **not** a `Defs.lean` edit. No repo Lean file was
touched, nothing committed, PowerPoint not opened. Inputs: PLAN-spiral (all sections), `CLAUDE.md`, `Defs.lean`,
`notes/spiral/{W,F1,F2,B,C,O,I4}.md`, skims of I1-I3, F3, F4, L, and `notes/ppt-curves/{P1,P1b}.md`.
Backends: **Wolfram MCP** for the two identities and the root count marked [Wolfram]; **`lean_run_code`** (scratch,
stand-alone, nothing written to the repo) for the two typecheck results marked [Lean-scratch]. Labels: [Proof]
[Wolfram] [Measured] [Lean-scratch] [Heuristic] [Open].

## Findings summary

1. **Recommended form: a single fixed curve, the open ray of the unit Archimedean spiral**, with similarity coming from
   the closure operations, exactly as `sine` and `exp_two` work:

   ```lean
   /-- The Archimedean spiral `r = t` (counterclockwise), at parameter `t`. -/
   noncomputable def spiralParam (t : ℝ) : ℝ × ℝ := (t * Real.cos t, t * Real.sin t)

   -- in `PConstructibleCurve`:
   | archimedes : PConstructibleCurve (spiralParam '' Set.Ioi 0)
   ```
   It is the one fixed curve; `restrict` / `arc_of_length` cut windows, `scale_x/y`, `rotate`, `translate_x/y` give
   every similarity, mirror image and (non-uniform) affine image.
2. **Why this is the right shape.** W's normal form says every drawn arc is a mirrored similarity image of a window of
   `r = ψ`. A window of a fixed curve is reachable from the fixed curve; the converse (everything the constructor gives
   is a similarity image of something drawn) holds inside the measured range. The two differences are the ψ-range
   (drawn: about `[0.002, 47]`; ray: `(0, ∞)`) and multi-turn extent. §2 argues **multi-turn extent adds nothing**
   [Proof for `inter_x/y`, argued for `box`], and the ψ-range is the **same kind of idealization the project already
   accepts for `sine`** (a glyph with about one period stands for the whole graph on ℝ). The one real difference:
   `sine`'s argument range is irrelevant under `scale_x`; the spiral's ψ-range is **not** removable by similarity, so the
   range over-claim buys genuinely more numbers (tail roots, §2.3). That is the decision to flag.
3. **Fallback if the user wants no range over-claim:** windowed form with rational turn-fractions and the W/F2 window
   law as hypotheses (form B2 below). It is exact to what PowerPoint draws, at the price of a hypothesis-heavy
   constructor and a Lean statement "for every `k`" no longer being provable.
4. **Evidence and category.** Category (b): corners 0.06-0.74 pt, between corners 2.8-5.4 % of R (F1). That is 2-6 times
   closer to its ideal than the `sine` glyphs (U+223F) are to a best-fit sine (12-19 % max / amplitude, P1b §4), with
   the caveat that the spiral's ideal is fixed by an explicit map while the glyph is compared with a best fit.
5. **Lean cost of the recommended form is small:** `speed spiralParam t = √(1+t²)` is a 10-line proof
   [Lean-scratch, compiled]; injectivity, `C¹`, nonvanishing speed are immediate; no existing proof pattern for `sine`
   needs to change (§5).
6. **What it unlocks:** the whole box family `θ + arctan θ = β + π/2 + kπ` (T3, `x tan x = 1`, `tan x = −x`), spiral ∩
   line/conic/graph/transcendental classes of I1-I4, offset classes of O/B, the parabola-inversion R-results. Nothing
   reaches T1, T2 (λ ≠ 1) or T6 (§4).

## 1. Candidate constructor forms

Notation: `S₁ = spiralParam '' Set.Ioi 0`. `ψ`-window `[a, b]` means `spiralParam '' Set.Icc a b`. Drawn windows (W, F2):
`ψ ∈ [Θa(κ+w₀)/h, + Θa]`, with (Θ, κ) = (2π, 1) Warped Circle, (π, 1) Arch: Warped / Warped Button, (π, 1/3) Arch: Warped
Down; hence ratio `ψ₂/ψ₁ ≤ 2` (Circle, Up) or `≤ 4` (Down), length `ψ₂ − ψ₁ ≤ 2π` (Circle) or `≤ π` (Up, Down).

### A. Fixed curve, open ray (recommended)

```lean
noncomputable def spiralParam (t : ℝ) : ℝ × ℝ := (t * Real.cos t, t * Real.sin t)

| archimedes : PConstructibleCurve (spiralParam '' Set.Ioi 0)
```
Variants of A:
- **A0** `Set.Ici 0` (includes the origin, the convention of `power_law` with `b > 0`).
- **A1** `Set.Ioi 0` (recommended): the origin is never on a drawn arc (W [Proof]: `ψ₁ ≥ 2πa > 0`; F2: `ψ → 0` only as
  `n → ∞`). With `Ioi`, a `restrict` window that contains the pole yields a non-closed set, so `box_*` correctly refuses
  it (same discipline as the negative `power_law`). Compact pieces come from `arc_of_length`, whose `γ '' Icc a b` is
  compact, or from `restrict` windows that avoid the pole.
- **A2** two-sided `Set.univ` (`t ∈ ℝ`): **do not use.** `spiralParam (π/2) = spiralParam (−π/2)` (O §1.6), so the curve
  self-crosses and a single tracing is not injective; it also draws the mirror arm, which one pour never does.
- **Orientation.** `spiralParam` is counterclockwise; the clockwise drawn spiral is `scale_x (−1)` (free). F1: Flip
  Horizontal in the Rotate menu is an exact mirror, so the mirror is also a UI step. Because `offset` and
  `arc_of_length` take the tracing `γ` as a parameter, the orientation of the normal is chosen at the point of use
  (`d` of either sign is allowed); B's warning (mirrored arcs have cusps for the opposite sign of `d`) is therefore a
  matter for the Lean proofs, not for the constructor.

*Soundness vs what PowerPoint draws.*
- Every point of `S₁` with `ψ ∈ [0.002, 47]` lies on a drawn arc (§2.1). Every `restrict`/`arc_of_length` piece with
  P-constructible ends inside a drawn window is a sub-arc of a drawn arc. [Proof from W + B row 9.]
- Over-claims: (i) ψ outside `[0.002, 47]` (measured); (ii) windows longer than one drawn arc; (iii) irrational/arbitrary
  P-constructible window ends that PowerPoint reaches only after `arc_of_length` (but see §2.2: those are in the class
  anyway).

### B. Windowed forms

**B1. P-constructible window ends** (a family, like `cubic_bezier` with P-constructible control points):
```lean
| archimedes_window (a b : ℝ) (ha : PConstructible a) (hb : PConstructible b)
    (h0 : 0 < a) (hab : a < b) :
    PConstructibleCurve (spiralParam '' Set.Icc a b)
```
Compact by construction (box applies directly). But it is **strictly weaker than A in nothing and stronger in nothing
that matters**: `restrict`+`arc_of_length` on A already gives every such window (a window of the ray with P-constructible
plane endpoints), and B1 additionally lets *every* P-constructible `a < b` be a single stroke, so it carries the same
range and multi-turn over-claim as A. Its only merit is that compactness is built in. Not recommended on its own.

**B2. Exactly what PowerPoint reaches (W normal form + F2 law)**, rational turn-fractions:
```lean
| archimedes_drawn (q₁ q₂ : ℚ) (h0 : 0 < q₁) (hlt : q₁ < q₂)
    (hwin : (q₂ ≤ 2 * q₁ ∧ q₂ - q₁ ≤ 1) ∨ (q₂ ≤ 4 * q₁ ∧ q₂ - q₁ ≤ 1 / 2))
    (hrange : 1 / 3 ^ 9 ≤ q₁ ∧ q₂ ≤ 7) :
    PConstructibleCurve (spiralParam '' Set.Icc (2 * Real.pi * (q₁ : ℝ)) (2 * Real.pi * (q₂ : ℝ)))
```
(first disjunct = Warped Circle/Arch Up windows, `ψ=2πq`; second = Arch Down. The numbers in `hrange` are placeholders
for the measured range `ψ ∈ [≈0.002, ≈47]`, `47/2π ≈ 7.5`; they would have to be fixed by the user.)
- *Sound:* every window with rational `(q₁, q₂)` satisfying `hwin` is the ideal window of some glyph edge (W Finding 2:
  `a, h, v₀` rational free ⇒ all such windows); real fonts, spacing and size lists give a **dense but finite** subset
  (F1/F2), so B2 over-claims windows in the gaps between the measured rationals and the exact value of `q`, not the set
  of numbers reachable (sub-windows by `arc_of_length` are P-constructible-ended anyway).
- *Under-claims:* mixed-height rows give `ψ₂ ≫ 2ψ₁`? No: `q₂ ≤ 2 q₁` still holds (ratio `1 + h/(1+v₀) ≤ 2`); the extra
  reach is only in `ψ`-range (to 47), already inside `hrange`.
- *Cost:* 6 hypotheses, a range constant that is a measurement not a theorem, and every Lean statement about "the k-th
  root of `x tan x = 1`" must carry `θ ≤ 47`.

### C. Glyph-edge / warp-map form

```lean
/-- Warped Circle map at ink-box fractions `(u, v)`, unit outer radius, `ρ = 1/2`: angle `π − 2πu`
(clockwise from 9 o'clock in the y-up plane), radius `(1 + v)/2`. -/
noncomputable def warpCircle (u v : ℝ) : ℝ × ℝ :=
  ((1 + v) / 2 * Real.cos (Real.pi - 2 * Real.pi * u), (1 + v) / 2 * Real.sin (Real.pi - 2 * Real.pi * u))

| warp_edge (u₁ a v₀ h : ℚ) (ha : 0 < a) (hh : 0 < h) (hu : 0 ≤ u₁ ∧ u₁ + a ≤ 1) (hv : 0 ≤ v₀ ∧ v₀ + h ≤ 1) :
    PConstructibleCurve ((fun s : ℝ => warpCircle (u₁ + a * s) (v₀ + h * s)) '' Set.Icc 0 1)
```
- *Faithful to the physics* (the idealization (b) is literally "PowerPoint's warp = this map"), and it gives windows
  exactly as W's law: `q₁ = a(1+v₀)/h`, `q₂ = q₁ + a`. It also brings the exact by-products (full circles, radial
  segments) which are already `ellipse` / `restrict`-of-`rectangle` and add nothing (I4 "warp by-products: E").
- *Costs:* (i) three presets (Circle, Arch Up/Button, Arch Down) mean three maps (or a `(Θ, κ)` parameter limited to
  the finite set `{(2π,1), (π,1), (π,1/3)}`); (ii) to use any W/B/C/O result in Lean one must first prove the normal form
  `warp_edge = similarity image of spiralParam '' Icc`, which needs rotation by the non-whole-degree angle `κ`
  (available through `rotate_PConstructibleCurve`) and a reparametrization of `s` to `ψ`; (iii) the Lean content is
  then the same as A plus a lemma. (iv) `hv`, `hu` are glyph-box constraints, i.e. UI geometry in a mathematical
  constructor.
- *Verdict:* expressively contained in A (W: `A` in `r = A + Bθ` adds nothing; the three presets give the same
  curve with different windows), so C is a **derived lemma** (`warp_edge_PConstructibleCurve` from A) for the
  documentation of the UI route, not a constructor.

### D. Other forms considered

- **General `r = A + Bθ` with P-constructible `A, B`:** redundant (uniform scale gives `B`; rotation gives `A/B`). Reject.
- **Parametric family `r = ψ` with unbounded `(q₁,q₂)` pairs as a set (union over windows):** no union operation exists
  in `PConstructibleCurve`; irrelevant.
- **Closed ray `Set.Ici 0`:** discussed as A0.
- **Tracing in polar angle, `r = θ` for θ ∈ [0, ∞) as a polar graph:** the same curve; the Cartesian parametrization is
  what `arc_of_length`/`offset` need.

## 2. Over-claim analysis (the main decision)

### 2.1 What is drawn, exactly
- Window law (all three presets) [Proof, W+F2, Wolfram-verified there]: `[ψ₁, ψ₂]`, `ψ₂ ≤ 2ψ₁` (Circle, Up) or `≤ 4ψ₁`
  (Down); length `≤ 2π` or `≤ π`.
- Contiguous coverage [Measured-model, F2]: pure ◢/▲ rows cover `[0.055, 4π]` (Circle); with spacing spinner down to
  `0.0106` (Circle), `0.0018` (Down); one extra tall glyph and two sizes cover `[0.76, 47.0]` (robust: 44.7 at 0.5 %,
  36.7 at 2 %); Up/Down mixed rows only to about 23.5 / 20.7. There is a ceiling near 50 for the swept recipes.
  [Open, F2 §1.4]: baseline offset, Stacked with wide polygons, and W's flat-slanted glyph edges (`q₂ ≈ 20`, `ψ ≈ 131`,
  in principle) are unmeasured.
- Multi-turn: one arc never turns more than once (`2πa ≤ 2π`); nothing glues two edges into one spiral (v resets).
- Origin: never reached.

### 2.2 Does a longer window (multi-turn, or ends beyond a drawn arc) give new numbers? No for the crossing read-outs
- **`inter_x/inter_y` [Proof].** Suppose a ray piece `P = restrict(S₁, W)` meets a curve `T` in the single point `p`,
  with `ψ_p` inside a drawn window and `A` the drawn arc through `p`. Then `restrict(A, W)` is a subset of `P` containing
  `p`, so `restrict(A, W) ∩ T = {p}` as well. Hence any coordinate obtained through the ray is obtained through a drawn
  arc, for every `p` with `ψ_p` in the drawn range.
- **`box_*` [Argued].** The maximum of `ψ cos(ψ − β)` over a window is either an end or an interior local maximum, and
  successive local maxima grow like `ψ`. So the box of a multi-turn window is the box of its last turn: no new value
  beyond the stationary points `θ tan(θ − β) = 1` and the window ends.
- **`arc_of_length` along the ray [Proof, B row 10].** `A(ψ₁) − A(ψ₀) = x` is the parabola arc-length inversion, already
  in the class. The endpoint `ψ₁` may exceed 47 if `x` is large; it is a P-constructible number regardless of
  PowerPoint's window, so nothing new in kind. It is, however, usable afterwards as a window end on the ray.
- **`offset`.** Whole-curve offset of a multi-turn arc is legal (`hinj` is about `γ`; cusps of the offset at `ψ_c` are
  not a hypothesis failure, B §0); B/O results are cusp-free sub-windows `Δφ < π`, so they never need multi-turn.

### 2.3 Does the ψ-range over-claim matter? Yes, in exactly one way: tail roots
- Similarity cannot rescale ψ (it is the dimensionless angle), and neither does `arc_of_length` (it moves ψ only along
  the drawn curve). So **a root `θ` of any family above the drawn range is not reachable from drawn windows**.
- Example [Wolfram]: roots of `x tan x = 1` are `0.86033…, 3.42561…, 6.43729…, 9.52933…, …`; the first 15 (`k = 0…14`)
  are below 47, the 16th is above. Under A, all `k` are P-constructible; under B2 only 15 (and fewer if the robust
  44.7 cap is used, 14 or so). The same holds for every spiral ∩ line / conic root family.
- The class-level statement "the roots of `θ + arctan θ = β + π/2 + kπ` are P-constructible for all `k`" is **provable
  only under A / B1**. Under B2 it becomes a finite list, `k ≤ 14`.
- Why this is **not obviously an over-claim worth avoiding:**
  - `sine` has the same shape: the glyph has 1 to 1.2 periods, yet the class has the whole graph `y = sin x`, hence roots
    of `sin x = x / m` at `x ≈ 300` for large `m`. `exp_two` is drawn on a finite chart or window, yet `y = 2^x` has no
    bound; `power_law` for all `x > 0`; polynomial graphs for all `x ∈ ℝ`. The project's convention is that an
    idealized curve stands for the whole analytic curve.
  - The ψ ceiling is not a theorem but a recipe-dependent measurement (F2: "dense above 50 is [Open]"; W: flat-edge glyphs
    give `ψ` to about 131-204 in principle). The true ceiling is plausibly higher; and the lower end `ψ → 0` is
    reached as `n → ∞` (more glyphs), only restricted by slide space and font-size limits, which are not mathematical.
- **Honest recommendation:** state the idealization in the Defs comment as "the whole ray" and list in the decision
  that the *measured* drawn range is `[0.002, 47]`, as an acknowledged extension, in the same sentence that already
  explains `sine`. If the user rejects that, use B2.

### 2.4 Summary table

| form | ψ-range over-claim | multi-turn | irrational ends | origin | compactness | Lean hypotheses |
|---|---|---|---|---|---|---|
| A1 `Ioi 0` ray | `(0, ∞)` vs `[0.002, 47]` | yes (harmless §2.2) | via restrict / arc | no | via restrict/arc | none |
| A0 `Ici 0` | same + origin | yes | same | yes (extra point) | `box` on `[0, b]` | none |
| B1 `Icc a b`, P ends | same as A | yes | all P | no | built in | 4 |
| B2 rational `q`, law, range | none (by hypothesis) | no | rational only (+ sub-windows) | no | built in | 6 + a measured constant |
| C `warp_edge` | none up to Arch variants | no | rational only | no | built in | 6 + 3 presets |

## 3. Evidence and idealization category

- **Measured accuracy** [Measured, F1, P1, P1b]: glyph corners lie on the ideal map within **0.06-0.74 pt** (typical
  0.1; best 0.000-0.055 pt at R = 151 pt) for Warped Circle, Arch: Warped / Warped Button, Arch: Warped Down. Between
  corners the baked or rendered outline is a Bézier fit: max **2.8-3.4 % of R** (Circle, Up/Button), **5.4 %** worst case
  (Arch Down ▲, band ratio 4:1), rms 1.0-2.8 %. The fit is a fixed percentage and does not shrink with size.
- **Category (b)**: a stored/rendered Bézier approximation of an ideal map. The spec (ECMA-376 §20.1.10.76) fixes only
  the guide paths, not the interior map; the interior map `Z(u,v) = C + (ρ + (R−ρ)v)e^{i(π+2πu)}` is **measured**, not
  specified. Corner anchors are exact.
- **Project convention:** an idealized curve that clearly approximates an ideal is treated as exact.
- **Comparison with the `sine` glyph** (memory: `sine` comes from a sine-wave character in a font, not the wave preset):
  P1b §4 measured U+223F "∿" in Cambria Math / Segoe UI Symbol / Lucida Sans Unicode against a best-fit sine: max
  13.7-18.6 % of amplitude (rms 4.8-7.3 %), with 1 to 1.2 periods. The spiral's 3 % of R is smaller and is against an
  *explicit* ideal rather than a best fit; counter-points: the normalisations differ (R vs amplitude), and the spiral's
  ideal map is itself measured. On this evidence the spiral is on at least as good a footing as the glyph precedent.
  [Heuristic: it is the user's call whether (b) stands.]
- **Residual factor:** the exactness of corners requires both guide circles to span 360° (or both 180° for the arch
  presets); the sizes where they do are chaotic in `n` (F1/P1b). The user must verify visually (the seam segment
  must look radial, not a chord). This is a UI discipline, not part of the constructor.

## 4. What each form unlocks

All forms A/B1/B2/C give the same set of numbers **inside the drawn range**. A and B1 additionally give tail roots (§2.3).
Rows: catalogue class → how → class label (plan §1) → note.

| class | route | label | notes |
|---|---|---|---|
| Box family `θ + arctan θ = β + π/2 + kπ`, i.e. `θ tan(θ−β) = 1`, T3 `tan y + y = k` | `box_*` of a window, `β` = direction | **N** (B row 1) | includes `x tan x = 1` (0.8603…), `tan x = −x` (2.0288…); closed under composition (C S2): tower `θ₁, θ₂, θ₃` |
| `x tan x = 1` for all `k` | A / B1 only | N | B2: `k ≤ 14` (`θ < 47`) |
| Sub-windows of any P-constructible ends | `arc_of_length` (B row 9) | N | removes F2's "window must end before the next extremum" |
| Spiral ∩ line/conic (I1) | `inter_x/y` after `restrict` | R mostly; generic conics **?** | master equation `Re(Aθ²e^{2iθ} + Bθe^{iθ}) + mθ² + f = 0` |
| Spiral ∩ polynomial / power law / Bézier (I2, F3) | same | R / **?** | parabola `sin θ = kθ cos²θ` **?** |
| Spiral ∩ `exp_two`, `sine` (I3) | same | **?** | `θ sin θ = 2^{θ cos θ}`, `θ sin θ = sin(θ cos θ)` |
| Spiral ∩ spiral (I4) | two copies via closure | E (same pole) / **?** | different poles, own offset |
| Offset spiral (O), arc length (B 14, 15) | `offset` of a whole window | E/R; intersections **?** | cusp `c³ = d(c²+1)` (E/R) |
| Offset inversion along the spiral | offset whole arc, `arc_of_length`, two boxes in non-parallel directions | **?** | `½(sinh u cosh u + u) − d(sinh u + gd u) = c` |
| Non-uniform images (B 5, 12, 13) | `scale_x ≠ scale_y` | **?** | box invisible, offsets/arc length visible |
| Parabola arc inversion | `arc_of_length` from any P start | R | already in class |
| **Fails to give:** T1, T2 (λ ≠ 1), T6; `tan x = x` (needs `β` depending on root, M §6); the log spiral; non-P-constructible rotation angles; `power_law` exponent slot and degree-5/6 shape invariants accept no spiral number (C) | | | [Proof, C] |

## 5. Lean-side impact

For form A (recommended) the following would need proving, none of which is hard:

1. **Parametrization lemmas.** `spiralParam` `C¹` (product of `id` with `cos`/`sin`); derivatives
   `(cos t − t sin t, sin t + t cos t)`; **`speed spiralParam t = √(1 + t²)`** — [Lean-scratch] compiled in a stand-alone
   file in 10 lines with `HasDerivAt.mul`, `Real.hasDerivAt_cos/sin`, `Real.sin_sq_add_cos_sq`, `nlinarith`; speed `≥ 1 > 0`
   gives `hreg` for `offset`.
2. **Injectivity.** `|spiralParam t| = |t|` (`Real.sqrt` of `t²(cos²+sin²)`), so `spiralParam` is injective on `Ioi 0`
   (r strictly increasing); this is the proof of `hinj` for `arc_of_length`/`arc_length` and (with `a < b`, no seam since
   `γ b ≠ γ a`) for `offset`.
3. **Arc length.** `arcLengthOf spiralParam a b = ½(b√(1+b²) + asinh b) − ½(a√(1+a²) + asinh a)`. Proof: FTC with
   `deriv` of `A(t) = ½(t√(1+t²) + asinh t)` equal to `√(1+t²)` [Wolfram: `D[…] = √(1+t²)` simplified]. Mathlib has
   `Real.deriv_arsinh`; or avoid `asinh` and use `Real.log (t + √(1+t²))`. Needed to show `arc_of_length` hits a stated
   length (compare `arcLengthOf_sineArc` in `BoxSine.lean`, which does the elliptic analogue).
4. **Compactness / box.** `spiralParam '' Icc a b` compact: `isCompact_Icc.image_of_continuousOn` (continuity). Nonempty
   from `a ≤ b`.
5. **Box value.** `max` of `ℓ·spiralParam` over a window: derivative `cos(t−β) − t sin(t−β)`; stationary point `t tan(t−β) = 1`;
   endpoint comparison. The infrastructure of `Pptc.Box`/`BoxGraph` (arc endpoint reading by `arc_xendpoint_Pconstructible`,
   monotone coordinate) does **not** transfer verbatim, because the spiral's coordinates are not monotone in a window;
   one needs the stationary-point analysis (new).
6. **Endpoint P-constructibility.** `spiralParam ψ` is P-constructible iff `ψ` is, via `cos_Pconstructible`,
   `sin_Pconstructible` (Basic.lean 2652/2657) and `ψ = |p|`. Needed for `hx₀ hy₀` of `arc_of_length` (B §0).
7. **Rotation by spiral numbers** (`rotate_PConstructibleCurve` is already derived), for the depth-2 box directions of B row 8.
8. **Offset of a window.** `unitNormal spiralParam t = (−(sin t + t cos t), cos t − t sin t)/√(1+t²)`; `offsetParam` closed
   form `e^{it}[t(1 − d/c) + i d/c]` (O) is only needed for the classification theorems, not for the soundness of the
   constructor.

**Patterns that transfer.** The `sine` pattern in `BoxSine.lean`/`Basic.lean` (`PConstructibleCurve.arc_of_length
PConstructibleCurve.sine (fun s => (s, Real.sin s)) hX0 hsub hinj hdiff hint …` with the five obligations spelled out by
`rintro`/`simpa`) carries over almost verbatim, replacing `(s, sin s)` by `spiralParam s`. What does **not** transfer:
`arc_xendpoint_Pconstructible` needs a coordinate monotone along the arc; the spiral gives monotone **radius**, not
monotone `x`. A radius-read-out lemma (via `inter_x` with a circle, or a `box` in a direction after a similarity) would be
needed to read the far end of a spiral `arc_of_length`; alternatively use the polar-ray trick of B row 10 (parabola
inversion), already R. No `Defs.lean` proof is affected by adding the constructor (all `induction` over
`PConstructibleCurve` would gain one case; any such proof elsewhere in the repo that matches on all constructors will
need a case — **not checked here, the repo was not edited**).

**Scratch typecheck of the candidate shapes** [Lean-scratch]: `spiralParam`, the three constructor shapes
(`archimedes`, `archimedes_window`, `archimedes_drawn`, written as a stand-alone `inductive Mock : Set (ℝ × ℝ) → Prop`)
typecheck. The only snag was `Real.pi` times `(q : ℚ)` needing an explicit `((q : ℚ) : ℝ)` cast.

## 6. Exact UI path (UI only; COM/VBA/XML edits do not count)

Based on P1b/F1. Measured on desktop PowerPoint 16.0 build 20527; steps 2 and 3 use only ribbon/pane UI.

1. **Shape Format tab visible.** The user's ribbon hides it by default (File ▸ Options ▸ Customize Ribbon ▸ Tool Tabs ▸
   Drawing Tools ▸ Shape Format); tick it, or reach Text Effects through the Format Shape pane route noted in P1b.
2. **Insert ▸ Text Box**; drag a box; type one glyph. Which glyph:
   - **◢ (U+25E2)**: font **Segoe UI Symbol**; chosen from the Home font box so that both `latin` and `ea` typefaces are
     Segoe UI Symbol. **Pitfall** (F1): ◢ ▲ use the run's `ea` typeface; typing "Consolas" in the font box changes only
     `latin`, leaving `ea = Segoe UI Symbol`. To get a true Consolas ▲, use Home ▸ Clear All Formatting first, or
     Insert ▸ Symbol with font Consolas and code 25B2 in a *new* text box. ◢ in a Consolas run falls back to another
     font (ink 48.90 vs 50.41 pt), so the font of ◢ must be fixed to read the window.
   - **Consolas ╱ (U+2571)** or **Arial /**: one slanted parallelogram stroke; windows `[2π·483/563, 4π·483/563]` (Consolas ╱)
     and `[4.6931, 9.3861]` (Arial `/`) (W §1).
3. **Do not Autofit.** Format Shape pane ▸ Text Options ▸ Textbox ▸ **Do not Autofit** (the autofit radios are greyed once
   a warp is active; set it before warping).
4. **Shape Format ▸ Text Effects ▸ Transform ▸ Warp ▸ Warped Circle** (UI name; `prstTxWarp = textCirclePour`). For the
   arch variants: **Arch: Warped** (`textArchUpPour`), **Arch: Warped Down** (`textArchDownPour`), **Warped Button**
   (`textButtonPour`). The gallery needs hover, mouse-down 0.35 s, mouse-up; sometimes Enter commits (P1b input note).
   **Do not touch the yellow handle**: defaults are the exact configuration, and dragging yields only pixel-quantised
   values (P1b §3).
5. **Make the box square** with the ribbon Size spinners (0.1 in steps, first click snaps to a multiple of 0.1 in). Choose
   a side `n/10` in where **both** guide circles span 360° (the shorter span makes the map non-polar and a radial segment
   a chord):
   - Warped Circle: n = **10, 20, 21, 23, 29, 33, 35, 37, 40, 42**.
   - Arch: Warped and Warped Button: n = **10, 11, 12, 14, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 35, 36, 38, 40, 42**.
   - Arch: Warped Down: n = **11, 12, 17, 18, 22, 23, 24, 25, 31, 34, 35, 36, 39, 41**.
   No UI readout exists; check visually (the seam must be a radial segment). Larger non-square arch boxes unmeasured.
6. **To set window parameters** (rows, spacing, sizes): number of glyphs `n` in the row gives `a ≈ 1/n`-type fractions;
   character spacing presets (−3, −1.5, 0, +3, +6 pt) or the 0.1 pt spinner (layout snaps to 0.75 pt); font size steps
   with A^ / A-v (list 1…96, then ×1.2). Mixed-height rows (◢ plus a tall `|`, two sizes) reach `ψ` up to about 47 (F2 §3).
   Flip Horizontal/Vertical in the Rotate menu gives the exact mirror (F1).
7. **From outline to a curve.** P1/P1b/F1 read the geometry by baking a *duplicate* with Merge Shapes (performed by COM
   for observation, with the slide in view). The same operation exists in the UI: select the text box and a second shape,
   Shape Format ▸ **Merge Shapes ▸ Combine** (or Fragment). The result is a freeform whose edges are the warped glyph
   edges. **[Open] I did not find in the notes how the user's existing `sine` glyph is turned into a curve (Insert ▸
   Symbol ∿ and then?). If it is the same Merge Shapes route, the spiral inherits it unchanged; please confirm.**
8. **Isolating an edge.** The model uses `restrict` (crop to a window) and `arc_of_length` (lay a sub-arc of prescribed
   length from a P-constructible point). In the UI: Edit Points on the freeform, or Fragment with a cutter rectangle,
   then delete the unwanted pieces. [Open] whether the user wants this stated as part of the route.

## 7. Recommendation

1. **Adopt form A1**, the fixed curve `spiralParam '' Set.Ioi 0`, plus the helper `spiralParam` next to `bezierParam`.
   Reasons:
   - it mirrors the `sine`/`exp_two` pattern: one fixed curve, similarity from closure ops;
   - it has no hypotheses, so no measured constant sits in `Defs.lean`;
   - W shows every drawn arc is a similarity image of a window of it; B shows `arc_of_length` + `restrict` isolate any
     window with P-constructible ends;
   - multi-turn extent adds nothing (§2.2); the only over-claim is the ψ-range, which the project already accepts for
     `sine`, and which lets the Lean statements "for all `k`" be provable;
   - Lean cost is small and proven in the key step (`speed`).
2. Document the measured range `[0.002, 47]` and the "window law" in the comment on the constructor, as the idealization
   statement, mirroring the comment on `sine`.
3. Keep **C (`warp_edge`) as a derived lemma**, not a constructor. It documents the UI route, and requires only the normal
   form lemma.
4. If the user rejects any range over-claim, take **B2**; it is exact and small but a Lean theorem "for all `k`" is
   then lost, and the measured range constants become part of `Defs.lean`.

Recommended snippet (to place after `cubic_bezier`, with `spiralParam` after `bezierParam`):

```lean
/-- The Archimedean spiral `r = t`, counterclockwise from the origin: `(t cos t, t sin t)`. -/
noncomputable def spiralParam (t : ℝ) : ℝ × ℝ := (t * Real.cos t, t * Real.sin t)

  -- The Archimedean spiral `r = θ` for `θ > 0`, a single fixed curve like `sine` and `exp_two`
  -- (pitch, rotation, centre and handedness come from the closure ops). Idealizes the edge of a
  -- slanted glyph under the Warped Circle text effect, `θ = π + 2πu`, `r = ρ + (R - ρ)v`.
  | archimedes : PConstructibleCurve (spiralParam '' Set.Ioi 0)
```

## 8. Open questions for the user

1. **ψ-range.** Accept the ray (A1) as an idealization like `sine`, or insist on the measured window `[0.002, 47]` (B2)?
   Do you want theorems "for all k" about the box family?
2. **Origin.** Exclude it (`Ioi 0`, recommended; matches the never-reached origin) or include it (`Ici 0`, matches
   `power_law` with `b > 0`)?
3. **Idealization acceptability.** Is the 2.8-5.4 % of R between-corner deviation (corners exact to 0.74 pt) acceptable as
   category (b), compared to the 12-19 % of the `sine` glyph? The interior map is measured, not in the spec.
4. **How is the `sine` glyph turned into a curve in your route** (Merge Shapes ▸ Combine, Convert to Shape, Edit Points)?
   The spiral route in §6 step 7 assumes the same.
5. **Box-size discipline.** OK to rely on a human visually checking both guide circles for a 360° span (no UI readout, no
   rule for which sizes work)?
6. **Presets.** Include the Arch presets in the idealization or only Warped Circle? (They add the `ψ₂ ≤ 4ψ₁` windows and lower
   `ψ`, but no new curve; under A it makes no difference. Under B2 it matters.)
7. **Rotation of the mirror.** Is `scale_x (−1)` acceptable as "Flip Horizontal"? (F1: exact mirror.)
8. **Untested:** the route has not been run end-to-end through to a final curve with Merge Shapes in the UI, and the Arch
   rows beyond single glyphs and the Stacked/baseline-offset recipes are unmeasured (F1/F2 open).

## Other things noticed

- The helper `spiralParam` shares its algebra with `bezierParam` in being an `ℝ → ℝ × ℝ` tracing; the same `γ` can be passed
  straight to `arc_of_length`/`offset`/`arc_length`.
- The F2 count "15 roots of `x tan x = 1` below 47" was re-derived here [Wolfram]: roots at `k = 0` plus `k = 1…14`; the 15th
  multiple of π is 47.12.
- `spiralParam '' Set.Ioi 0` makes `box_xmax` unavailable on the bare curve, correctly (unbounded, not closed); the
  `restrict` windows that avoid the pole recover it.
- Not checked: whether any repo proof by induction over `PConstructibleCurve` would need a new case. A grep for
  `induction`/`cases` on it should precede any real edit.
