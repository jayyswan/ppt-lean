# Text characters and text warps: theory, probes, and a formalization plan

Written 2026-11-06. Builds on `GLYPH-CATALOGUE.md`, `WP.md`, `../spiral/F1.md` and the
ECMA-376 preset definitions (`presetTextWarpDefinitions.xml`). Probe scripts and raw results
are in `probes/` (see `probes/README.md`). Labels: [Measured] = PowerPoint observation,
[Proof] = argued here (and, where noted, checked in Lean), [Heuristic], [Open].

## 0. Summary

1. **One law covers every bending preset [Measured].** All 36 Transform presets that bend
   glyphs are the *ruled arc-length warp*
   `F(u, v) = (1 − v)·T(u) + v·B(u)`.
   - `T` and `B` are the preset's two guide paths from the spec, each traced at constant
     speed over `u ∈ [0, 1]`.
   - `(u, v)` is the glyph point normalized by the ink box of the whole text (u left→right,
     v top→bottom).
   - Corners agree to ≤ 0.5 pt on a 288 pt box, most to 0.00–0.10 pt. The Bézier-parameter
     alternative misses by 4–20 pt wherever the two parametrizations differ.
   - The four **Follow Path** presets are not warps: each glyph moves **rigidly**
     (0.000 pt residual over 68 contours), so they add nothing.
2. **Straight edges on polygonal presets add nothing [Proof, Lean].** Under the 15 presets
   whose guides are straight (Plain, Stop, Triangle ×2, Chevron ×2, Fade ×4, Slant ×2,
   Cascade ×2), the map is a patchwork of bilinear cells. A straight glyph edge becomes a
   quadratic arc, which is a cubic Bézier already in the class.
3. **Round glyphs are where new shapes come from.** With your rule that a circular glyph is
   idealized as a circle:
   - a circle under a bilinear cell is a rational quartic **egg**;
   - with the Triangle handle at its stop the egg degenerates to the **piriform (pear
     curve)** `a²y² = x³(2a − x)`;
   - under the polar presets a circle is the transcendental **polar ellipse**, and a slanted
     edge is the **Archimedean spiral** (known from the spiral survey).
   - The probes confirm the ideal images: the warped `●` is within 0.33–0.40 pt of the
     exact image of a true circle (1.04 pt on Circle Pour, at the seam).
4. **Arc-length tracing makes Can, Ring, Wave, Curve and Inflate-Top genuinely
   transcendental [Proof].** Their slanted-edge and mixed-guide images involve the guide's
   own arc-length function (an incomplete elliptic integral for the ellipse guides), not
   just its shape.

## 1. Idealization: what is exact, what is idealized, what is not

| Datum | Status | Why |
|---|---|---|
| Preset guide formulas | **exact** | Spec formulas, evaluated by PowerPoint. |
| Default handle values (`50000`, `33333`, `45977`, `85714`, …) | **exact rationals** | Stored integers in 1/100000 units; PowerPoint computes with exactly that value. `45977` (≈ 40/87, Curve Up/Down) *looks* arbitrary, but it is a stored rational, not a measurement. Every rational is P-constructible, so it costs nothing. |
| Polygon glyph vertices | **exact rationals** | Integer font units; layout snaps to 0.75 pt (F1), so `u, v` are rationals. |
| Circular glyph (`●`, `○`, …) | **idealized: circle** | Clear intent; fonts store Bézier approximations, 0.03–1.5 % (`GLYPH-CATALOGUE.md` §4.5). Centre and radii come from the integer bounding box, so they are rational. |
| Arc-length fill fraction `k` | **idealized: 1** | Exactly 1.0000 on Stop, Triangle, Fade and Circle Pour. 0.976 on the waves and up to 2 % drift on Ring Inside, where PowerPoint underestimates the guide length. The intent is "the text spans the guide". |
| PowerPoint's rendering between nodes | **idealized: the exact map** | Long straight edges are under-subdivided (Inflate plot: the outer edge sags about 8 pt); short edges are within 0.4 pt. Same category as the spiral notes. |
| Box sizes with short arc spans (F1 §e) | **use only full-span sizes** | Arch Down Pour at 4 in fits at 1.85 pt instead of ~0.05 pt: that is F1's span artifact, not a different map. |
| A handle dragged to an arbitrary position | **rational, but no intent** | Dragging always stores a rational, so it is harmless for constructibility. Results should still be stated for *every* rational handle value, not a measured one. |
| A handle dragged **past its stop** | **exact bound, if confirmed** | `pin 0 adj 100000` clamps exactly. Whether a UI drag stores `100000` is [Open] (§5). |

**The practical rule this gives.** Because ℚ ⊆ P-constructible, the "is 0.457 really 0.457?"
worry only bites for a number known *solely* by measuring an approximation (a fitted radius,
a sampled curve). Anything PowerPoint stores or computes from stored integers is exact. State
theorems for arbitrary rational parameters and the question disappears.

## 2. The measured warp law (probes 1–3)

`probe_sweep.py ▦` (crosshatch square, Segoe UI Symbol 72 pt, 288 × 288 box, zero insets).
The "corner" column is the worst flat-corner image vs the nearest baked node; "interior edge"
uses contours smaller than half the ink box.

| Family | Presets | k | corner (pt) | interior edge (pt) | param-model corner (pt) |
|---|---|---|---|---|---|
| straight | Plain, Stop, Triangle(Inv), Chevron(Inv), Fade ×4, Slant ×2, Cascade ×2 | 1.0000 | 0.000–0.003 | 0.33–0.48 | Stop: 6.17, others equal |
| polar arcs | Circle Pour, Arch Up Pour, Button Pour | 1.0000 | 0.044–0.058 | 0.50–1.04 | 0.06–0.07 |
| polar arcs | Arch Down Pour (4 in: short-span size) | 0.98 | 1.85 | 1.39 | 9.29 |
| ellipse arcs | Can Up/Down | 1.0019 | 0.44 | 0.50 | 20.1 |
| ellipse arcs | Ring Outside / Ring Inside | 1.0002 / 0.992 | 0.10 / 5.96 | 0.89 / 5.94 | 12.6 / 18.2 |
| cubic Bézier | Wave1/2, Double Wave, Wave4 | 0.976–0.978 | 0.10–0.28 | 0.40–0.99 | 7.2–8.0 |
| cubic Bézier | Inflate, Deflate, Curve Up/Down | 0.999–1.000 | 0.02–0.05 | 0.37–0.40 | 4.6–16.0 |
| quad. Bézier + line | Inflate/Deflate Top/Bottom, Deflate-Inflate(-Deflate) | 0.999–1.000 | 0.02–0.32 | 0.35–0.62 | 0.85–17.8 |
| rigid | Arch Up, Arch Down, Circle, Button (Follow Path) | — | 0.000 rigid fit, scale 1.0000 | — | — |

`probe_slaw.py` fits the guide fraction `s` at which each corner lands: `s = k·u` with
residual ≤ 0.002 and fit distance ≤ 0.016 pt. So the map is **exactly ruled** (straight
interpolation in `v`) and **exactly arc-length** in `u`, up to the fill constant `k`.

Multi-path presets (Button Pour with 6 paths, Deflate-Inflate with 4, Deflate-Inflate-Deflate
with 6) use paths 1–2 for a single line. Paths 3–6 are presumably for lines 2 and 3 [Open,
untested].

## 3. The dictionary: preset family × glyph primitive

Families by guide geometry, given arc-length tracing:

- **B (bilinear cells):** both guides straight, so each cell is `P + uA + vB + uvC`. Cells
  break where a guide has a corner, at arc-length fractions; Stop's break is at
  `u = L₁/L`, algebraic.
- **A (affine cells):** B with parallel, equally long guides (Plain, Slant, Chevron halves);
  the twist `C = 0`.
- **P (polar):** concentric circular guides in a square box,
  `z = c + (ρ₀ + ρ₁v)·e^{i(θ₀ + Θu)}`.
- **E (translated ellipse arcs):** Can and Ring, `F = E(φ(u)) + v·Δ`, where `φ(u)` inverts the
  ellipse's arc length.
- **W (translated Bézier):** Wave ×4, `F = G(σ(u)) + v·Δ`, where `σ` inverts the Bézier arc length.
- **M (mirror Béziers):** Inflate and Deflate; the guides are mirror images, so their arc
  lengths correspond.
- **X (mismatched guides):** Curve Up/Down, Inflate/Deflate Top/Bottom, Deflate-Inflate(-Deflate),
  and P in a non-square box. The two guides have unrelated arc-length functions.

| Glyph primitive | A | B | P | E | W | M | X |
|---|---|---|---|---|---|---|---|
| horizontal edge | segment | segment / parabola arc | **circle arc** | ellipse arc | Bézier arc | Bézier (vertical affine image) | **new** blend |
| vertical edge | segment | segment | radial segment | vertical segment | vertical segment | segment | segment |
| slanted edge | segment | parabola arc (= cubic Bézier) | **Archimedean spiral** | **elliptic trochoid** | **arc-length-sheared Bézier** | new | new |
| circle glyph | ellipse | **egg quartic**; piriform when pinched | **polar ellipse** | new | new | new | new |

Bold marks a curve not given by any single existing constructor up to affine maps. That is
the sense of "new" throughout. No impossibility proofs exist for this class; nothing here
claims the curve cannot be reached by some longer composite.

### 3.1 The shapes worth having

1. **Egg quartics** (B, circle). Cell normalized to `x = u`, height `D(x) = d₀ + d₁x`. A round
   glyph with centre `(a, ½)` and radii `(a, ½)` maps exactly to
   `a²(D(x) − 2y)² = D(x)²·x(2a − x)`, for `x ≥ 0` (the side condition removes an acnode).
   - Rational quartic, one shape parameter `d₀/(d₁a)`.
   - Default Triangle (`α = ½`) gives `d₀ : d₁ = 1 : 2`; any rational handle value gives
     the rest of the family.
   - Fade and Cascade give eggs whose height falls along the text.
   - [Proof, Lean: `heightCell_image_glyphCircle`.] Measured: `●●` on Triangle at 0.33 pt,
     `●` on Fade Right at 0.37 pt.
2. **Piriform** (pear curve). The Triangle handle at its stop pinches each half-cell to a point
   at the outer edge. The left `●` of `●●` lies in `u ∈ [0, 0.456]`, tangent to the pinch.
   After the shear `y ↦ x − 2y` its image is exactly `a²y² = x³(2a − x)`.
   - [Proof, Lean: `piriform_eq_image`.] Measured at 0.40 pt max, 0.18 pt rms
     (`probes/pinned_textTriangle_100000.png`: two mirror-image pears).
   - A Lean derivation that it is in the class, *given* the rule, is
     `piriform_PConstructibleCurve_of_rule`.
3. **Archimedean spiral** (P, slanted edge). As in `../spiral/SUMMARY.md`; the window law
   carries over unchanged.
4. **Polar ellipse** (P, circle). `r(θ) = R(1 − v₀/2) ∓ (R/2)·√(s² − ((θ − θ₀)/Θ − u₀)²)`.
   - The earlier notes rejected it because the font circle is only approximate. **Your rule
     lifts that objection**: it is now an idealized curve with rational data.
   - Measured on Circle Pour at 1.04 pt max (seam), 0.34 rms.
5. **Elliptic trochoid** (E, slanted edge). `(a cos φ, b sin φ + c·E(φ | m) + const)`, where
   `E(φ | m)` is the incomplete elliptic integral of the second kind, i.e. the arc length of
   the guide. This is a trochoid whose phase is measured along the ellipse instead of by
   angle.
   - It arises because the guide is traced by arc length; an angle-linear guide would give an
     ordinary trochoid with ratio in ℚπ. [Proof, from the measured law; image not separately
     measured.]
   - Probably the most novel transcendental curve here: it puts `E(φ | m)` *inside* a curve,
     where previously it was only available as a number via `arc_length`.
6. **Arc-length-sheared Bézier** (W, slanted edge). `G(σ) + (α·s(σ)/L + β)·Δ`, a Bézier
   wave lifted in proportion to its own arc length. Hyperelliptic in general.
7. **Mismatch blends** (X, horizontal edge). On Inflate Top, `(1 − c)·Q(σ_Q(u)) + c·Line(u)`:
   a parabola point and a line point matched by equal arc-length fraction. This involves
   `arsinh` through the parabola's arc length. Even *straight horizontal* edges give new
   curves here, the only family where that happens.

### 3.2 Numbers

Not the focus, but for orientation:

- The eggs and the piriform are rational quartics with rational data. Against lines and
  conics they give solvable equations. Against each other, or against degree-6 graphs, they
  give degree-16+ systems. That is relevant to `../algebraic/` (which algebraic numbers are
  reachable), not settled here.
- The transcendental families have box and intersection equations of the same shape as
  the spiral catalogue, with `E(φ | m)` or a Bézier arc length in place of `θ`.

### 3.3 Threads: possible new numbers (open, each worth its own investigation)

Novel shapes are a goal in their own right (user, 2026-11-06). The threads below are where a
shape might also give numbers the class does not reach yet. None is established.

- **T1. Elliptic trochoid: mixed sine and elliptic-integral equations.** Today `E(φ | m)`
  enters only as a number: `arc_length` reads it at P-constructible endpoints, and
  `arc_of_length` inverts it. The trochoid puts `sin φ`, `cos φ` and `E(φ | m)` in one curve.
  - A line meeting it solves `b·sin φ + c·E(φ | m) = λ·a·cos φ + μ`. That is a
    Kepler-type equation with an elliptic integral in place of `φ`.
  - The question is whether such roots are already reachable, by composing `arc_of_length`
    with the sine curve, or are new. This is the analogue of `sin x = x/2`, which needed the
    `sine` constructor.
  - **Tested in §12:** extremes not new (proved), circle case collapses to `sine` (proved),
    elliptic root open. Original note: its box extremes are probably *not* new. The derivative condition is algebraic in
    `sin φ`, so the extreme value is `E` at an algebraic amplitude, which `arc_length`
    already gives. Check that.
- **T2. Mismatch blends: `arsinh` inside a curve.** Inflate/Deflate Top/Bottom match a
  parabola point and a line point by equal arc-length fraction. The parabola's arc length
  involves `arsinh`, so its intersections mix algebraic and `arsinh` terms.
  - Compare with `exp_two` (logarithms) and with what arc lengths of `poly_graph` already
    give.
- **T3. Polar warps: `θ` inside a curve with rational angular rate.** The Pour presets send
  `u` to an angle linearly, so a glyph's image is a curve in `(r, θ)` with `θ` appearing
  outside the trig functions.
  - The Archimedean-spiral case is in `../spiral/`.
  - The polar ellipse is the new case. Its intersections with rays and circles give
    equations like `r(θ) = const` mixing `θ` with square roots.
  - Check against what `rotate` with P-constructible angles already provides.
- **T4. Arc-length-sheared Bézier.** Hyperelliptic arc length inside a curve. Same question
  as T1, with a Bézier arc length in place of `E`.
- **Targets (§14).** Inverse elliptic integrals and a new operation: the first-kind inverse is the
  open one; algebraic text curves provably cannot supply it; the elliptic Kepler inverse and the
  Warp Up diagonal constant `δ_W = 0.46027847…` are constructed there.
- **T6. Arc length of a warped edge (§13).** The `arc_length` of the image of a slanted glyph
  edge between two P-constructible corners is a number in the class whose integrand has a
  nested radical. For ◢ under Warp Up in a 4 × 4 box it is 5.5122674859237737761…, a period of
  half a period of a second-kind differential on a genus-2 curve with no extra symmetry that
  is not the arc-length curve of any degree-4 polynomial graph (§13.1). Candidate new number,
  newness unproved.
- **T5. Algebraic engines.** The straight-guide families (egg quartics, piriform, Gerono lobe)
  are one-parameter families of rational quartics. Each could be a new rational-coefficient
  engine for the open degree 9–10 cases in `../algebraic/SUMMARY.md`. That is unlikely to help
  much on its own (F is small), but cheap to test against the bookkeeping law there.

## 4. Lean formalization plan

You are right that nothing *new* is constructible until `Defs.lean` has a warp constructor.
Two things can be done before that, and one is already done as a sketch.

### 4.1 Done (sketch): `Pptc/Warp/Bilinear.lean`

Uncommitted, not imported by `Pptc.lean`. Elaborates with no errors or warnings; axioms are
`propext`, `Classical.choice`, `Quot.sound`. Keep it, revise it, or delete it: your call.

- `ruledWarp`, `bilinearCell`, `ruledWarp_segment` (two constant-speed segment guides give a
  bilinear cell).
- `bilinearCell_segment_PConstructibleCurve` — **unconditional**: straight edges under any
  bilinear cell with P-constructible data are already constructible (degree-elevated cubic
  Bézier).
- `heightCell_image_glyphCircle` (circle → egg, set equality) and `piriform_eq_image`.
- `triangleWarp` (Triangle preset with arc-length guides), `triangleWarp_eq_left`,
  `triangleWarp_image_glyphCircle`.
- `TriangleCircleRule` (the proposed rule for one preset, as a `Prop`), and the
  **conditional** theorems `eggCurve_PConstructibleCurve_of_rule` and
  `piriform_PConstructibleCurve_of_rule` (the canonical pear `y² = x³(2 − x)`).

The conditional style lets a candidate constructor be tested for consequences, and for
collapse, before `Defs.lean` changes.

### 4.2 Constructor options for `Defs.lean` (your decision)

**Option A — one generic `text_warp`, guides as data.** It would take a preset's guides as
parametrized paths, the arc-length reparametrization defined from `arcLengthOf`, a box, a
rational handle, and a glyph primitive.
- Faithful.
- Heavy: the reparametrization is an inverse of an integral. Every downstream use must
  unfold it, and soundness depends on encoding the 36 presets exactly.

**Option B (recommended) — one constructor per family, in closed form.**

- `warp_bilinear`: the image of a rational glyph segment or rational axis-aligned glyph
  ellipse inside `[0,1]²` under a cell of one of the 15 straight-guide presets.
  - The preset's cell corners are given by the spec formula at a P-constructible box and a
    rational handle.
  - Do **not** allow arbitrary quadrilaterals. Modulo affine maps a quadrilateral has
    2 parameters; the presets give 1-parameter families (Fade, Cascade, Triangle halves).
    The general form over-claims.
  - The segment half is redundant (§4.1), so in effect this constructor adds the circle
    images: eggs and the piriform.
- `warp_polar`: Pour presets in a square box with full span (F1 §e). Segment or ellipse
  glyph. Adds spirals and polar ellipses. Supersedes the spiral survey's `archimedes`
  proposal, or should be stated alongside it.
- `warp_translate`: Can, Ring and Wave. `F = G(σ(u)) + vΔ` for a translated guide pair,
  with `σ` the arc-length inverse. This is the first place Option A's machinery is needed,
  but only for one guide.
- Families M and X: defer. M straight edges are conservative (affine images of Bézier
  arcs). X needs two different arc-length inverses.

Soundness checklist for any of these:

- glyph data rational and inside the unit square;
- box P-constructible with positive size;
- handle rational within the `pin` range;
- the image is of a *fixed* compact primitive, so no continuum of choices can collapse
  `PConstructible`.

### 4.3 Proof work, in order

1. `warp_polar` lemmas:
   - horizontal edge → circle arc and vertical edge → radial segment, both conservative
     (reuse `circleArc_PConstructibleCurve`);
   - slanted edge → `spiralParam` normal form, the W window law of the spiral survey;
   - circle → polar-ellipse parametrization.
2. `warp_bilinear` corollaries:
   - eggs for the default Triangle, Fade and Cascade with spec handle values;
   - piriform via the pinned Triangle, once §5 item 1 is settled.
3. The `warp_translate` normal form: Can with a slanted edge → elliptic trochoid with
   `E(φ | m)` from Mathlib's integral form (or the local `arcLengthOf`).
4. Number-level payoffs, as broad sweeps: boxes and intersections of each new curve against
   the base curves, in the style of `../spiral/SUMMARY.md` §2.

## 5. Open probes

1. **Handle past its stop.** `probes/probe_handle.py` drags the Triangle handle by real mouse
   input and reads back the stored `adj`.
   - It needs PowerPoint in the foreground. My one attempt ran with VS Code in front, so the
     drag landed there (harmless) and nothing was measured.
   - Run it yourself with PowerPoint in front, or tell me when I may take the screen.
2. **Multi-line text** on Button Pour, Deflate-Inflate and Deflate-Inflate-Deflate: which path
   pair does each line use?
3. **Wave fill shortfall** (k = 0.976): does it vary with box size or text length? Either way
   the ideal is k = 1, but a size-independent constant would mean PowerPoint uses a fixed
   flattening.
4. **Non-square Circle Pour**: confirm that arc length on the elliptic guide (not angle) is
   used. That would make it family X, not P.
5. **Ring Inside drift** (6 pt on the back half of the loop): length estimation, or a
   different seam convention?
6. **Stacking**: Transform followed by 3-D Rotation (see `../3d/`) or by shape flip/rotate.
   F1 found flips and rotations rigid; 3-D perspective is not.

## 6. Files

- `probes/warplab.py` — spec evaluator (all ECMA guide operators, arcs with visual →
  parametric angles), the parametrization models, the PowerPoint bake, and scoring.
- `probes/enum_probe.py` — maps COM `WarpFormat` to spec names (36 values; Follow Path is
  absent).
- `probes/probe_maplaw.py`, `probe_sweep.py`, `probe_slaw.py` — the warp law.
- `probes/probe_pinned.py` — idealized-circle images at a chosen handle value (handle set in
  XML, observation only).
- `probes/probe_followpath.py`, `probe_follow_render.py` — rigidity of Follow Path.
- `probes/probe_handle.py` — the UI handle drag (§5 item 1).
- `probes/plotcase.py` — debug plots. `plot_*.png`, `pinned_*.png`, `follow_*.png` and
  `sweep_25A6_288x288.json` are outputs.

## 7. Preset names: the UI's and the file format's

The notes above use the file format's preset names (`textCanUp`, `textCirclePour`, …).
PowerPoint's Transform gallery (Shape Format ▸ Text Effects ▸ Transform) shows different
names. This table was read from the gallery itself by `probes/probe_ui_warpnames.py`, which
applies each item and records the preset it stores. **Prefer the UI names** in anything
user-facing. In particular, "Pour" corresponds to the gallery's *Warped* items and "Can" to
*Warp Up / Warp Down*.

| Gallery name | Preset in the file | Family (§3) |
|---|---|---|
| Arch | `textArchUp` | Follow Path (rigid) |
| Arch: Down | `textArchDown` | Follow Path (rigid) |
| Circle | `textCircle` | Follow Path (rigid) |
| Button | `textButton` | Follow Path (rigid) |
| Square | `textPlain` | affine |
| Stop | `textStop` | straight |
| Triangle: Up | `textTriangle` | straight |
| Triangle: Down | `textTriangleInverted` | straight |
| Chevron: Up | `textChevron` | straight |
| Chevron: Down | `textChevronInverted` | straight |
| Ring: Inside | `textRingInside` | ellipse arcs |
| Ring: Outside | `textRingOutside` | ellipse arcs |
| Arch: Warped | `textArchUpPour` | polar |
| Arch: Warped Down | `textArchDownPour` | polar |
| Warped Circle | `textCirclePour` | polar |
| Warped Button | `textButtonPour` | polar |
| Curve: Up | `textCurveUp` | mismatched |
| Curve: Down | `textCurveDown` | mismatched |
| Warp Up | `textCanUp` | ellipse arcs |
| Warp Down | `textCanDown` | ellipse arcs |
| Wave: Down | `textWave1` | Bézier (wave) |
| Wave: Up | `textWave2` | Bézier (wave) |
| Double Wave: Down-Up | `textDoubleWave1` | Bézier (wave) |
| Double Wave: Up-Down | `textWave4` | Bézier (wave) |
| Inflate | `textInflate` | mirror Bézier |
| Deflate | `textDeflate` | mirror Bézier |
| Inflate: Bottom | `textInflateBottom` | mismatched |
| Deflate: Bottom | `textDeflateBottom` | mismatched |
| Inflate: Top | `textInflateTop` | mismatched |
| Deflate: Top | `textDeflateTop` | mismatched |
| Deflate: Top, Inflate: Bottom | `textDeflateInflate` | mismatched |
| Inflate: Middle, Deflate: Top and Bottom | `textDeflateInflateDeflate` | mismatched |
| Fade: Right | `textFadeRight` | straight |
| Fade: Left | `textFadeLeft` | straight |
| Fade: Up | `textFadeUp` | straight |
| Fade: Down | `textFadeDown` | straight |
| Slant: Up | `textSlantUp` | affine |
| Slant: Down | `textSlantDown` | affine |
| Cascade: Up | `textCascadeUp` | straight |
| Cascade: Down | `textCascadeDown` | straight |

COM's `WarpFormat` reads back 0 for the four Follow Path items, although the file stores
the presets above.

## 8. Wave: Down vs the "x³ − x shear" model (`probes/probe_wave_overlay.py`)

At the default handles the Wave: Down guide is exactly an affine copy of `x³ − x`. Its
control points are evenly spaced in x and offset (0, −d, +d, 0). The question is how text
follows it. The word "WAVE" (Arial 72 pt) was baked and compared with two models, each with
its own fitted fill factor `k`:

| Box (pt) | Shear (lift by the guide, x kept), rms / max | Arc length, rms / max | k (arc length) |
|---|---|---|---|
| 288 × 288 | 1.96 / 5.6 | **0.51 / 3.0** | 0.976 |
| 288 × 432 | 2.64 / 10.3 | **0.76 / 4.5** | 0.995 |
| 504 × 144 | 0.52 / 1.6 | **0.30 / 1.6** | 0.999 |

Arc-length tracing wins everywhere, and by a factor of 3–4 when the wave is steep relative to
the box. In a wide, shallow box the two nearly coincide. Figures: `probes/wave_overlay_WAVE_*.png`.

New, and open:
- **The fill factor depends on the box** (0.976 square, 0.995 tall, 0.999 wide). It is not a
  constant property of the preset.
- **The arc-length model's residual is still 3–4.5 pt max** in the steep boxes, larger than
  for the straight and polar presets.

So Wave's exact rule is not pinned down yet. The likeliest explanation is that PowerPoint
estimates the Bézier's length approximately, but that is untested.

### 8.1 Single solid glyphs: PowerPoint approximates long edges (`probe_wave_ctrl.py`)

The same comparison on single glyphs (Segoe UI Symbol 72 pt, Wave: Down):

| Glyph, box | Shear rms / max | Arc length rms / max |
|---|---|---|
| ● 288×288 | 1.76 / 5.4 | **0.17 / 0.57** |
| ● 504×144 | 0.27 / 0.87 | 0.23 / 0.86 |
| ■ 288×288 | 7.9 / 18.1 | 7.7 / 18.2 |
| ■ 504×144 | 1.8 / 6.6 | 1.7 / 6.7 |

**● follows the arc-length law.** **■ follows neither model**, because PowerPoint does not draw
the warped image of a long straight edge. The unwarped ■ is `M L L L Z`, four edges. The
warped one is `M C C C C C Z`:
- Each edge's end points land on the guide at the arc-length positions, for example
  (382.852, 358.094) at Bézier parameter 0.98213.
- The end tangents follow the guide's tangent.
- The handle lengths, however, are about 0.17–0.18 of the guide's derivative. Exact
  subdivision would give `t₁/3 = 0.327`, and the arc-length Hermite estimate is about 0.24.
- So the edge is a cubic of PowerPoint's own fitting, up to 18 pt off the guide.
- The top edge is split into two cubics at a point partway along. The reason is not known.
- Mapping the control points (lines treated as cubics with handles at thirds) does not fit
  either: 10 pt max.

Consequence for the idealization: "the exact warped image" matches PowerPoint well when the
glyph's own outline segments are short relative to the warp's bending. That holds for ●, for
lettering, and for every straight-guide preset, where a cubic represents the image exactly.
It does **not** hold for long straight edges under curved guides. Whether to idealize those
to the exact image is a modelling decision. PowerPoint's segment-fitting rule is open.

**Is the warp itself "squished"?** (A suggestion that PowerPoint's ■ is the x³ − x shear with
reduced amplitude.) For ■ alone, scaling the guide's offset by λ ≈ 0.58 brings the edges from
18 pt to 2.6 pt rms / 5 pt max. Allowing a horizontal stretch and shift as well, it stays above
2 pt rms. For ●, the best squish is **λ = 1.000** under arc-length tracing, at 0.13 pt rms. The
shear model stays at 1.7 pt rms whatever λ is. So the warp is not squished, and the flattening
is specific to how PowerPoint draws long straight edges.

**The calibrated "squashed cubic" model** (`probe_friend_model.py`). The model is
`y = chord + λ·(guide's x³ − c·x)`, with λ calibrated on ■ (0.607, at c = 0.95) and then
applied elsewhere:

| Shape | λ from ■ | Best λ, c for that shape | Arc length |
|---|---|---|---|
| ● | 8.5 rms / 15.7 max | λ = 0.99, c = 1.00: 2.4 / 5.8 | 0.13 / 0.38 |
| "WAVE" (Arial) | 5.6 / 15.5 | λ = 0.99, c = 1.01: 2.9 / 7.4 | 0.38 / 2.0 |

The squash calibrated on the square makes every other shape worse. Each shape's own best fit
is no squash and `x³ − x`. Arc-length spacing is 5–20× closer.

### 8.2 What PowerPoint actually does in Wave: Down (probes 28–30)

**Positions follow exact arc length, scaled to an underestimated total.** A row of 24 thin
bars gives `t(u)` at 48 points (`probe_wave_tmap.py`; x = W·t on this guide). The true arc
length `s(t(u))` is linear in `u` to within 0.11 pt; polyline lookup tables fit worse. The
slope is the total length PowerPoint assumes, which is below the true length. That is the
fill factor.

**The fill factor takes one of two values, and the usual one is near 1.** For square boxes
from 144 to 576 pt (`wave_t1_scan.json`), the end of the text lands at guide parameter
t₁ = 0.997065, a length fraction of 0.99589. The exceptions are 144, 156, 288, 312, 324 and
576 pt, where t₁ = 0.982126 (fraction 0.97565).
- The original sweep box, 288 × 288, is one of the exceptions. The "k ≈ 0.976" quoted
  earlier is therefore atypical.
- Within each class the result does not depend on scale: 144², 288² and 576² are
  identical, and so are 576 × 288 and 288 × 144. That points to a scale-free length
  estimate whose branch flips at particular sizes.
- No equal-step polyline or Gauss–Legendre rule reproduces either value exactly. The
  typical class lies between 10 and 11 chords, the exceptional between 4 and 5. An adaptive
  subdivision search is in progress.

**Each source segment becomes one cubic** (`probe_wave_edges.py`, `probe_wave_span.py`).
- Its end points are the exact warped points.
- Its end tangents are exactly along the warp's derivative (perpendicular error ≤ 0.002 pt).
- Its handle lengths are close to the exact Hermite value, `(1/3)·Δu·L_est`, for short
  segments: ratio 0.97–1.00 for Δu ≤ 0.3. They fall well short for long ones: 0.73 for a
  full-width edge in the square box, 0.59–0.96 depending on aspect.
- That shortfall is the "squish" seen on ■. Glyphs made of short segments (letters, ●)
  barely show it. The handle-length rule is still open.

**The screen rendering is also flattened**, but it differs from the Merge Shapes output by up
to 3 pt (slide exported at 10×). That suggests a dependence on output resolution, not yet
characterized.

**Measurement artifact:** Merge Shapes splits curves at approximate extrema. The top edge of
■ appeared as two cubics, which are one cubic split at τ = 7/32. Harmless, but don't read
structure into such splits.

### 8.3 Where L_est comes from (partly identified)

`L_est` is the total guide length PowerPoint assumes when it spaces text along a curved guide
(the text spans `u·L_est`). It was fitted against the exact `L_est` implied by the warped ■'s
corner, for 11 box shapes (`fit_lest.py`, `fit_lest2.py` and inline fits). The fitted
quantity is accurate to about 0.001 pt.

**Typical sizes.** Split the guide into **6 equal parameter pieces** and take per piece
`chord + w·(control polygon − chord)`, with w = 0.328, close to ⅓. That is nearly the classic
`(2·chord + polygon)/3` estimate, and it matches all 9 typical boxes to 0.026 pt. It is very
close but not bit-exact, so the precise rule is still open. These were ruled out:
- equal-step polylines: between 10 and 11 chords, 0.21 pt at best;
- adaptive subdivision in real space: 0.8 pt;
- adaptive subdivision in the normalized box: 0.27 pt;
- Gauss–Legendre, Simpson, trapezoid and midpoint rules: these converge to the true length
  from above, while `L_est` is below it.

**Exceptional sizes** (square boxes of 144, 156, 288, 312, 324 and 576 pt; 288 × 144;
576 × 288). The fraction is about 0.976, and the estimate is structurally different. No
piece count and weight of the same family fits both exceptional aspects (5.4 pt at best). The
trigger is an irregular set of sizes. **Explained in §9.2:** 0.976 ≈ 0.99589 · 48/49, the
typical estimate with one of 49 pieces dropped, the same slip that shortens straight and
elliptic guides at some sizes. The trigger is still unknown.

**Conclusion for the model.** `L_est` is a numerical approximation, not a design parameter.
The recommended idealization is `L_est = L`, the true arc length. The difference is a 0.4 %
compression along the text at typical sizes and 2.4 % at the exceptional ones. Where
PowerPoint fidelity matters, the 6-piece estimate reproduces typical sizes to about 0.03 pt.

### 8.4 Getting the idealized warp from straight edges: rows of blocks (`probe_block_rows.py`)

No installed font has a straight-edged square glyph with extra points along its edges; all
were scanned. A row of N touching full blocks (█, U+2588) in **Lucida Sans Unicode** works
instead. Each block is exactly 1 em wide, so at 72 pt the pen steps are exact and the blocks
touch. The row then has edges made of N short segments. Wave: Down, 360 × 360 pt, deviation
from the exact arc-length image with PowerPoint's own fill:

| N | 1 | 2 | 4 | 8 | 16 |
|---|---|---|---|---|---|
| rms / max (pt) | 10.0 / 21.8 | 5.2 / 10.5 | 0.65 / 1.7 | 0.25 / 1.7 | 0.17 / 1.7 |

Eight or more blocks approach ●-level fidelity. A 1.7 pt local maximum that does not depend
on N is not yet located. Other seamless full blocks: Consolas, Cascadia Code/Mono, Courier New,
Lucida Console, Segoe UI Variable, Yu Gothic and MS Gothic. Their advances need a size that
keeps the pen step on the 0.75 pt grid.

**Decision (2026-11-06): idealize `L_est = L`.** Curved guides are traced by true arc length.
In Lean this is `arcTrace` in `Pptc/TextBox.lean`, built on `arcLengthOf`. `speed`,
`arcLengthOf` and `bezierParam` moved unchanged from `Defs.lean` to the new `Pptc/Curves.lean`
so that `TextBox` can use them. Wave: Down (`WarpPreset.waveDown`) is the first curved-guide
preset. It models the first handle (default, 0 or 20000) with the second handle at its default
0. The measured fills (§8.2) and the 6-piece estimate (§8.3) remain the reference for anyone
comparing a construction with PowerPoint's literal output. For straight edges, rows of short
glyph edges (§8.4) make PowerPoint's output approach the idealized curve.

## 9. All straight, elliptic and polar presets in Lean (probes 32–33)

`Pptc/TextBox.lean` now models 23 of the 40 gallery presets: the 12 straight ones (Square,
Stop, Triangle ×2, Chevron ×2, Fade ×4, Slant ×2, Cascade ×2), the 4 elliptic ones (Warp
Up/Down, Ring: Inside/Outside), the 4 Warped ones (one row of text), and Wave: Down. Left: 7
Bézier presets, 6 mixed Inflate/Deflate presets, 4 Follow Path presets.

### 9.1 Handles

Each handle may sit at its default or at a stop reached by dragging past the end of its
range (`WarpPreset.stops`). Measured with real mouse drags (`probe_handle.py`):
- **Straight handles** store their bound exactly at both ends (Stop: 14286 and 50000; earlier
  Triangle).
- **Polar handles** (the Warped presets). Dragged straight outward, a polar handle keeps its
  default angle exactly (10800000, or 0 for Arch: Warped Down) and stores radius 100000,
  which the spec pins to 99000. Dragged inward there is no stop. A drop at the centre stored
  `adj1 = 0, adj2 = 1`, and just past it flips the angle to 0. Short of the centre the radius
  is wherever the pointer lands (9770 and 20115 at two drops). So the minimum is
  unreachable, except on **Warped Button**, whose spec pins every radius below 40000 up to
  40000 (a drop short of the centre stored 0).
- **Wave: Down's sideways handle** (`adj2`, ±10000) shortens both guides to `(1 − 2|b|)·w` and
  shifts them `2|b|·w` apart, top and bottom in opposite directions.

### 9.2 Validation (`probes/probe_presets_model.py`, `probe_presets_fill.py`)

`probe_presets_model.py` re-implements `WarpPreset.map` from the Lean text. It agrees with the
spec-parser guides of `warplab` at every stop to under 0.05 pt. The two exceptions are Warp
Up at max and Warp Down at min, where the ellipse height is 0. There `warplab`'s angle
conversion degenerates, the Lean guide is flat, and PowerPoint agrees with Lean (1.8 pt, the
floor). The probe then compares the model with PowerPoint's baked outline of "◗●◖" (Segoe UI
Symbol, glyphs idealized): 91 cases, every reachable stop in a 288 pt square box and every
default in 360 × 216.

- **Floor.** Ring: Outside is checked by the PowerPoint-to-model distance only, because its
  two ends meet and the seam edges vanish from the merged outline. In the 71 non-Wave cases
  outside the table below, PowerPoint's outline lies within 0.7 pt of the model and the model
  within 2.0 pt of PowerPoint's (rms ≤ 0.52). The 2 pt is the font's ◗/◖ not being exact half
  discs: it is the same at the identity-like Square default. Wave: Down's other 5 cases are
  within 1.9 / 2.4 pt, the typical `k ≈ 0.995` of §8.3.
- **Every miss has one cause: 48/49.** In the other 15 cases, fitting a fill fraction per
  guide (the text spans `k·L` from the start) gives `k = 0.9795 ± 0.0002`, against
  48/49 = 0.97959, on one guide or both. The other guide fits 1.000. With that fraction every
  case drops back to the floor (≤ 0.9 pt max, ≤ 0.24 rms):

  | case | guides short | unfitted max (pt) | fitted max (pt) |
  |---|---|---|---|
  | Chevron: Up / Down, 360 × 216 | both | 7.35 | 0.21 |
  | Warp Up min, 288²; Warp Down max, 288² | bottom | 3.9; 5.7 | 0.24; 0.25 |
  | Warp Up / Down default, 360 × 216 | top | 4.5; 3.9 | 0.55; 0.57 |
  | Ring: Inside default, 288² and 360 × 216 | top | 6.3; 6.9 | 0.40; 0.86 |
  | Ring: Outside min 288²; default 360 × 216 | bottom; both | 6.3; 13.2 | 0.36; 0.92 |
  | Arch: Warped Down default and max, 288² | bottom (outer) | 8.5; 3.8 | 0.19; 0.18 |
  | Warped Circle default 360 × 216; max 288² | both; bottom | 16.7; 7.5 | 0.37; 0.37 |
  | Wave: Down default, 288² | both, k = 0.9758 | 6.5 | 0.28 |

  This is F1 §e's span artifact (176.30° = 180° · 48/49), now seen on straight guides, on
  ellipses and on the waves. Wave: Down's exceptional 0.976 is that slip times the typical
  Bézier underestimate (0.99589 · 48/49 = 0.9756). Its other stops fit `k ≈ 0.995`, the
  typical class. Which box sizes trigger the slip is still unknown, and it is per guide.
- **Idealization.** The model spans the whole guide (`k = 1`), consistent with §8.3. A
  construction must name its box size and be checked by `probe_presets_model.py`.

New number threads: none. New curve families enter through the elliptic (trochoid, T1) and
polar (spiral, T3) presets, which are now in the Lean model with all their handle stops.

### 9.3 The 7 other cubic Bézier presets (probe 32 second run, `presets_model2.json`)

Added: Wave: Up, Double Wave: Down-Up, Double Wave: Up-Down, Inflate, Deflate, Curve: Up,
Curve: Down. All 30 modelled presets are now validated (125 cases). The four waves share
`waveMap`: one cubic per guide (or two for the Double Waves) with control heights
`y, y − d, y + d, y`, `d = ±10y₁/3`, and the same sideways handle. Deflate's handle scales
with `min w h`, not `h`; the spec-parser cross-check passes in a tall 216 × 360 box too.

- **At the floor** (≤ 0.54 pt PowerPoint-to-model, ≤ 1.84 pt model-to-PowerPoint): every
  Inflate and Deflate case, Curve: Up/Down at 288², and every handle-minimum (flat) case.
- **The waves' usual fill.** Away from the slip, a wave spans 0.994–0.996 of each guide with
  one cubic, and 0.998 with two, from PowerPoint's length estimate (§8.3). That puts them at
  up to 1.9 pt; the model uses the true length.
- **The 48/49 slip, set aside** (user decision, 2026-11-06: some size always works and a
  result can be scaled). Wave: Up at 288² fits 0.9757 on both guides (= 0.99589 · 48/49, as
  for Wave: Down). The Double Waves at 288² fit 0.9784 ≈ 0.9984 · 48/49 on both guides at the
  default, and on one guide at each sideways stop. Curve: Up/Down at 360 × 216 fit 0.979 on
  the top guide. With those fractions every case drops to ≤ 0.66 pt.

### 9.4 The 6 quadratic presets (`presets_model3.json`)

Added: Inflate: Bottom, Deflate: Bottom, Inflate: Top, Deflate: Top, "Deflate: Top, Inflate:
Bottom" and "Inflate: Middle, Deflate: Top and Bottom". Each guide pair is one straight edge
and one quadratic Bézier, written in Lean as the degree-elevated cubic (`quadBezierParam`).
The last two presets have 4 and 6 guides. A single row of text uses the first two: the sweep
(`sweep_25A6_288x288.json`) fits pair (0, 1) to 0.02–0.07 pt and every other pair is tens of
points off. Their middle bands are for further rows, which the one-row model does not have.
Deflate: Bottom, like Deflate, scales its handle by `min w h`. Inflate: Bottom's default
(60000) is also its minimum.

All 24 cases (every stop in 288², every default in 360 × 216) are at the floor:
≤ 0.59 pt PowerPoint-to-model, ≤ 1.84 pt model-to-PowerPoint, rms ≤ 0.50. No 48/49 slip
appeared.

All 36 warping presets are now in the Lean model (149 cases validated). Remaining: the 4
Follow Path presets (rigid placement, a separate constructor).

## 10. Reference: the exact map of every warping preset

Everything below is what `WarpPreset.map` in `Pptc/TextBox.lean` computes (the 36 presets
that warp; the 4 Follow Path presets are not modelled). Each closed form was checked
numerically against the validated guides of `probe_presets_model.py` (error ≤ 1e-9).

### 10.1 The common map

1. Normalize: the ink box of the whole row goes to the unit square, `u` across (0 → 1) and `v`
   from the top (0 → 1).
2. Map: `F(u, v) = (1 − v)·T(u) + v·B(u)`, into the box `[0, w] × [0, h]`, `y` pointing down.
3. `T(u)`, `B(u)` are the preset's top and bottom guides at the fraction `u` of their arc
   length (`arcTrace`; the true length, §8.3).

`a` is the first handle (stored value / 100000), `b` the waves' sideways handle in
`{−0.1, 0, 0.1}`. Handles are listed min / default / max; "—" is not reachable by a drag.

**Slide presets.** If `B = T + τ` for a constant vector `τ`, then `F(u, v) = T(u) + v·τ`: the
text slides along one curve and is sheared by `τ`. Straight vertical edges stay vertical.

### 10.2 Straight guides (12)

| Preset | T | B | a |
|---|---|---|---|
| Square | (0,0)→(w,0), shrunk to `[max(0, w−2aw), min(w, 2(1−a)w)]` | (0,h)→(w,h), shrunk to `[max(0, (2a−1)w), min(w, 2aw)]` | .3 / .5 / .7 |
| Stop | (0,ah)→(w/3,0)→(2w/3,0)→(w,ah) | (0,h−ah)→(w/3,h)→(2w/3,h)→(w,h−ah) | .14286 / .25 / .5 |
| Triangle: Up | (uw, ah·\|2u−1\|) | (uw, h) | 0 / .5 / 1 |
| Triangle: Down | (uw, 0) | (uw, h − (1−a)h·\|2u−1\|) | 0 / .5 / 1 |
| Chevron: Up | (uw, ah·\|2u−1\|) | T + (0, (1−a)h) | 0 / .25 / .5 |
| Chevron: Down | (uw, (1−a)h·(1−\|2u−1\|)) | T + (0, ah) | .5 / .75 / 1 |
| Fade: Right | (0,0)→(w,ah) | (0,h)→(w,h−ah) | 0 / .33333 / .49999 |
| Fade: Left | (0,ah)→(w,0) | (0,h−ah)→(w,h) | same |
| Fade: Up | (aw,0)→(w−aw,0) | (0,h)→(w,h) | same |
| Fade: Down | (0,0)→(w,0) | (aw,h)→(w−aw,h) | same |
| Slant: Up | (0,ah)→(w,0) | T + (0, (1−a)h) | 0 / .55555 / .71431 |
| Slant: Down | (0,0)→(w,(1−a)h) | T + (0, ah) | .28569 / .44445 / 1 |
| Cascade: Up | (0,(1−a)h/4)→(w,0) | (0,h)→(w,ah) | .2857 / .44444 / 1 |
| Cascade: Down | (0,0)→(w,(1−a)h/4) | (0,ah)→(w,h) | same |

Single-segment pairs give a bilinear map; Square at its default is the plain stretch
`(uw, vh)`. Slant: Up is the affine map `(uw, ah(1−u) + (1−a)h·v)`, Slant: Down
`(uw, (1−a)h·u + ah·v)`. Only Square, Fade: Up/Down move points sideways. Stop's three pieces
have unequal lengths, so it needs `arcTrace`; the Triangles' and Chevrons' two pieces are equal.

### 10.3 Ellipse arcs (4): slide presets

| Preset | T | τ | a |
|---|---|---|---|
| Warp Up | `d = (1−a)h`: upper half of the ellipse with centre `(w/2, d)`, semi-axes `(w/2, d)`, from the left end | (0, h − d) | .66667 / .85714 / 1 |
| Warp Down | `d = ah`: lower half, centre `(w/2, 0)`, semi-axes `(w/2, d)` | (0, h − d) | 0 / .14286 / .33333 |
| Ring: Inside | `r = ah/2`: whole ellipse, centre `(w/2, r)`, semi-axes `(w/2, r)`, from the left end, sweeping +(360° − 1/60000°) | (0, h − 2r) | .5 / .6 / .99 |
| Ring: Outside | same, sweeping −(360° − 1/60000°) | (0, h − 2r) | same |

Ring's sweep is by the spec's visual angle `θ`: the point is `c + ρ(θ)(cos θ, sin θ)` with
`ρ = (w/2)·r / √((r cos θ)² + ((w/2) sin θ)²)`. At Warp Up max and Warp Down min the ellipse
height is 0, the guides are flat, and the map is the plain stretch. Vertical edges stay vertical
and slanted ones become elliptic trochoids (thread T1).

### 10.4 Warped (4): radial between similar ellipses

With `c = (w/2, h/2)` and `E(φ) = ((w/2) cos φ, (h/2) sin φ)`, the inner guide is the outer one
scaled by `a` about `c`. A homothety preserves arc-length fractions, so both guides use the same
angle `φ(u)` (the arc-length parametrization of the outer arc) and the map is radial:

| Preset | F(u, v) | arc | a |
|---|---|---|---|
| Arch: Warped | `c + (1 − (1−a)v)·E(φ(u))` | upper half, φ from π to 2π | — / .5 / .99 |
| Arch: Warped Down | `c + (a + (1−a)v)·E(φ(u))` | lower half, φ from π to 0 | — / .25 / .99 |
| Warped Circle | `c + (1 − (1−a)v)·E(θ(u))` | whole ellipse from the left, 360° − 2/60000° | — / .5 / .99 |
| Warped Button (one row) | as Arch: Warped | upper half | .4 / .5 / .99 |

In a square box `φ(u)` is linear in `u`: a true polar map (Archimedean spirals, thread T3). The
polar handle keeps its default angle; only the radius moves.

### 10.5 Cubic Béziers (8)

All control points are equally spaced in `x`, so each guide is a polynomial graph in `X = x/w`.

**The four waves** are slide presets with `τ = (2bw, h − 2ah)`. The top guide starts at
`x = max(0, −2bw)` and spans `s = (1 − 2|b|)w`. With `y₀ = ah` and `Z = 2X − 1 ∈ [−1, 1]`
across one cubic, the top guide is `y = y₀ − ε·(5/2)y₀·(Z³ − Z)` and the bottom guide is
`y = (h − y₀) − ε·(5/2)y₀·(Z³ − Z)`: the *same* wiggle, set by the top's height, not the
bottom's. This is the x³ − x curve of §8, placed by arc length rather than by `x`.

| Preset | ε | cubics per guide | a |
|---|---|---|---|
| Wave: Down | +1 | 1 | 0 / .125 / .2 |
| Wave: Up | −1 | 1 | same |
| Double Wave: Down-Up | +1 | 2, each spanning s/2 | 0 / .0625 / .125 |
| Double Wave: Up-Down | −1 | 2 | same |

**The other four**, with `X = x/w`:

| Preset | T: y(X) | B: y(X) | a |
|---|---|---|---|
| Inflate | parabola `d(1−2X)²`, `d = ah` | `h − d(1−2X)²` | 0 / .1875 / .2 |
| Deflate | parabola `4δX(1−X)`, `δ = a·min(w,h)` | `h − 4δX(1−X)` | 0 / .1875 / .375 |
| Curve: Up | true cubic `ah(1 + ¾X − (9/4)X² + ½X³)` | parabola `h − 3ah/8 + (3/2)ah·X(1−X)` | 0 / .45977 / .56338 |
| Curve: Down | the same cubic at `1 − X` | same as Curve: Up | same |

The spec writes Inflate and Deflate as cubics, but their control points make the cubic
terms cancel: they are parabolas.

### 10.6 Quadratic Béziers (6): one straight guide each

The control point sits at `x = w/2`, so a curved guide is `y = p + q·X(1−X)`:

| Preset | T | B | extreme point | a |
|---|---|---|---|---|
| Inflate: Bottom | `y = 0` | `ah + 2(1−a)h·X(1−X)` | `(1+a)h/2` | .6 / .6 / 1 |
| Deflate: Bottom | `y = 0` | `h − 4(h−δ)·X(1−X)`, `δ = a·min(w,h)` | `δ` | .0625 / .5 / 1 |
| Inflate: Top | `ah(1 − 2X(1−X))` | `y = h` | `ah/2` | 0 / .4 / .5 |
| Deflate: Top | `4ah·X(1−X)` | `y = h` | `ah` | 0 / .5 / .9375 |
| Deflate: Top, Inflate: Bottom (one row) | `y = 0` | `0.45h + 2(2a−1)h·X(1−X)` | `(a − 0.05)h` | .05 / .35 / .95 |
| Inflate: Middle, Deflate: Top and Bottom (one row) | `y = 0` | `0.3h + 2(2a − 0.66)h·X(1−X)` | `(a − 0.03)h` | .03 / .25 / .47 |

### 10.7 Where arc length is not elementary

`arcTrace` is the only non-algebraic step. Exact closed forms (no integral): the straight
presets except Stop, Square, Slant. Elliptic integrals: Warp, Ring and the Warped presets, and
the cubic guides of the waves and Curve. Arsinh: every parabolic guide (Inflate, Deflate,
Curve's bottom, the quadratic presets), which is thread T2.

## 11. Which glyphs go in the Lean model, and the Full Block (probes 34–35)

**Policy (user, 2026-11-07).** A glyph enters `Glyph` only if it is *clearly* a geometric
figure, and then it is that figure. Whether a font stores a clean outline for it is not the
test: the letter A is not clearly any figure, even though its outline can be read from the
font file. The circles and half circles qualify because they are clearly meant to be circles
and half circles. Their shape is idealized (a true ellipse), and the dimensions are what the
font stores (integer bounding box), which is also what PowerPoint draws.

**Glyphs so far:** ● ◗ ◖ (§1), █ (below) and ◢ (§12.1).

**█ U+2588 FULL BLOCK** qualifies (clearly a filled rectangle). Segoe UI Symbol stores it as
one four-point contour, `(-10, -440)–(1931, 1501)` in 2048 units per em: a square of side 1941,
advance 1921. The corners are stored integers, so there is nothing to idealize. The block is
20 units wider than its advance, so neighbouring blocks overlap by 20 units and Merge Shapes
unions them into one contour (two 72 pt blocks: one contour, 135.7383 pt wide, as predicted).

Validation against PowerPoint:
- **Layout** (`probe_row_block.py`, predictions from `RowCheckBlock.lean`): a row of blocks
  and circles with sizes 10.7–100 pt, spacing, a superscript, a subscript and a 2 % offset,
  plain and with Equalize Character Height. Every ink box agrees to 0.0001 pt.
- **Warps** (`probe_block_warp.py`): a lone block's four corners are (u, v) ∈ {0,1}², so the
  ruled map predicts them exactly. 36 preset/box cases: 29 are within 0.4 pt (most 0.0), one
  is at 0.78 pt (Wave: Down in 360 × 216, the waves' usual length shortfall), and 6 miss by
  7–9 pt. Those 6 are exactly the preset and box combinations where the 48/49 slip already
  appeared (Warp Up and Warp Down at 360 × 216, Arch: Warped Down, Wave: Down and Double
  Wave: Up-Down at 288², Curve: Up at 360 × 216), with errors of the same size. Only corners
  are tested: PowerPoint under-subdivides a block's long edges (§8.1).

## 12. Thread T1 tested: the elliptic trochoid (`probes/t1_trochoid.wl`)

**Setting.** Warp Up, 4 × 4 box, handle 3/4. The top guide is the upper half of the ellipse
with centre (2, 1) and semi-axes (2, 1), and `B = T + (0, 3)`. A glyph edge that is a slanted
segment `v = m·u` goes to `F(u, v) = T(u) + v·(0, 3)`. With `ψ` the ellipse angle measured
from the left end, `u = E(ψ | m_e) / L` (arc length over half-ellipse length), so for the
diagonal `v = u`:

    x(ψ) = 2 − 2 cos ψ,   y(ψ) = 1 − sin ψ + κ·E(ψ | −3),   κ = 3 / L,   L = 2 E(−3).

This is the elliptic trochoid: the circle case (`E(ψ) = ψ`) is the ordinary trochoid, and the
elliptic integral replaces the angle.

**The glyph for it is now in Lean (§12.1).** The circle, half circles and Full Block have no
slanted straight edge, so ◢ U+25E2, clearly a right triangle, was added (2026-11-07). A ●
under Warp Up gives a different new curve (its circle is pulled back through
`u(ψ) ∝ E(ψ)`, so `E` sits inside a square root).

**Result 1: the extremes are not new (proved, informal).** `dy/dψ = −cos ψ + κ·√(1 + 3 sin²ψ)`.
Setting it to 0 and squaring gives a quadratic in `cos²ψ`; in general (semi-axes `A, B`,
`κ` the shear per unit arc length)

    cos²ψ_e = κ²A² / (B² + κ²(A² − B²)).

Checked at 130 digits for the example (`cos²ψ_e = 0.71334439364968309904…`, difference from
the formula 0). Now `κ` is P-constructible (`L` is `arc_length` of the half-ellipse between
rational endpoints, `κ = 3/L`), so `cos ψ_e` and `sin ψ_e` are square roots of P-constructible
numbers, the ellipse point at `ψ_e` has P-constructible coordinates, and `E(ψ_e | −3)` is
`arc_length` of the ellipse between two P-constructible points. So `y_ext = 1 − sin ψ_e +
κ·E(ψ_e | −3)` is built from `arc_length`, `sqrt` (`sqrt_Pconstructible`) and `+ − × ÷`: it is
already in the class. Box extremes of a slanted edge's image add nothing.

**Result 2: circles collapse to `sine` (proved, informal).** If the guide is a circle (Warped
Circle in a square box, Ring with `w = ah`, Warp Up/Down with `d = w/2`), then `E(ψ) = Rψ` and
a line meets the image where `Rκψ = c + α sin ψ + β cos ψ`, i.e. `sin(ψ − δ) = linear in ψ`.
That is the `sin x = x/2` situation the `sine` constructor already handles. No new number.

**Result 3: the elliptic case is a Kepler-type equation, and its root looks transcendental.**
For the line `y = x/2 + 3/2` the equation is

    κ·E(ψ | −3) = 3/2 + sin ψ − cos ψ,

with a single root (the line meets the image once; `f` changes sign once after the dip at
`ψ_e ≈ 0.565`):

    ψ* = 2.80020022486580634883864402109954759366708902731214875…
    x* = 3.88457878947755277491871731784674947112518337534600…
    y* = 3.44228939473877638745935865892337473556259168767300…

Integer-relation search at 125 digits (coefficients up to 10⁵): `cos ψ*`, `x*` and `ψ*` satisfy
no polynomial relation of degree ≤ 12, and neither does `κ`. The same search finds the degree-6
relation of `cos(2π/13)` and finds none for `√2 + π`. This is the expected picture and not
evidence of newness: `κ` already contains the complete integral `E(−3)`.

**Open question (the thread).** Is `x*` in the class generated by the existing constructors?
- A route would unroll the ellipse: a curve whose x-coordinate is the arc length along it, so
  the unknown `s` becomes a coordinate. `arc_of_length` places an arc of *given* length, and
  `box_xmax` recovers its far endpoint, but the unknown here is the length itself, so the
  existing constructors do not obviously build the graph of `s ↦ ellipse point`.
- Showing the root is *not* in the class needs an independence statement about incomplete
  elliptic integrals at algebraic amplitudes. Nothing like that is known to me; it is
  Schanuel-type, so a proof of newness is not realistic, and a constructive reduction is the
  only decidable outcome.
- Either way the `text` constructor now includes these curves in the class, so these roots are
  reachable (◢ is in Lean). Newness is a separate question.

Result 1 could be formalized in Lean now (it needs only `arc_length`, `sqrt` and the
algebra above), and so could 2–3, now that ◢ exists.

### 12.1 The Lower Right Triangle ◢ (probes 36–38)

◢ U+25E2 in Segoe UI Symbol is stored as three points, `(1599, 1434)`, `(1599, 0)`, `(165, 0)`
(advance 1764, as for the circles), so nothing is idealized. It passes the §11 policy.
Validation against PowerPoint:
- **Layout** (`probe_row_triangle.py`, `RowCheckTriangle.lean`): triangles and circles, sizes
  10.7–100 pt, spacing, superscript, subscript, a 2 % offset, plain and Equalize: every ink
  box agrees to 0.0000 pt.
- **A lone triangle** (`probe_triangle_warp.py`, 38 preset/box cases): corners are exact except
  at the box sizes of the 48/49 slip. The slanted edge, though, is 2–13 pt off under the curved
  presets, slip cases aside (about 1.7 pt even under Square, where the true image is a straight
  line). The
  hypotenuse stretches to the whole box, about 290 pt, and PowerPoint refits it with one Bézier:
  the one-cubic-per-segment effect of §8.2, which the model idealizes away (§8.3).
- **A row of triangles** (`probe_triangle_row.py`, 8 triangles at 36 pt, 11 preset/box cases):
  with every slanted edge short, the Lean layout plus the preset formulas match PowerPoint at
  the same floor as the plain Square case. Slanted edges: ≤ 1.9 pt max, 0.3–1.1 rms (Warp Up
  1.77, Warp Down 1.78, Ring: Outside 0.99, Arch: Warped 0.52, Wave: Down 1.30, Inflate 1.82,
  Deflate 1.81, Curve: Up 1.63, Inflate: Top 1.47; Square itself 1.82). PowerPoint-to-model:
  ≤ 0.9 pt. So the elliptic trochoid pieces of Warp Up/Down are what PowerPoint draws.

## 13. Thread T6: the arc length of a warped edge (`probes/t6_warped_edge_length.wl`)

T1 (§12) asks whether a *root* of a Kepler-type equation is already reachable. T6 is a more
direct source of a candidate new number, and it needs no equation solving. It uses the
`arc_length` constructor on a curve that only `text` provides.

**The number.** Warp Up, 4 × 4 box, handle 3/4 (ellipse centre (2, 1), semi-axes (2, 1), shear
`(0, 3)`). The image of ◢'s hypotenuse `v = 1 − u` (or ◣'s, `v = u`) runs from the corner
`(0, 4)` to the corner `(4, 1)`, both rational. By `ψ → π − ψ` both hypotenuses have the same
length:

    N₁ = ∫₀^π √( 4 sin²ψ + (cos ψ + κ·√(1 + 3 sin²ψ))² ) dψ     (◢; ◣ has − in place of +)
       = 5.51226748592377377613798025362061525306584914294369037519499…

with `κ = 3/L`, `L = 2E(−3)`. The straight chord between the corners is 5. `arc_length`
accepts this arc: it is an injective, differentiable, integrable tracing of a piece of the
outline of `text` with P-constructible plane endpoints. So `N₁` is in the class. Inverting it
by `arc_of_length` on the same edge gives, for a P-constructible length, a point on the warped
edge: an inverse of this integral, the analogue for T6 of the inverse elliptic integral that
the ellipse already gives.

**Why it is not an elliptic integral.** Write `sp(ψ) = √(1 + 3 sin²ψ)`, the ellipse's own speed
(the integrand of `L`). The warped edge's speed satisfies (checked to 10⁻¹⁰)

    speed² = sp·((1 + κ²)·sp − 2κ cos ψ),

a square root inside a square root. In `c = cos ψ`: `P + Q√R` with `P = (1+κ²)(4 − 3c²)`,
`Q = −2κc`, `R = 4 − 3c²`. It would denest only if `P² − Q²R` were a square, and

    P² − Q²R = (3c² − 4)·(3c² − 4 − 8κ² + 10c²κ² − 4κ⁴ + 3c²κ⁴).

The second factor is `(3κ² + 1)(κ² + 3)·c² − 4(1 + κ²)²`, linear in `c²` with a non-square
coefficient product, and `3c² − 4` is a different factor, so `P² − Q²R` is not a square and the
radical is genuinely nested.

**The curve is of genus 2 (checked numerically).** Put `c = cos ψ = (2/√3)·cos α`, so
`v = √(4 − 3c²) = 2 sin α`, with `α` running from `π/6` to `5π/6` as `ψ` runs from 0 to `π`.
Then `w² = v((1+κ²)v − 2κc) = 4R·sin α·sin(α − δ)` with `R = √((1+κ²)² + 4κ²/3)` and
`tan δ = 2κ/(√3(1+κ²))`, and `1 − c² = (1 − 2cos 2α)/3`. All three radicals now depend on
`θ = 2α` through `cos θ` and `sin α`, and with `t = tan α` the squared integrand is a rational
function of `t`. The result is

    N₁ = ∫ 4√R · t²(t cos δ − sin δ) / ((1 + t²)·Z) dt,    Z² = t(t cos δ − sin δ)(1 + t²)(3t² − 1),

taken over `t` from `1/√3` through `∞` to `−1/√3`: a hyperelliptic integral on the genus-2 curve
`Z² = t(t − t₀)(t² + 1)(3t² − 1)`, `t₀ = tan δ`. Numerically the two forms agree to 29 digits
(`5.51226748592377377613798025361` against `…362`). The earlier count of a genus-5 cover
(three independent radicals) was of a larger curve that maps onto this one; the integrand only
needs the genus-2 quotient.

Two structural facts follow:
- The path's endpoints `t = ±1/√3` are branch points (roots of `3t² − 1`), so `N₁` is an integral
  between two Weierstrass points: half of a period.
- The differential has double poles at the branch points `t = ±i` with zero residue: it is of the
  second kind, like `E`'s integrand, and the complete `L = 2E(−3)` is the one-dimension-lower
  analogue (an elliptic curve, a period of a second-kind differential).

**No elliptic involution (checked numerically).** A genus-2 Jacobian splits (up to isogeny of
degree 2) into two elliptic curves iff a Möbius involution permutes the six branch points
`{0, t₀, i, −i, 1/√3, −1/√3}` in three pairs. Of the 15 pairings of the six points, none admits
one: the involution fixed by the first two pairs always fails the third (residuals 0.5–1.2). So
the Jacobian has no degree-2 elliptic factor. A splitting of higher degree (a Humbert surface)
is not excluded by this test.

**Control.** If the guide is a circle (`A = B`), `sp` is constant, the nested radical
disappears, and the length is an ordinary elliptic integral: for semi-axes (1, 1) and
`κ = 3/π`, `∫₀^π √(1 + κ² − 2κ cos ψ) dψ = 2√(1 + κ² + 2κ)·E(4κ/(1 + κ² + 2κ)) =
3.91469832138551893821403649496…`, the numeric integral and closed form agreeing to 30 digits.
So the new structure comes from the guide being a genuine ellipse.

**Status.** This is a candidate, not a proof of newness. The old class holds hyperelliptic arc
lengths too: a `poly_graph` of degree 4 has `√(1 + q²)` with `q = p′` a cubic, a genus-2 curve
`Z² = 1 + q(x)²` whose six branch points are the roots of `q = ±i`, and degree 6 gives genus up
to 4. A genus-2 curve alone is therefore not new. Two things count against a coincidence:
the old genus-2 curves have rational `q` up to `scale_x`/`scale_y`/`translate` by class numbers
(a countable, thin family in the 3-dimensional moduli space of genus-2 curves), while our
curve's moduli depend on `κ = 3/L`; and its differential is of the second kind with poles at
`t = ±i`, unlike the arc-length differential `√(1 + q²) dx`, which has a pole only at ∞.
### 13.1 Comparison with the old genus-2 curves (`probes/t6_curve_tests.wl`)

**The test.** `Z² = 1 + q(x)²` with `q` a cubic (any complex coefficients) holds iff the six
branch points split into two triples `T₁, T₂` and, in some coordinate (the pole `p` of `q`
moved to ∞ by `x ↦ 1/(x − p)`), the monic cubics with roots `T₁` and `T₂` differ by a constant:
equal sums of roots and equal sums of pairwise products. That is two equations in the unknown
`p`, so it holds on a hypersurface of the moduli space. The test returns exactly 0 on the
control `q = x³ − 2x`, both with the pole at ∞ and moved to `p = 3`.

**Results for `Z² = t(t − t₀)(t² + 1)(3t² − 1)`:**
1. *No symmetry.* At our `t₀` no Möbius map other than the identity permutes the six branch
   points (0 of 719 permutations; the control of sixth roots of unity has 11). So the curve is
   not a binomial curve `w² = 1 + c·xⁿ` either (genus 2 needs `n = 5, 6`, which have an
   order-5 or order-6 symmetry).
2. *A finite list of coincidences.* Eliminating `p` gives, for each of the 10 splittings, a
   polynomial in `t₀` with algebraic coefficients. After discarding degenerate roots (branch
   points colliding), 32 values of `t₀` remain, 6 of them real: `±2/√3`, `±3√3/7` and
   `±0.335657855782…` (a root of `73s³ + 3√3·s² + 9s + 3√3`). Only at those values is the curve
   of the form `1 + q²`. Ours is `t₀ = 0.516867565868…`, at distance 0.111 from the nearest.
   Directly at our `t₀`, the closest approach of the `1 + q²` conditions is a 1.5 % miss,
   identical at 60 and 120 digits.
3. *Transcendence closes it.* `t₀ = 2κ/(√3(1 + κ²))`, so `t₀` is algebraic iff `κ = 3/L` is,
   iff `L = 4E(3/4)` is. `L` is transcendental: the curve for modulus `k² = 3/4` has
   `j = 35152/9`, not an integer, so no complex multiplication, and by Chudnovsky a period and
   a quasi-period are algebraically independent, while `E(k)` is a nonzero algebraic
   combination of the two (the dictionary from `E` to `ω, η` is not re-derived here, so this
   step rests on the literature). Hence `t₀` is never one of the 32 values.

**Conclusion.** The curve `Z² = t(t − t₀)(t² + 1)(3t² − 1)` is not isomorphic over ℂ to the
arc-length curve of any polynomial graph of degree 4, however scaled or with whatever
coefficients, nor to a binomial curve. So `N₁` is not one of those old arc lengths, and its
curve is genuinely a different genus-2 curve. The same argument applies to any box with rational
data (the set of coincidences is recomputed for that ellipse's eccentricity; `κ` stays a
rational multiple of `1/L`).

**Not excluded.** The Jacobian of our curve could still be isogenous to a factor of the
Jacobian of a higher-genus old curve (a degree-5 or 6 polynomial graph has genus 3 or 4), or
split at a degree above 2, or `N₁` could still coincide numerically with some other old number.
So this settles the comparison with genus-2 old curves, not newness in general.

**Next.** (1) Test the higher-genus old families (degree-5 and degree-6 graphs): does their
Jacobian contain a factor isogenous to ours? That needs the Jacobian's decomposition and is
harder. (2) Search for integer relations between `N₁` and the other periods of the same
differential (the curve has four independent periods).
(If the comparison above is not enough:) a proof of newness would need transcendence results for such periods and is out of reach;
   a reduction to old constructors is the only outcome that can be proved.

## 14. Targets: a new operation, a named constant, and the inverse elliptic integral (2026-11-07)

User's definition of a target: **a new operation or named constant that we can P-construct;
the inverse elliptic integral is also a target.** This section records what the library already
has, what the warp machinery can and cannot supply, and the operation and constant constructed.

### 14.1 Where the inverse elliptic integrals stand in Lean

From `Pptc/Jacobi.lean` (section Outlook) and `Pptc/JacobiAddition.lean`:
- Forward integrals `F`, `E`, `Π` at P-constructible arguments: done.
- Inverse of the second kind, the amplitude `ellipticEAm`: done (`arc_of_length` along the
  ellipse, then the box).
- Inverse of the first kind, the Jacobi amplitude `jacobiAm`, hence `sn`, `cn`, `dn` at an
  arbitrary P-constructible argument `u`: **missing**. They are P-constructible exactly when
  the amplitude is, at every `u` presented as `F(φ)` for a P-constructible `φ`, and it
  suffices to fill a neighbourhood of 0.
- The recorded obstruction: `F` is not the arc length of any drawable curve. It is the integral
  of a differential with *no poles*, while an unbounded or elliptic drawn curve has a pole at
  infinity (a boundary term or a second-kind part). The most economical fix named there is a
  base curve with first-kind arc length, e.g. Serret's curves (the lemniscate moves at speed
  `√2/√(1 + t⁴)`).

### 14.2 The algebraic text curves cannot supply it (proved)

**Claim.** Let `γ(θ) = (x(θ), y(θ))` have `x, y` real trigonometric polynomials and
non-constant speed. Then its arc-length differential is never holomorphic, so its arc length is
never a first-kind integral and cannot be inverted to give `am`.

**Proof.** `speed² = T(θ)` is a real trigonometric polynomial of exact degree `d ≥ 1`. With
`z = e^{iθ}`, `T = z⁻ᵈ R(z)`, `R` of degree `2d`, `R(0) = c₋d = c̄_d ≠ 0`. Then
`√T dθ = √R · z^{−d/2 − 1} dz / i`: at `z = 0` this has a pole (order `d/2 + 1` on the curve
`w² = R`), so it is not holomorphic. By contrast the first-kind differential is
`dθ/√(1 − m sin²θ) = dz/(i√R)`: its speed is `1/√T`, the *reciprocal* shape. ∎

Checked in Wolfram (`degInfo`): the ellipse has `d = 2` (leading coefficient `(B² − A²)/4`,
nonzero off a circle), a glyph circle under Fade: Right has `d = 4` (`a²h²r⁴`), the Gerono
lobe has `d = 4` (`1/4`). A circle has `d = 0` (constant speed, linear arc length).

**Consequence.** Every text curve from a straight-guide preset (Square, Stop, Triangle, Chevron,
Fade, Slant, Cascade) with an ellipse or circle glyph has trigonometric-polynomial speed², so
none gives a first-kind arc length; a straight polygon edge goes to a parabola arc whose length
is elementary. Serret's curves are rational with denominators such as `1 + t⁴`, not images of
these under bilinear maps. Only the part of the machinery that places points by arc length on
a *curved* guide (`arcTrace`) can matter for `F`.

### 14.3 The new operation: the elliptic Kepler inverse

Take Warp Up (top guide the upper half of the ellipse with centre `(A, y_c)`, `y_c = d`, semi-axes
`A = w/2` and `B = d = (1 − a)h`; `B_guide = T + (0, τ_y)` with `τ_y = h − d`), `L` the half-length and
`s(ψ) = ∫₀^ψ √(A² sin²θ + B² cos²θ) dθ = B·E(ψ | μ)`, `μ = −(A² − B²)/B²`. A glyph edge
`v = σu + c` goes to

    x(ψ) = A(1 − cos ψ),    y(ψ) = y_c − B sin ψ + τ_y·(σ·s(ψ)/L + c),

the elliptic trochoid. Meeting the line `y = λx + μ₀` (`μ₀` an intercept) gives

    Φ(ψ) := κ·E(ψ | μ) − B sin ψ + λA cos ψ = c₀,
    κ = τ_y σ B / L,    c₀ = μ₀ + λA − y_c − τ_y c.

**Definition (elliptic Kepler inverse).** `Kep(κ, B, λA, μ; c₀)` is the unique `ψ ∈ [0, π]` with
`Φ(ψ) = c₀`, when `Φ` crosses `c₀` exactly once. (For a circle, `μ = 0`, `E(ψ) = ψ`, and this is the
classical Kepler equation `ψ − e sin ψ = M` up to constants, solved by the `sine` constructor.)

**P-constructibility (paper argument).** The warped edge is a piece of `T.outline` for the
`text` constructor, so it is a `PConstructibleCurve`; the line is a `poly_graph`; `restrict` to a
rational window around the crossing leaves exactly one point; `inter_x`/`inter_y` give `x*`, `y*`;
and `cos ψ* = 1 − x*/A`, `sin ψ*` follow by field operations and `sqrt`. The coefficient `κ`
contains `1/L`, which is `arc_length` of the half-ellipse between rational endpoints. So `Kep` at
P-constructible arguments is P-constructible.

**Not in Lean.** The statement needs the analytic facts about the `text` outline (the
intersection is a single point; `arcTrace` is the inverse of a strictly increasing arc length),
which have not been written. Whether `Kep` reduces to the old constructors is open (T1, §12).

### 14.4 The named constant: the Warp Up diagonal constant

**Definition.** Put ◢ (U+25E2, Segoe UI Symbol) in a square text box (any square size on the
0.1 in grid), apply Transform ▸ Warp Up at its default handle (stored `85714`), and draw the
box's diagonal from the top-left corner to the bottom-right corner. The hypotenuse of the warped
triangle crosses that diagonal exactly once (one sign change on a 2001-point grid). Let `δ_W` be
the crossing's horizontal position as a fraction of the box width.

    ψ*  = 1.49126947866372197223069719860257988051778674…   (ellipse angle at the crossing)
    δ_W = 0.460278476774386745602319370729…

At 288 pt the crossing is `x = y = 132.560201311023382733467978770088…` pt, and `L = 313.7335155363…`.
`δ_W` is the same to 30 digits for boxes of 72, 288 and 1000 pt, as scaling requires (everything
scales with the box). It is solved from `Kep` with all inputs UI-valid (default handle,
square box, one glyph). At the min handle stop (66667) the constant is `0.3943289301622131448248201…`.
Integer-relation search on `cos ψ*` finds no polynomial relation of degree ≤ 8 with coefficients
≤ 10⁵ (consistent with a transcendental value, not evidence of newness). Script:
`probes/t_kepler_constant.wl`.

### 14.5 What this does and does not do for the first-kind inverse

It gives an inversion of the type the library says is missing, **`E`-type arc length minus an
algebraic correction**, but for the *second* kind on an ellipse, where `E` was already invertible.
The first-kind amplitude needs the arc length `J` of a Bézier or polynomial graph together with
the second-kind part and an algebraic boundary term `tan φ·Δ(φ)` removed, all in one variable.
For the guide `y = x³`, `J(x) = x√(1 + 9x⁴)/3 + (2/3)∫dx/√(1 + 9x⁴)`: pure first kind plus an
algebraic boundary term, and a slide preset's trochoid carries `J(x)` in its height. The crossing
of that trochoid with a `poly_graph` inverts `J(x) − (polynomial)`, but the boundary term is
`x√(1 + 9x⁴)/3`, not a polynomial. Open routes (route (i)'s pure-cubic form was tried in §14.6 and closed): (i) a drawn curve supplying
that algebraic term (offsets give `1/√Q` terms); (ii) a mismatch preset (cubic over parabola)
that puts two different arc-length inversions in one image; (iii) a numerical search over
presets and glyph edges for a trochoid height of the form `F + polynomial`.

### 14.6 Route 1 tried: the pure cubic guide (`probes/t_route1.wl`)

**Result: closed in this form.** Four findings.

1. **The boundary term is a tangent segment.** For `y = x³`, `J(T) = (T/3)√(1 + 9T⁴) + (2/3)Φ(T)`
   with `Φ(T) = ∫₀^T dx/√(1 + 9x⁴)` (checked to 29 digits at `T = 0.8`). The tangent at
   `(T, T³)` meets the x-axis at `x = 2T/3`, at distance exactly `(T/3)√(1 + 9T⁴)` from the point:
   the boundary term *is* the tangent length to the x-axis. The involute point of the cubic,
   with the string unwound from the origin, lies on the same tangent at distance `J(T)` from the
   point, so the first-kind quantity is the distance between the involute point and the tangent's
   x-axis intercept: `J − B = (2/3)Φ(T)`. This is a geometric picture of exactly what the
   library's obstruction says laying out a length cannot do. Whether an involute-type operation
   can be drawn, and used to invert `Φ`, is open; I have not shown that it can.

2. **No preset has a pure cubic guide.** For an even quartic `Q = aZ⁴ + bZ² + c`,
   `∫√Q dZ = Z√Q/3 + (1/3)∫(bZ² + 2c)/√Q dZ` (checked numerically). The second-kind part
   `∫Z²/√Q` carries the coefficient `b/3`, which no algebraic term can cancel, and `b = 0` exactly
   when the guide is a pure cubic, `g′ = k(Z − z₀)²`. The Wave guides have `g′ = k(3Z² − 1)`,
   `b = −6k² ≠ 0`; Curve: Up/Down's top cubic has two distinct critical points (discriminant
   `63/4 > 0`); every other preset has a line, conic or parabola. So the heights of the
   trochoids available carry both a first-kind and a second-kind part, in addition to a boundary term.

3. **The correction a glyph can supply is the wrong shape (proved).** A circle (or ellipse) glyph
   with centre `(u₀, v₀)` and radius `r`, crossed with a drawn `poly_graph` `y = P(x)`, gives
   `J(X) = L·u₀ ± (L/τ)·√(τ²r² − p(X)²)`, with `p(X) = P(X) − g(X) − τv₀` a polynomial. To
   match the boundary term `(X/3)√(1 + 9c²X⁴)` one needs the identity
   `p² + (κ₀X)² + (3cκ₀X³)² = (τr)²`, `κ₀ = τ/(3L)`: a sum of squares of three real polynomials,
   two of them non-constant, equal to a constant. That is impossible over ℝ (the leading
   coefficient of a sum of squares of real polynomials is positive). The box-extreme version gives
   (derived by hand, not machine-checked) `J(X) = L·u₀ + ρL²g′/√(τ² + (τ² + L²)g′²)`, which is
   not of the boundary form either.

4. **What this leaves.** The natural next steps are not preset choices. They are either (a) a
   source of a pure cubic guide together with a way to read off its tangent length (an involute
   or similar new operation), or (b) routes 2 and 3 of §14.5: a mismatch preset, which brings
   two different arc-length inversions into one image, and a numerical search for a trochoid height
   of the form `F + polynomial`. The base curve `y = a·x³` (a `power_law`) already exists in
   the class, so the pure cubic itself is available as a drawn curve but not as a text guide.

### 14.7 Route 3 tried: which trochoid heights are "first kind plus algebraic" (`probes/t_route3.wl`)

**Result: none. A theorem settles every preset at once.**

**Reduction (verified to 24 digits on two random quartics).** For `Q = q₀ + q₁X + q₂X² + q₃X³ + q₄X⁴`,

    ∫√Q dX = [(X/3 + q₃/(12 q₄))·√Q] + ∫ (c₀ + c₁X + c₂X²)/√Q dX,
    c₂ = (q₂ − 3q₃²/(8q₄))/3,  c₁ = (3q₁/2 − q₂q₃/(4q₄))/3,  c₀ = (2q₀ − q₁q₃/(8q₄))/3.

The three integrands are the three classes on the elliptic curve `w² = Q`: `dX/√Q` is first
kind, `X dX/√Q` third kind (poles at the two points at infinity), `X² dX/√Q` second kind.

**Theorem.** For a cubic guide `y = g(x)` with `Q = 1 + g′²`, the arc length `J` is a multiple of
a first-kind integral plus an algebraic function iff `c₁ = c₂ = 0`, and (solved in Wolfram, with
`g′ = αx² + βx + γ`) that holds iff `γ = β²/(4α)`, i.e. iff **`g′` is a perfect square
`α(x − x₀)²`**: the pure, possibly shifted, cubic. Otherwise `J` carries a second-kind part
(`c₂ ≠ 0`) and, if `Q` is not even about its centre, a third-kind part as well.

**Applied to the presets.** `g′` is a perfect square iff the discriminant of the quadratic `g′`
vanishes. The Wave guide has `g′ ∝ 3Z² − 1` (`Z = 2x/w − 1`), discriminant `12 ≠ 0` in every
box and handle setting; the Curve top cubic has `g′ ∝ 3/4 − (9/2)X + (3/2)X²`, discriminant
`63/4 ≠ 0`; these are shape constants, unaffected by the handle, the box ratio, or the Wave's
sideways handle. Every other preset has a line, conic or parabola for a guide. So:

> **No crossing or extreme of any slide-preset trochoid with any algebraic correction can invert
> a first-kind integral.** This covers poly_graph crossings (§14.6), glyph-circle crossings and
> extremes, and any other drawn algebraic curve.

For the Wave guide in a square box at the default handle (`K = 5ah/w = 0.625`) the height is
`g + κ·J` with `J = boundary + (2c/3)F + (b/3)Ê` on the even quartic `9K²Z⁴ − 6K²Z² + 1 + K²`;
the ratio of the second-kind to first-kind coefficient is `b/(2c) = −3K²/(1 + K²) = −0.8427`,
never 0 for `K ≠ 0`.

**Why combining two guides does not rescue it.** The even quartics of Wave and Curve have
shape invariant `b²/(ac)` ranging over `(0, 4)` in both families, so with a continuum of
parameters one could put both on the same elliptic curve (the UI grid gives only isolated values), with the heights both linear in `x` after a translation
and scaling. But the reduction coefficients of one quartic are proportional to `(2c, b)`, so the
two heights carry the same combination `2c·F + b·Ê` (up to a constant) and no linear
combination eliminates `Ê`. Ellipse guides sit on a different real form of the curve (two real
branch points when `A > B`, four when `A < B`, against none for the cubic guides), so they cannot
share its variable without an imaginary scaling.

**What this leaves.** The first-kind inverse is not reachable from a slide-preset trochoid by
crossings or extremes. Still open: route 2 (a mismatch preset, with two different arc-length
inversions in one image, which is not a slide preset and is not covered by the theorem), a
construction that supplies a pure cubic guide or an involute (§14.6), or a non-text source of a
first-kind curve (Serret's curve) as a new base curve.
