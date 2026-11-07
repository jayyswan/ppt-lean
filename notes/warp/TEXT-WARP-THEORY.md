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
  - Its box extremes are probably *not* new. The derivative condition is algebraic in
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
