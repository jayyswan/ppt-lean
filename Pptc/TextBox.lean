/- Copyright (c) 2024 Lean Community. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file is part of the Pptc (PowerPoint Constructibility) project.
-/

import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Pptc.Curves

/-! # Pptc.TextBox

The data side of text: what a single PowerPoint text box holds, and the outline it draws.
`Pptc.Defs` imports this file for its one constructor `PConstructibleCurve.text`, which turns
a well-formed `TextBox` into a curve (Merge Shapes ▸ Fragment on the box). Nothing here
mentions `PConstructible`, and nothing needs to: every input is a step count or a menu choice,
so every number below is rational. Text needs no third mutual inductive.

Text is a structure, not an inductive, because it has no construction history. A box holds
one row of glyphs with one Transform setting, and no operation turns a curve back into text.
That gives the two restrictions on warps for free:
* warps act only on text, since `WarpPreset.map` appears only inside `TextBox.outline`;
* each box is warped once, since `TextBox.warp` is a single field.

## What the UI can set

Only choices count: list entries, spinner arrow steps, the Grow/Shrink Font buttons and
preset menu items, never a typed value. Measured in PowerPoint
(`notes/warp/probes/probe_ui_inputs.py`, `probe_layout.py`, `probe_layout2.py`,
`probe_offset.py`, `probe_offset2.py`, `probe_handle.py`):

* **Font size.** The Font dialog's spinner steps by 0.1 pt over `[1, 4000]`, and the size
  is stored as that number of tenths. A glyph outline is drawn at the stored size rounded
  to the nearest multiple of 0.75 pt (one pixel at 96 dpi): 72.1 to 72.26 draw the 72 pt
  outline, 72.4 to 72.9 the 72.75 pt one. No stored size lies halfway between two
  multiples, so the rounding never meets a tie. The stored size, not the drawn one, is what
  baseline offset reads.
* **Baseline offset.** The Offset spinner steps by 2 % over `[-100 %, 100 %]`; the
  Superscript and Subscript checkboxes set 30 % and −25 %, and stepping from −25 % lands back
  on even values. With a stored size `S` and a nonzero offset `p %`, writing
  `d = |p| · S / 100` (fitted exactly over about 800 glyphs at 9 sizes):
  - the glyph is drawn at `2S/3` rounded to the nearest multiple of 0.75 pt (again never a
    tie), and the pen then advances by that drawn size;
  - a superscript (`p > 0`) moves up by `0.75 · ⌊4d/3 + 1/2⌋`, that is `d` rounded to the
    nearest 0.75 pt (never a tie on this grid);
  - a subscript (`p < 0`) moves down by `0.75 · max 0 ⌊4d/3 - 1/2⌋`: one pixel less than
    that, ties going down (−25 % at 10.5 pt moves 2.25 pt), and never upward.
* **Character spacing.** The dialog's `By` spinner steps by 0.1 pt, Expanded or Condensed,
  up to 1000 pt either way: the field accepts `1000` and refuses the keystroke that would
  make `1001`, `1000.1` or a second decimal. The menu presets −3, −1.5, 0, 3, 6 pt lie on
  that grid. (COM accepts any value, so only the dialog shows the bound.)
* **Layout.** Each glyph advances the pen by `advance · size / unitsPerEm` rounded to a
  multiple of 0.75 pt, plus its character spacing scaled by drawn size / stored size and
  rounded separately, step by step (not cumulatively). Exact halves round up (a 192 pt `●`
  advances 165.375 → 165.75 pt), as Lean's `round` does; the scaled spacing never meets a
  tie. Glyphs sit on a common baseline unless offset.
* **Kerning** is on by default from 12 pt, and adds the font's pair adjustment to the pen
  step before it is snapped (Arial `AV` at 72 pt: −152 units, step 48 → 42.75 pt). Segoe UI
  Symbol has no kerning pairs among the glyphs below, so it does not enter here; a glyph
  with pairs would need it in `penStep`.
* **Equalize Character Height** (Font dialog checkbox, here for the whole row) stretches
  each glyph vertically, by one affine map, so that its ink runs from its baseline (raised
  or lowered if offset) up to the band height `equalizeBand` of its drawn size. The band is
  computed from pixel-rounded font metrics; see `equalizeBand` and
  `notes/warp/EQUALIZE-AND-OFFSET.md`.
* **Box size.** The Height and Width spinners step by 0.1 in = 7.2 pt. The warp fills the
  whole shape box: the text insets do not enter.
* **Handle.** A drag stores whatever value the pointer lands on, which is not a clear
  choice, except when it is dragged past an end of its range: then the stored value is the
  bound exactly (Stop: `val 14286` and `val 50000`). So a handle takes its spec default or
  one of its two bounds. The polar handle of the Warped presets reaches only its outer stop,
  except on Warped Button; see `WarpPreset.stops`.

## The warp

Measured in `notes/warp/TEXT-WARP-THEORY.md` §2 and checked against this file's definitions
by `probe_textbox_model.py`: the ink box of the whole row is normalized to `[0, 1]²`, `u`
across and `v` top to bottom, and sent by the ruled map `(1 - v) · T(u) + v · B(u)` between
the preset's two guide paths, each traced at constant speed, into the box `[0, w] × [0, h]`.
Coordinates are the spec's, `y` pointing down. PowerPoint then refits the image with fresh
Béziers, within about 0.5 pt rms on a 4 in box; the exact image is the idealization.

All 36 modelled presets were checked at every reachable handle stop (149 cases, two box
sizes; `probe_presets_model.py`). PowerPoint's outline lies within about 0.7 pt of the
model's, and the model's within about 2 pt of PowerPoint's, which is the error of treating
the font's glyphs as true circles. The exceptions all have one cause
(`probe_presets_fill.py`). At some box sizes, with no pattern found, PowerPoint spreads the
text over only 48/49 of a guide's length, on one guide or on both. The fitted fractions are
0.9795 ± 0.0002 (times the waves' usual underestimate, below), and with them the misses fall
back to the ≤ 0.9 pt floor. Chevron (straight guides) shows it at 5 in × 3 in, the curved
presets at various sizes, and the waves at 4 in square, where it explains the "exceptional"
fill 0.976 ≈ 0.99589 · 48/49. Some size always avoids it, and a result can be scaled, so it
is set aside. The waves also fill a little short at every size, by PowerPoint's length
estimate: 0.996 for one cubic per guide, 0.998 for two (the idealization `L_est = L`,
`arcTrace`). This is the span
artifact of `notes/spiral/F1.md` (e), now seen on straight guides too. It is a numerical
slip, not a different map, so the model spans the whole guide. A construction should name its
box size and check it with `probe_presets_model.py`.

Modelled: the 12 straight presets, written at constant speed or traced by `arcTrace`; the 4
ellipse-arc presets (Warp Up/Down, Ring: Inside/Outside); the 4 Warped presets, one row of
text; the 8 cubic Bézier presets (the 4 waves, Inflate, Deflate, Curve: Up/Down); and the 6
presets with one straight and one quadratic guide (Inflate/Deflate: Top/Bottom and the two
combinations, one row of text). Their curved guides are traced by `arcTrace`, by true arc
length. Not yet modelled: the 4 Follow Path presets, which place glyphs rigidly rather than
warping them.
-/

namespace Pconstructible

/-! ### Glyph outlines -/

/-- One piece of an idealized glyph outline, with rational data in font units:
* `seg p q` is the straight edge from `p` to `q`;
* `ellArc c rx ry lo hi` is the part of the axis-aligned ellipse with centre `c` and
  semi-axes `rx`, `ry` that lies in the window `[lo.1, hi.1] × [lo.2, hi.2]`. -/
inductive GlyphPiece
  | seg (p q : ℚ × ℚ)
  | ellArc (c : ℚ × ℚ) (rx ry : ℚ) (lo hi : ℚ × ℚ)

/-- The point set of one outline piece. -/
def GlyphPiece.toSet : GlyphPiece → Set (ℝ × ℝ)
  | .seg p q =>
      (fun t : ℝ => ((1 - t) * p.1 + t * q.1, (1 - t) * p.2 + t * q.2)) '' Set.Icc 0 1
  | .ellArc c rx ry lo hi =>
      {z | ((z.1 - c.1) / rx) ^ 2 + ((z.2 - c.2) / ry) ^ 2 = 1 ∧
        (lo.1 : ℝ) ≤ z.1 ∧ z.1 ≤ hi.1 ∧ (lo.2 : ℝ) ≤ z.2 ∧ z.2 ≤ hi.2}

/-- The catalogued glyphs, all from Segoe UI Symbol (2048 units per em, `y` up). A glyph is
used only where its outline is clearly a geometric figure, and then it is that figure:
three are an ellipse and its two halves, with centre and semi-axes read off the integer
bounding box of the font's own outline, and two are polygons (a rectangle and a right
triangle), whose corners are the font's own integer points (the font stores no curves for
them, so nothing is idealized). -/
inductive Glyph
  /-- ● U+25CF BLACK CIRCLE: bounding box `(140, -25)–(1624, 1458)`, within 0.15 %. -/
  | blackCircle
  /-- ◗ U+25D7 RIGHT HALF BLACK CIRCLE: the right half, flat side on `x = 882`, within
  0.07 %. -/
  | rightHalfBlackCircle
  /-- ◖ U+25D6 LEFT HALF BLACK CIRCLE: the left half, flat side on `x = 882`, within
  0.06 %. -/
  | leftHalfBlackCircle
  /-- █ U+2588 FULL BLOCK: the rectangle `(-10, -440)–(1931, 1501)`, a square of side 1941.
  It is one four-point contour in the font. It is 20 units wider than its advance, so
  neighbouring blocks overlap by 20 units. -/
  | fullBlock
  /-- ◢ U+25E2 BLACK LOWER RIGHT TRIANGLE: the right isosceles triangle with vertices
  `(1599, 1434)`, `(1599, 0)`, `(165, 0)`; legs of length 1434, hypotenuse slanted. It is the
  one glyph here with a slanted straight edge, which a curved warp turns into a trochoid. -/
  | lowerRightTriangle

/-- Units per em of the font the glyphs come from. -/
def Glyph.unitsPerEm (_ : Glyph) : ℚ := 2048

/-- The font's Windows ascent (`OS/2.usWinAscent`), in font units. -/
def Glyph.winAscent (_ : Glyph) : ℚ := 2210

/-- The font's Windows descent (`OS/2.usWinDescent`), in font units. -/
def Glyph.winDescent (_ : Glyph) : ℚ := 514

/-- The bottom of a glyph's ink, in font units (`glyf` bounding box). -/
def Glyph.inkBottom : Glyph → ℚ
  | .fullBlock => -440
  | .lowerRightTriangle => 0
  | _ => -25

/-- The top of a glyph's ink, in font units (`glyf` bounding box). -/
def Glyph.inkTop : Glyph → ℚ
  | .fullBlock => 1501
  | .lowerRightTriangle => 1434
  | _ => 1458

/-- The advance width of a glyph, in font units (`hmtx`). -/
def Glyph.advance : Glyph → ℚ
  | .blackCircle => 1764
  | .rightHalfBlackCircle => 1764
  | .leftHalfBlackCircle => 1764
  | .fullBlock => 1921
  | .lowerRightTriangle => 1764

/-- The idealized outline of a glyph, in font units with `y` up. The three circular glyphs
share the centre `(882, 1433/2)` and semi-axes `742` and `1483/2`; the block and the
triangle are their polygon's edges. -/
def Glyph.pieces : Glyph → List GlyphPiece
  | .blackCircle => [.ellArc (882, 1433 / 2) 742 (1483 / 2) (140, -25) (1624, 1458)]
  | .rightHalfBlackCircle =>
      [.ellArc (882, 1433 / 2) 742 (1483 / 2) (882, -25) (1624, 1458), .seg (882, -25) (882, 1458)]
  | .leftHalfBlackCircle =>
      [.ellArc (882, 1433 / 2) 742 (1483 / 2) (140, -25) (882, 1458), .seg (882, -25) (882, 1458)]
  | .fullBlock =>
      [.seg (-10, -440) (1931, -440), .seg (1931, -440) (1931, 1501),
        .seg (1931, 1501) (-10, 1501), .seg (-10, 1501) (-10, -440)]
  | .lowerRightTriangle =>
      [.seg (1599, 1434) (1599, 0), .seg (1599, 0) (165, 0), .seg (165, 0) (1599, 1434)]

/-! ### Rows -/

/-- `x` rounded to the nearest multiple of 0.75 pt, the pixel grid layout snaps to. -/
def snap (x : ℚ) : ℚ := 3 / 4 * round (x / (3 / 4))

/-- One character of a row: its glyph, its stored font size in tenths of a point, the
character spacing after it in tenths of a point, and its baseline offset in percent
(`0` for none, `30` for Superscript, `-25` for Subscript). -/
structure RowGlyph where
  glyph : Glyph
  sizeTenths : ℕ
  spacingTenths : ℤ
  offsetPercent : ℤ := 0

/-- The stored font size in points. -/
def RowGlyph.storedSize (g : RowGlyph) : ℚ := g.sizeTenths / 10

/-- The size the outline is drawn at: the stored size, or two thirds of it when offset,
snapped to 0.75 pt. -/
def RowGlyph.size (g : RowGlyph) : ℚ :=
  if g.offsetPercent = 0 then snap g.storedSize else snap (2 / 3 * g.storedSize)

/-- How far the glyph's baseline moves up, in points (negative is down). Superscripts round
`d = |p| · S / 100` to the nearest pixel; subscripts go one pixel less, with ties going
down, and never above the baseline. -/
def RowGlyph.rise (g : RowGlyph) : ℚ :=
  let d : ℚ := |(g.offsetPercent : ℚ)| * g.storedSize / 100
  if 0 < g.offsetPercent then 3 / 4 * ⌊4 * d / 3 + 1 / 2⌋
  else if g.offsetPercent < 0 then -(3 / 4 * max 0 ⌊4 * d / 3 - 1 / 2⌋)
  else 0

/-- How far the pen moves past this glyph: the advance at the drawn size, snapped to 0.75 pt,
plus the character spacing scaled by drawn size / stored size (so by about 2/3 for an offset
glyph), snapped separately (probe_row_model.py and the spacing sweeps in
`notes/warp/EQUALIZE-AND-OFFSET.md`). -/
def RowGlyph.penStep (g : RowGlyph) : ℚ :=
  snap (g.glyph.advance * g.size / g.glyph.unitsPerEm) +
    snap (g.spacingTenths / 10 * (g.size / g.storedSize))

/-- The Equalize Character Height band, in points, for a glyph drawn at `size` points: the
ascent share of a 1.2-size line, computed from pixel-rounded metrics. With `n` the size in
pixels, `a` and `d` the font's Windows ascent and descent rounded to pixels and
`L = round(1.2 n)` the line height, the band is `round(L · a / (a + d))` pixels. It is a
function of the font and the drawn size only (not of the glyph or the rest of the row), and
it fits all 5332 drawn sizes of Segoe UI Symbol and 1497 of Arial, Times New Roman and
Cambria (`probe_equalize_table.py`). -/
def equalizeBand (g : Glyph) (size : ℚ) : ℚ :=
  let n : ℚ := size / (3 / 4)
  let a : ℤ := round (n * g.winAscent / g.unitsPerEm)
  let d : ℤ := round (n * g.winDescent / g.unitsPerEm)
  let L : ℤ := round (6 / 5 * n)
  3 / 4 * round ((L * a : ℚ) / (a + d))

/-- The vertical scale of a glyph's outline, from font units to points: `size / unitsPerEm`,
or under Equalize the factor that stretches its ink onto the band. -/
def RowGlyph.yScale (g : RowGlyph) (eq : Bool) : ℚ :=
  if eq then equalizeBand g.glyph g.size / (g.glyph.inkTop - g.glyph.inkBottom)
  else g.size / g.glyph.unitsPerEm

/-- The outline of a glyph with its pen at `pen` on the baseline `y = 0`, in points with `y`
down: font units are scaled by `size / unitsPerEm` across, by `yScale` up (under Equalize,
with the ink's bottom moved onto the baseline), flipped, and raised by `rise`. Equalize
leaves `x` alone and stretches each glyph by one exact affine map (probes 13–14). -/
def RowGlyph.toSet (g : RowGlyph) (eq : Bool) (pen : ℚ) : Set (ℝ × ℝ) :=
  let lift : ℚ := if eq then g.glyph.inkBottom else 0
  (fun z : ℝ × ℝ =>
      (pen + g.size / g.glyph.unitsPerEm * z.1,
        -(g.rise + g.yScale eq * (z.2 - lift)))) ''
    ⋃ piece ∈ g.glyph.pieces, piece.toSet

/-- The ink of a row whose first pen position is `pen`, with Equalize on or off. -/
def rowInk (eq : Bool) : List RowGlyph → ℚ → Set (ℝ × ℝ)
  | [], _ => ∅
  | g :: gs, pen => g.toSet eq pen ∪ rowInk eq gs (pen + g.penStep)

/-! ### Warps -/

/-- The ruled warp between a top guide `T` and a bottom guide `B`: the point `(u, v)` of the
unit square goes to `(1 - v) · T(u) + v · B(u)`. Every bending Transform preset has this
form, with `T` and `B` traced at constant speed (`TEXT-WARP-THEORY.md` §2). -/
def ruledWarp (T B : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - p.2) * (T p.1).1 + p.2 * (B p.1).1, (1 - p.2) * (T p.1).2 + p.2 * (B p.1).2)

/-- The point a fraction `u` of the way along the curve `γ` (traced over `[0, 1]`), measured
by arc length: `γ τ` for the least `τ ∈ [0, 1]` with
`arcLengthOf γ 0 τ ≥ u · arcLengthOf γ 0 1`.

This is the idealized tracing of a curved guide. PowerPoint places text by exact arc length
but scales it to its own estimate `L_est` of the guide's total length. For a Bézier guide that
estimate is a little short: 0.4 % at typical box sizes and 2.4 % at a few exceptional ones
(`notes/warp/TEXT-WARP-THEORY.md` §8.2–8.3). It is a numerical approximation, not a design
choice, so the model uses the true length `arcLengthOf γ 0 1` (decision of 2026-11-06).
PowerPoint measures straight and circular guides exactly, so for those nothing is idealized. -/
noncomputable def arcTrace (γ : ℝ → ℝ × ℝ) (u : ℝ) : ℝ × ℝ :=
  γ (sInf {τ ∈ Set.Icc (0 : ℝ) 1 | u * arcLengthOf γ 0 1 ≤ arcLengthOf γ 0 τ})

/-- The straight guide from `p` to `q`, traced at constant speed. -/
def segGuide (p q : ℝ × ℝ) (u : ℝ) : ℝ × ℝ :=
  ((1 - u) * p.1 + u * q.1, (1 - u) * p.2 + u * q.2)

/-- The three-piece polyline `p₀ → p₁ → p₂ → p₃`, a third of the parameter per piece. The
pieces need not have equal lengths; a warp traces it with `arcTrace`. -/
noncomputable def poly3Guide (p₀ p₁ p₂ p₃ : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 / 3 then segGuide p₀ p₁ (3 * t)
  else if t ≤ 2 / 3 then segGuide p₁ p₂ (3 * t - 1) else segGuide p₂ p₃ (3 * t - 2)

/-- The arc of the axis-aligned ellipse with centre `c` and semi-axes `wR`, `hR`, by its
parametric angle `φ₀ + t Δ`. Used where an `arcTo` starts and ends at multiples of 90°, where
the spec's visual angles and the parametric ones agree; it stays a valid tracing when
`hR = 0` (a flat guide). -/
noncomputable def ellArcGuide (c : ℝ × ℝ) (wR hR φ₀ Δ t : ℝ) : ℝ × ℝ :=
  (c.1 + wR * Real.cos (φ₀ + t * Δ), c.2 + hR * Real.sin (φ₀ + t * Δ))

/-- The arc of the same ellipse by the spec's *visual* angle `θ = θ₀ + t Δ`: the point of the
ellipse on the ray from `c` at angle `θ` (`y` down, so positive angles turn clockwise on
screen). This is the literal meaning of an `arcTo` with `stAng = θ₀`, `swAng = Δ`; it is
used for the sweeps that do not end at a multiple of 90° (Ring, Warped Circle). -/
noncomputable def ellArcVisualGuide (c : ℝ × ℝ) (wR hR θ₀ Δ t : ℝ) : ℝ × ℝ :=
  let θ := θ₀ + t * Δ
  let ρ := wR * hR / √((hR * Real.cos θ) ^ 2 + (wR * Real.sin θ) ^ 2)
  (c.1 + ρ * Real.cos θ, c.2 + ρ * Real.sin θ)

/-- The quadratic Bézier with ends `p`, `q` and control point `c`, written as the cubic with
the same parametrization (degree elevation: handles `(p + 2c)/3` and `(q + 2c)/3`). -/
noncomputable def quadBezierParam (p c q : ℝ × ℝ) : ℝ → ℝ × ℝ :=
  bezierParam p ((p.1 + 2 * c.1) / 3, (p.2 + 2 * c.2) / 3)
    ((q.1 + 2 * c.1) / 3, (q.2 + 2 * c.2) / 3) q

/-- Two cubic Béziers end to end, `p₁ p₂ p₃ p₄` then `p₄ q₂ q₃ q₄`, half the parameter each.
-/
noncomputable def bezier2Guide (p₁ p₂ p₃ p₄ q₂ q₃ q₄ : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 / 2 then bezierParam p₁ p₂ p₃ p₄ (2 * t) else bezierParam p₄ q₂ q₃ q₄ (2 * t - 1)

/-- The four wave presets share one shape. Each guide is one cubic (`double = false`) or two
(`double = true`) with control heights `y, y - d, y + d, y` per cubic, where `y` is `y₁ = ah`
on top and `y₄ = h - y₁` below, and the bulge is `d = e · 10 y₁ / 3` with `e = 1` (Wave:
Down, Double Wave: Down-Up) or `e = -1` (Wave: Up, Double Wave: Up-Down). The control
points are equally spaced across each cubic. The sideways handle `b` shortens both guides to
`(1 - 2|b|) w` and starts them at `max 0 (-2bw)` (top) and `max 0 (2bw)` (bottom). -/
noncomputable def waveMap (double : Bool) (e a b w h : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  let y₁ := a * h
  let d := e * (10 / 3 * y₁)
  let s := (1 - 2 * |b|) * w
  let guide (x y : ℝ) : ℝ → ℝ × ℝ :=
    if double then
      arcTrace (bezier2Guide (x, y) (x + s / 6, y - d) (x + s / 3, y + d) (x + s / 2, y)
        (x + 2 * s / 3, y - d) (x + 5 * s / 6, y + d) (x + s, y))
    else arcTrace (bezierParam (x, y) (x + s / 3, y - d) (x + 2 * s / 3, y + d) (x + s, y))
  ruledWarp (guide (max 0 (-2 * b * w)) y₁) (guide (max 0 (2 * b * w)) (h - y₁))

/-- The Transform presets modelled so far, named as in PowerPoint's Transform gallery
(`notes/warp/TEXT-WARP-THEORY.md` §7 maps them to the file format's names). Every guide is
the spec's path (`presetTextWarpDefinitions.xml`) with `l = t = 0`; `WarpPreset.map` gives
the formulas, and `notes/warp/probes/probe_presets_model.py` checks each one, at every
handle stop, against PowerPoint. -/
inductive WarpPreset
  /-- "Square" (`textPlain`). The handle slides the guides sideways: the top guide covers
  `[max 0 (w - 2aw), min w (2(1-a)w)]` and the bottom one `[max 0 ((2a-1)w), min w (2aw)]`,
  both all of `[0, w]` at the default `a = 1/2`. -/
  | square
  /-- "Stop" (`textStop`): top `(l, ah) → (w/3, t) → (2w/3, t) → (r, ah)`, and its mirror
  image at the bottom. -/
  | stop
  /-- "Triangle: Up" (`textTriangle`): top `(l, ah) → (hc, t) → (r, ah)`, bottom straight. -/
  | triangleUp
  /-- "Triangle: Down" (`textTriangleInverted`): top straight, bottom
  `(l, ah) → (hc, b) → (r, ah)`. -/
  | triangleDown
  /-- "Chevron: Up" (`textChevron`): both guides bent up at the centre by `ah`. -/
  | chevronUp
  /-- "Chevron: Down" (`textChevronInverted`): both guides bent down at the centre by
  `(1 - a) h`. -/
  | chevronDown
  /-- "Fade: Right" (`textFadeRight`): the right end pinched to `[ah, h - ah]`. -/
  | fadeRight
  /-- "Fade: Left" (`textFadeLeft`): the left end pinched to `[ah, h - ah]`. -/
  | fadeLeft
  /-- "Fade: Up" (`textFadeUp`): the top guide shortened to `[aw, w - aw]`. -/
  | fadeUp
  /-- "Fade: Down" (`textFadeDown`): the bottom guide shortened to `[aw, w - aw]`. -/
  | fadeDown
  /-- "Slant: Up" (`textSlantUp`): parallel guides rising by `ah` to the right. -/
  | slantUp
  /-- "Slant: Down" (`textSlantDown`): parallel guides falling by `h - ah` to the right. -/
  | slantDown
  /-- "Cascade: Up" (`textCascadeUp`): the top guide rises by `(1-a)h/4`, the bottom one
  by `(1-a)h`. -/
  | cascadeUp
  /-- "Cascade: Down" (`textCascadeDown`): the mirror image of Cascade: Up. -/
  | cascadeDown
  /-- "Warp Up" (`textCanUp`): two upper half-ellipses of height `(1 - a) h`. -/
  | warpUp
  /-- "Warp Down" (`textCanDown`): two lower half-ellipses of height `ah`. -/
  | warpDown
  /-- "Ring: Inside" (`textRingInside`): two whole ellipses of height `ah`, swept clockwise
  on screen from the left end by `21599999` units (1/60000°), just short of a full turn. -/
  | ringInside
  /-- "Ring: Outside" (`textRingOutside`): as Ring: Inside, swept the other way. -/
  | ringOutside
  /-- "Arch: Warped" (`textArchUpPour`): the upper half of the box's inscribed ellipse, and
  the same arc scaled by `a` about the centre. The polar handle keeps its default angle. -/
  | archWarped
  /-- "Arch: Warped Down" (`textArchDownPour`): the lower half of the inscribed ellipse
  scaled by `a` on top, the lower half itself below. -/
  | archWarpedDown
  /-- "Warped Circle" (`textCirclePour`): the inscribed ellipse and its copy scaled by `a`,
  each swept from the left end by `21599998` units, just short of a full turn. -/
  | warpedCircle
  /-- "Warped Button" (`textButtonPour`), one row of text: its first two guides, which are
  those of Arch: Warped. Its handle range differs. -/
  | warpedButton
  /-- "Wave: Down" (`textWave1`): two cubic Bézier guides, each an affine copy of `x³ - x`,
  with a height handle `a` and a sideways handle `b`; see `waveMap`. -/
  | waveDown
  /-- "Wave: Up" (`textWave2`): Wave: Down with the bulge reversed. -/
  | waveUp
  /-- "Double Wave: Down-Up" (`textDoubleWave1`): two periods of Wave: Down per guide. -/
  | doubleWaveDownUp
  /-- "Double Wave: Up-Down" (`textWave4`): two periods of Wave: Up per guide. -/
  | doubleWaveUpDown
  /-- "Inflate" (`textInflate`): top cubic `(l, ah), (w/3, -ah/3), (2w/3, -ah/3), (r, ah)`
  bulging out of the box, and its mirror image at the bottom. -/
  | inflate
  /-- "Deflate" (`textDeflate`): top cubic `(l, t), (w/3, 4d/3), (2w/3, 4d/3), (r, t)` with
  `d = a · min w h`, bulging in, and its mirror image at the bottom. -/
  | deflate
  /-- "Curve: Up" (`textCurveUp`): top cubic `(l, ah), (w/3, 5ah/4), (2w/3, 3ah/4), (r, t)`;
  bottom `(l, h - 3ah/8), (w/3, h + ah/8), (2w/3, h + ah/8), (r, h - 3ah/8)`. -/
  | curveUp
  /-- "Curve: Down" (`textCurveDown`): top `(l, t), (w/3, 3ah/4), (2w/3, 5ah/4), (r, ah)`,
  the mirror image of Curve: Up's; the same bottom guide. -/
  | curveDown
  /-- "Inflate: Bottom" (`textInflateBottom`): top straight; bottom the quadratic
  `(l, ah) → (r, ah)` with control point `(hc, b)`. -/
  | inflateBottom
  /-- "Deflate: Bottom" (`textDeflateBottom`): top straight; bottom the quadratic
  `(l, b) → (r, b)` with control point `(hc, 2d - h)`, `d = a · min w h`. -/
  | deflateBottom
  /-- "Inflate: Top" (`textInflateTop`): top the quadratic `(l, ah) → (r, ah)` with control
  point `(hc, t)`; bottom straight. -/
  | inflateTop
  /-- "Deflate: Top" (`textDeflateTop`): top the quadratic `(l, t) → (r, t)` with control
  point `(hc, 2ah)`; bottom straight. -/
  | deflateTop
  /-- "Deflate: Top, Inflate: Bottom" (`textDeflateInflate`), one row of text: of its four
  guides, the first two (the row's band), the top edge and the quadratic
  `(l, 0.45h) → (r, 0.45h)` with control point `(hc, 2ah - 0.55h)`. -/
  | deflateTopInflateBottom
  /-- "Inflate: Middle, Deflate: Top and Bottom" (`textDeflateInflateDeflate`), one row: of
  its six guides, the first two, the top edge and the quadratic `(l, 0.3h) → (r, 0.3h)` with
  control point `(hc, 2ah - 0.36h)`. -/
  | inflateMiddle

/-- Where a handle is: as applied, or dragged past one end of its range. -/
inductive HandleSetting
  | default
  | min
  | max

/-- The stops of handle `i` (`0` or `1`) of a preset, `(min, default, max)` in the spec's
1/100000 units, after the spec's `pin`. A stop is `none` when no drag reaches it exactly.

Measured with real drags (`probe_handle.py`): a straight handle dragged past either end
stores that bound exactly. The Warped presets have one polar handle carrying an angle and a
radius. Dragged straight out, it keeps its default angle exactly and stores radius `100000`,
which the spec pins to `99000`. Dragged inwards it has no stop: crossing the centre flips
the angle, and short of the centre the radius is wherever the pointer lands. Warped Button
is the exception, because its spec pins every radius below `40000` up to `40000`. The four
waves have a second, sideways handle; every other preset has one handle. -/
def WarpPreset.stops : WarpPreset → ℕ → Option ℤ × ℤ × Option ℤ
  | .square, 0 => (some 30000, 50000, some 70000)
  | .stop, 0 => (some 14286, 25000, some 50000)
  | .triangleUp, 0 | .triangleDown, 0 => (some 0, 50000, some 100000)
  | .chevronUp, 0 => (some 0, 25000, some 50000)
  | .chevronDown, 0 => (some 50000, 75000, some 100000)
  | .fadeRight, 0 | .fadeLeft, 0 | .fadeUp, 0 | .fadeDown, 0 => (some 0, 33333, some 49999)
  | .slantUp, 0 => (some 0, 55555, some 71431)
  | .slantDown, 0 => (some 28569, 44445, some 100000)
  | .cascadeUp, 0 | .cascadeDown, 0 => (some 28570, 44444, some 100000)
  | .warpUp, 0 => (some 66667, 85714, some 100000)
  | .warpDown, 0 => (some 0, 14286, some 33333)
  | .ringInside, 0 | .ringOutside, 0 => (some 50000, 60000, some 99000)
  | .archWarped, 0 | .warpedCircle, 0 => (none, 50000, some 99000)
  | .archWarpedDown, 0 => (none, 25000, some 99000)
  | .warpedButton, 0 => (some 40000, 50000, some 99000)
  | .waveDown, 0 | .waveUp, 0 => (some 0, 12500, some 20000)
  | .doubleWaveDownUp, 0 | .doubleWaveUpDown, 0 => (some 0, 6250, some 12500)
  | .waveDown, 1 | .waveUp, 1 | .doubleWaveDownUp, 1 | .doubleWaveUpDown, 1 =>
      (some (-10000), 0, some 10000)
  | .inflate, 0 => (some 0, 18750, some 20000)
  | .deflate, 0 => (some 0, 18750, some 37500)
  | .curveUp, 0 | .curveDown, 0 => (some 0, 45977, some 56338)
  | .inflateBottom, 0 => (some 60000, 60000, some 100000)
  | .deflateBottom, 0 => (some 6250, 50000, some 100000)
  | .inflateTop, 0 => (some 0, 40000, some 50000)
  | .deflateTop, 0 => (some 0, 50000, some 93750)
  | .deflateTopInflateBottom, 0 => (some 5000, 35000, some 95000)
  | .inflateMiddle, 0 => (some 3000, 25000, some 47000)
  | _, _ => (none, 0, none)

/-- The value of handle `i` at a setting, as a fraction `adj / 100000`, if a drag reaches
it. -/
def WarpPreset.handleValue (k : WarpPreset) (i : ℕ) : HandleSetting → Option ℚ
  | .default => some ((k.stops i).2.1 / 100000)
  | .min => (k.stops i).1.map (fun x => (x : ℚ) / 100000)
  | .max => (k.stops i).2.2.map (fun x => (x : ℚ) / 100000)

/-- The warp of a preset with handle fractions `a` (first handle) and `b` (second; the waves
only), sending the unit square to the box `[0, w] × [0, h]` by `ruledWarp` between its two
guides. Straight guides, and polylines of two equal pieces, are written at constant speed;
the others are traced by `arcTrace`. -/
noncomputable def WarpPreset.map (k : WarpPreset) (a b w h : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  let c : ℝ × ℝ := (w / 2, h / 2)
  match k with
  | .square =>
      ruledWarp (segGuide (max 0 (w - 2 * a * w), 0) (min w (2 * (1 - a) * w), 0))
        (segGuide (max 0 ((2 * a - 1) * w), h) (min w (2 * a * w), h))
  | .stop =>
      ruledWarp (arcTrace (poly3Guide (0, a * h) (w / 3, 0) (2 * w / 3, 0) (w, a * h)))
        (arcTrace (poly3Guide (0, h - a * h) (w / 3, h) (2 * w / 3, h) (w, h - a * h)))
  | .triangleUp =>
      ruledWarp (fun u => (u * w, a * h * |2 * u - 1|)) (segGuide (0, h) (w, h))
  | .triangleDown =>
      ruledWarp (segGuide (0, 0) (w, 0)) (fun u => (u * w, h - (1 - a) * h * |2 * u - 1|))
  | .chevronUp =>
      ruledWarp (fun u => (u * w, a * h * |2 * u - 1|))
        (fun u => (u * w, h - a * h * (1 - |2 * u - 1|)))
  | .chevronDown =>
      ruledWarp (fun u => (u * w, (1 - a) * h * (1 - |2 * u - 1|)))
        (fun u => (u * w, h - (1 - a) * h * |2 * u - 1|))
  | .fadeRight => ruledWarp (segGuide (0, 0) (w, a * h)) (segGuide (0, h) (w, h - a * h))
  | .fadeLeft => ruledWarp (segGuide (0, a * h) (w, 0)) (segGuide (0, h - a * h) (w, h))
  | .fadeUp => ruledWarp (segGuide (a * w, 0) (w - a * w, 0)) (segGuide (0, h) (w, h))
  | .fadeDown => ruledWarp (segGuide (0, 0) (w, 0)) (segGuide (a * w, h) (w - a * w, h))
  | .slantUp => ruledWarp (segGuide (0, a * h) (w, 0)) (segGuide (0, h) (w, h - a * h))
  | .slantDown => ruledWarp (segGuide (0, 0) (w, h - a * h)) (segGuide (0, a * h) (w, h))
  | .cascadeUp =>
      ruledWarp (segGuide (0, (1 - a) * h / 4) (w, 0)) (segGuide (0, h) (w, a * h))
  | .cascadeDown =>
      ruledWarp (segGuide (0, 0) (w, (1 - a) * h / 4)) (segGuide (0, a * h) (w, h))
  | .warpUp =>
      let d := (1 - a) * h
      ruledWarp (arcTrace (ellArcGuide (w / 2, d) (w / 2) d Real.pi Real.pi))
        (arcTrace (ellArcGuide (w / 2, h) (w / 2) d Real.pi Real.pi))
  | .warpDown =>
      let d := a * h
      ruledWarp (arcTrace (ellArcGuide (w / 2, 0) (w / 2) d Real.pi (-Real.pi)))
        (arcTrace (ellArcGuide (w / 2, h - d) (w / 2) d Real.pi (-Real.pi)))
  | .ringInside =>
      let r := a * h / 2
      let Δ := 21599999 / 10800000 * Real.pi
      ruledWarp (arcTrace (ellArcVisualGuide (w / 2, r) (w / 2) r Real.pi Δ))
        (arcTrace (ellArcVisualGuide (w / 2, h - r) (w / 2) r Real.pi Δ))
  | .ringOutside =>
      let r := a * h / 2
      let Δ := -(21599999 / 10800000 * Real.pi)
      ruledWarp (arcTrace (ellArcVisualGuide (w / 2, r) (w / 2) r Real.pi Δ))
        (arcTrace (ellArcVisualGuide (w / 2, h - r) (w / 2) r Real.pi Δ))
  | .archWarped | .warpedButton =>
      ruledWarp (arcTrace (ellArcGuide c (w / 2) (h / 2) Real.pi Real.pi))
        (arcTrace (ellArcGuide c (a * w / 2) (a * h / 2) Real.pi Real.pi))
  | .archWarpedDown =>
      ruledWarp (arcTrace (ellArcGuide c (a * w / 2) (a * h / 2) Real.pi (-Real.pi)))
        (arcTrace (ellArcGuide c (w / 2) (h / 2) Real.pi (-Real.pi)))
  | .warpedCircle =>
      let Δ := 21599998 / 10800000 * Real.pi
      ruledWarp (arcTrace (ellArcVisualGuide c (w / 2) (h / 2) Real.pi Δ))
        (arcTrace (ellArcVisualGuide c (a * w / 2) (a * h / 2) Real.pi Δ))
  | .waveDown => waveMap false 1 a b w h
  | .waveUp => waveMap false (-1) a b w h
  | .doubleWaveDownUp => waveMap true 1 a b w h
  | .doubleWaveUpDown => waveMap true (-1) a b w h
  | .inflate =>
      let d := a * h
      ruledWarp (arcTrace (bezierParam (0, d) (w / 3, -d / 3) (2 * w / 3, -d / 3) (w, d)))
        (arcTrace (bezierParam (0, h - d) (w / 3, h + d / 3) (2 * w / 3, h + d / 3) (w, h - d)))
  | .deflate =>
      let d := a * min w h
      ruledWarp (arcTrace (bezierParam (0, 0) (w / 3, 4 * d / 3) (2 * w / 3, 4 * d / 3) (w, 0)))
        (arcTrace
          (bezierParam (0, h) (w / 3, h - 4 * d / 3) (2 * w / 3, h - 4 * d / 3) (w, h)))
  | .curveUp =>
      let d := a * h
      ruledWarp (arcTrace (bezierParam (0, d) (w / 3, 5 * d / 4) (2 * w / 3, 3 * d / 4) (w, 0)))
        (arcTrace (bezierParam (0, h - 3 * d / 8) (w / 3, h + d / 8) (2 * w / 3, h + d / 8)
          (w, h - 3 * d / 8)))
  | .curveDown =>
      let d := a * h
      ruledWarp (arcTrace (bezierParam (0, 0) (w / 3, 3 * d / 4) (2 * w / 3, 5 * d / 4) (w, d)))
        (arcTrace (bezierParam (0, h - 3 * d / 8) (w / 3, h + d / 8) (2 * w / 3, h + d / 8)
          (w, h - 3 * d / 8)))
  | .inflateBottom =>
      ruledWarp (segGuide (0, 0) (w, 0))
        (arcTrace (quadBezierParam (0, a * h) (w / 2, h) (w, a * h)))
  | .deflateBottom =>
      ruledWarp (segGuide (0, 0) (w, 0))
        (arcTrace (quadBezierParam (0, h) (w / 2, 2 * a * min w h - h) (w, h)))
  | .inflateTop =>
      ruledWarp (arcTrace (quadBezierParam (0, a * h) (w / 2, 0) (w, a * h)))
        (segGuide (0, h) (w, h))
  | .deflateTop =>
      ruledWarp (arcTrace (quadBezierParam (0, 0) (w / 2, 2 * a * h) (w, 0)))
        (segGuide (0, h) (w, h))
  | .deflateTopInflateBottom =>
      ruledWarp (segGuide (0, 0) (w, 0))
        (arcTrace (quadBezierParam (0, 9 / 20 * h) (w / 2, 2 * a * h - 11 / 20 * h)
          (w, 9 / 20 * h)))
  | .inflateMiddle =>
      ruledWarp (segGuide (0, 0) (w, 0))
        (arcTrace (quadBezierParam (0, 3 / 10 * h) (w / 2, 2 * a * h - 9 / 25 * h)
          (w, 3 / 10 * h)))

/-- The Transform setting of a text box: none, or one preset with its handles (the second
setting matters only for a preset with two handles). -/
inductive TextWarp
  | none
  | preset (k : WarpPreset) (s₁ : HandleSetting) (s₂ : HandleSetting := .default)

/-- Every handle of the warp sits at a stop a drag reaches exactly. -/
def TextWarp.Reachable : TextWarp → Prop
  | .none => True
  | .preset k s₁ s₂ => (k.handleValue 0 s₁).isSome ∧ (k.handleValue 1 s₂).isSome

/-! ### Text boxes -/

/-- A single text box: one row of glyphs, the box size in Height/Width spinner steps of
0.1 in (7.2 pt), and one warp. -/
structure TextBox where
  glyphs : List RowGlyph
  wSteps : ℕ
  hSteps : ℕ
  warp : TextWarp
  /-- Equalize Character Height, applied to the whole row (Font dialog checkbox). -/
  equalize : Bool := false

/-- The box width in points. -/
def TextBox.w (T : TextBox) : ℚ := 36 / 5 * T.wSteps

/-- The box height in points. -/
def TextBox.h (T : TextBox) : ℚ := 36 / 5 * T.hSteps

/-- The unwarped ink of a text box, with the first pen position at `0`. -/
def TextBox.ink (T : TextBox) : Set (ℝ × ℝ) :=
  rowInk T.equalize T.glyphs 0

/-- The affine map sending the bounding box of `S` onto `[0, 1]²`, the `(u, v)` frame of a
warp. A warp reads `u`, `v` off the ink box of the whole row, not the box of each glyph. -/
noncomputable def inkNormalize (S : Set (ℝ × ℝ)) (z : ℝ × ℝ) : ℝ × ℝ :=
  let x₀ := sInf (Prod.fst '' S)
  let y₀ := sInf (Prod.snd '' S)
  ((z.1 - x₀) / (sSup (Prod.fst '' S) - x₀), (z.2 - y₀) / (sSup (Prod.snd '' S) - y₀))

/-- The outline a text box draws: its ink as typed, or, when warped, its normalized ink sent
through the preset's map. -/
noncomputable def TextBox.outline (T : TextBox) : Set (ℝ × ℝ) :=
  match T.warp with
  | .none => T.ink
  | .preset k s₁ s₂ =>
      k.map ((k.handleValue 0 s₁).getD 0 : ℚ) ((k.handleValue 1 s₂).getD 0 : ℚ) T.w T.h ''
        (inkNormalize T.ink '' T.ink)

/-- The side conditions for a text box to be drawable: at least one glyph, each stored at a
size in `[1, 4000]` pt with a baseline offset the UI can set (an even percentage in
`[-100, 100]`, or the Subscript preset `-25`), character spacing within ±1000 pt, and a box
of positive size. -/
structure TextBox.WellFormed (T : TextBox) : Prop where
  glyphs_ne : T.glyphs ≠ []
  size_mem : ∀ g ∈ T.glyphs, 10 ≤ g.sizeTenths ∧ g.sizeTenths ≤ 40000
  spacing_mem : ∀ g ∈ T.glyphs, -10000 ≤ g.spacingTenths ∧ g.spacingTenths ≤ 10000
  offset_mem : ∀ g ∈ T.glyphs, (Even g.offsetPercent ∨ g.offsetPercent = -25) ∧
    -100 ≤ g.offsetPercent ∧ g.offsetPercent ≤ 100
  warp_ok : T.warp.Reachable
  w_pos : 0 < T.wSteps
  h_pos : 0 < T.hSteps

end Pconstructible
