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
* **Character spacing.** The dialog's `By` spinner steps by 0.1 pt (Expanded or
  Condensed); the menu presets −3, −1.5, 0, 3, 6 pt lie on that grid. Its range has not been
  measured: COM accepts any value, and a UI bound has not been read off yet.
* **Layout.** Each glyph advances the pen by `advance · size / unitsPerEm + spacing`,
  rounded to a multiple of 0.75 pt, step by step (not cumulatively), with `size` the drawn
  size. Glyphs sit on a common baseline unless offset. Kerning is not modelled (none of the
  glyphs below have kerning pairs), nor is Equalize Character Height.
* **Box size.** The Height and Width spinners step by 0.1 in = 7.2 pt. The warp fills the
  whole shape box: the text insets do not enter.
* **Handle.** A drag stores whatever value the pointer lands on, which is not a clear
  choice, except when it is dragged past an end of the range: then the stored value is the
  `pin` bound exactly (`val 100000` for Triangle, `val 0` for Triangle Inverted). So the
  handle takes its spec default or one of its two bounds.

## The warp

Measured in `notes/warp/TEXT-WARP-THEORY.md` §2 and checked against this file's definitions
by `probe_textbox_model.py`: the ink box of the whole row is normalized to `[0, 1]²`, `u`
across and `v` top to bottom, and sent by the ruled map `(1 - v) · T(u) + v · B(u)` between
the preset's two guide paths, each traced at constant speed, into the box `[0, w] × [0, h]`.
Coordinates are the spec's, `y` pointing down. PowerPoint then refits the image with fresh
Béziers, within about 0.5 pt rms on a 4 in box; the exact image is the idealization.

One anomaly is unexplained: at a few box sizes (6 in × 3 in among them) PowerPoint traces
the top guide off by up to 6 pt, while neighbouring sizes fit. A construction should name its
box size and have it checked by `probe_textbox_model.py`.

Only the Triangle pair is listed so far: their guides are polylines with equal pieces, so
constant speed has a closed form. Other straight-guide presets follow the same pattern. The
curved-guide families (Can, Ring, Wave, the Pours) need their arc-length maps first.
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
idealized only where its outline shows clear intent: these three are an ellipse and its two
halves, with centre and semi-axes read off the integer bounding box of the font's own
outline. -/
inductive Glyph
  /-- ● U+25CF BLACK CIRCLE: bounding box `(140, -25)–(1624, 1458)`, within 0.15 %. -/
  | blackCircle
  /-- ◗ U+25D7 RIGHT HALF BLACK CIRCLE: the right half, flat side on `x = 882`, within
  0.07 %. -/
  | rightHalfBlackCircle
  /-- ◖ U+25D6 LEFT HALF BLACK CIRCLE: the left half, flat side on `x = 882`, within
  0.06 %. -/
  | leftHalfBlackCircle

/-- Units per em of the font the glyphs come from. -/
def Glyph.unitsPerEm (_ : Glyph) : ℚ := 2048

/-- The advance width of a glyph, in font units (`hmtx`). -/
def Glyph.advance : Glyph → ℚ
  | .blackCircle => 1764
  | .rightHalfBlackCircle => 1764
  | .leftHalfBlackCircle => 1764

/-- The idealized outline of a glyph, in font units with `y` up. All three share the centre
`(882, 1433/2)` and semi-axes `742` and `1483/2`. -/
def Glyph.pieces : Glyph → List GlyphPiece
  | .blackCircle => [.ellArc (882, 1433 / 2) 742 (1483 / 2) (140, -25) (1624, 1458)]
  | .rightHalfBlackCircle =>
      [.ellArc (882, 1433 / 2) 742 (1483 / 2) (882, -25) (1624, 1458), .seg (882, -25) (882, 1458)]
  | .leftHalfBlackCircle =>
      [.ellArc (882, 1433 / 2) 742 (1483 / 2) (140, -25) (882, 1458), .seg (882, -25) (882, 1458)]

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

/-- How far the pen moves past this glyph: advance at the drawn size plus spacing, snapped
to 0.75 pt. -/
def RowGlyph.penStep (g : RowGlyph) : ℚ :=
  snap (g.glyph.advance * g.size / g.glyph.unitsPerEm + g.spacingTenths / 10)

/-- The outline of a glyph with its pen at `pen` on the baseline `y = 0`, in points with `y`
down: font units are scaled by `size / unitsPerEm`, flipped, and raised by `rise`. -/
def RowGlyph.toSet (g : RowGlyph) (pen : ℚ) : Set (ℝ × ℝ) :=
  (fun z : ℝ × ℝ =>
      (pen + g.size / g.glyph.unitsPerEm * z.1,
        -(g.rise + g.size / g.glyph.unitsPerEm * z.2))) ''
    ⋃ piece ∈ g.glyph.pieces, piece.toSet

/-- The ink of a row whose first pen position is `pen`. -/
def rowInk : List RowGlyph → ℚ → Set (ℝ × ℝ)
  | [], _ => ∅
  | g :: gs, pen => g.toSet pen ∪ rowInk gs (pen + g.penStep)

/-! ### Warps -/

/-- The ruled warp between a top guide `T` and a bottom guide `B`: the point `(u, v)` of the
unit square goes to `(1 - v) · T(u) + v · B(u)`. Every bending Transform preset has this
form, with `T` and `B` traced at constant speed (`TEXT-WARP-THEORY.md` §2). -/
def ruledWarp (T B : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - p.2) * (T p.1).1 + p.2 * (B p.1).1, (1 - p.2) * (T p.1).2 + p.2 * (B p.1).2)

/-- The Transform presets modelled so far. -/
inductive WarpPreset
  /-- `textTriangle`: top guide `(l, y) → (hc, t) → (r, y)`, bottom `(l, b) → (r, b)`. -/
  | triangle
  /-- `textTriangleInverted`: top `(l, t) → (r, t)`, bottom `(l, y) → (hc, b) → (r, y)`. -/
  | triangleInverted

/-- The handle range of a preset, from the `pin` guide of its spec, in 1/100000 units.
Both Triangles have `a = pin 0 adj 100000`. -/
def WarpPreset.adjRange : WarpPreset → ℤ × ℤ
  | .triangle => (0, 100000)
  | .triangleInverted => (0, 100000)

/-- The handle value a preset is applied with (`avLst` of its spec). -/
def WarpPreset.adjDefault : WarpPreset → ℤ
  | .triangle => 50000
  | .triangleInverted => 50000

/-- The warp of a preset with handle fraction `a = adj / 100000`, sending the unit square to
the box `[0, w] × [0, h]`. Both guides of a Triangle are polylines whose two pieces have
equal length, so the constant-speed tracing is the piecewise-linear `|2u - 1|`. -/
noncomputable def WarpPreset.map (k : WarpPreset) (a w h : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  match k with
  | .triangle =>
      ruledWarp (fun u => (u * w, a * h * |2 * u - 1|)) (fun u => (u * w, h))
  | .triangleInverted =>
      ruledWarp (fun u => (u * w, 0)) (fun u => (u * w, h - (1 - a) * h * |2 * u - 1|))

/-- Where the handle is: as applied, or dragged past one end of its range. -/
inductive HandleSetting
  | default
  | min
  | max

/-- The stored handle value of a setting. -/
def WarpPreset.adj (k : WarpPreset) : HandleSetting → ℤ
  | .default => k.adjDefault
  | .min => k.adjRange.1
  | .max => k.adjRange.2

/-- The Transform setting of a text box: none, or one preset with its handle. -/
inductive TextWarp
  | none
  | preset (k : WarpPreset) (s : HandleSetting)

/-! ### Text boxes -/

/-- A single text box: one row of glyphs, the box size in Height/Width spinner steps of
0.1 in (7.2 pt), and one warp. -/
structure TextBox where
  glyphs : List RowGlyph
  wSteps : ℕ
  hSteps : ℕ
  warp : TextWarp

/-- The box width in points. -/
def TextBox.w (T : TextBox) : ℚ := 36 / 5 * T.wSteps

/-- The box height in points. -/
def TextBox.h (T : TextBox) : ℚ := 36 / 5 * T.hSteps

/-- The unwarped ink of a text box, with the first pen position at `0`. -/
def TextBox.ink (T : TextBox) : Set (ℝ × ℝ) :=
  rowInk T.glyphs 0

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
  | .preset k s => k.map ((k.adj s : ℝ) / 100000) T.w T.h '' (inkNormalize T.ink '' T.ink)

/-- The side conditions for a text box to be drawable: at least one glyph, each stored at a
size in `[1, 4000]` pt with a baseline offset the UI can set (an even percentage in
`[-100, 100]`, or the Subscript preset `-25`), and a box of positive size. Character spacing
is not bounded here yet (its UI range is unmeasured). -/
structure TextBox.WellFormed (T : TextBox) : Prop where
  glyphs_ne : T.glyphs ≠ []
  size_mem : ∀ g ∈ T.glyphs, 10 ≤ g.sizeTenths ∧ g.sizeTenths ≤ 40000
  offset_mem : ∀ g ∈ T.glyphs, (Even g.offsetPercent ∨ g.offsetPercent = -25) ∧
    -100 ≤ g.offsetPercent ∧ g.offsetPercent ≤ 100
  w_pos : 0 < T.wSteps
  h_pos : 0 < T.hSteps

end Pconstructible
