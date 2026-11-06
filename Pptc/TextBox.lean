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
`probe_handle.py`):

* **Font size.** The Font dialog's spinner steps by 0.1 pt over `[1, 4000]`, but a glyph
  outline is drawn at the size rounded to the nearest multiple of 0.75 pt (one pixel at
  96 dpi): 72.1 to 72.26 draw the 72 pt outline, 72.4 to 72.9 the 72.75 pt one. So the
  drawn sizes are exactly the multiples `3k/4` pt, `1 ≤ k ≤ 5333`, and a size is stored
  as that `k`.
* **Character spacing.** The dialog's `By` spinner steps by 0.1 pt (Expanded or
  Condensed); the menu presets −3, −1.5, 0, 3, 6 pt lie on that grid. Its range has not been
  measured: COM accepts any value, and a UI bound has not been read off yet.
* **Layout.** Each glyph advances the pen by `advance · size / unitsPerEm + spacing`,
  rounded to a multiple of 0.75 pt, step by step (not cumulatively). All glyphs share the
  baseline. Baseline offset (2 % steps, Superscript 30 %, Subscript −25 %) is not modelled
  yet, nor is kerning (none of the glyphs below have kerning pairs).
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

/-- One character of a row: its glyph, its drawn size as a number of 0.75 pt steps, and the
character spacing after it in tenths of a point. -/
structure RowGlyph where
  glyph : Glyph
  sizeSteps : ℕ
  spacingTenths : ℤ

/-- The drawn font size in points. -/
def RowGlyph.size (g : RowGlyph) : ℚ := 3 / 4 * g.sizeSteps

/-- How far the pen moves past this glyph: advance plus spacing, rounded to 0.75 pt. -/
def RowGlyph.penStep (g : RowGlyph) : ℚ :=
  3 / 4 * round ((g.glyph.advance * g.size / g.glyph.unitsPerEm + g.spacingTenths / 10) / (3 / 4))

/-- The outline of a glyph with its pen at `pen` on the baseline `y = 0`, in points with `y`
down: font units are scaled by `size / unitsPerEm` and flipped. -/
def RowGlyph.toSet (g : RowGlyph) (pen : ℚ) : Set (ℝ × ℝ) :=
  (fun z : ℝ × ℝ =>
      (pen + g.size / g.glyph.unitsPerEm * z.1, -(g.size / g.glyph.unitsPerEm * z.2))) ''
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

/-- The side conditions for a text box to be drawable: at least one glyph, each drawn at a
size in `[0.75, 3999.75]` pt, and a box of positive size. Character spacing is not bounded
here yet (its UI range is unmeasured). -/
structure TextBox.WellFormed (T : TextBox) : Prop where
  glyphs_ne : T.glyphs ≠ []
  size_mem : ∀ g ∈ T.glyphs, 1 ≤ g.sizeSteps ∧ g.sizeSteps ≤ 5333
  w_pos : 0 < T.wSteps
  h_pos : 0 < T.hSteps

end Pconstructible
