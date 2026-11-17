import Pptc.TextBox
open Pconstructible
/-- Ink x-extent of each glyph in font units (its bounding box). -/
def inkX : Glyph → ℚ × ℚ
  | .blackCircle => (140, 1624) | .rightHalfBlackCircle => (882, 1624)
  | .leftHalfBlackCircle => (140, 882) | .fullBlock => (-10, 1931) | .lowerRightTriangle => (165, 1599)
/-- Predicted ink boxes (x0, y0, x1, y1), y down, relative to pen 0 on the baseline. -/
def boxes (eq : Bool) : List RowGlyph → ℚ → List (ℚ × ℚ × ℚ × ℚ)
  | [], _ => []
  | g :: gs, pen =>
    let s := g.size / g.glyph.unitsPerEm
    let lift : ℚ := if eq then g.glyph.inkBottom else 0
    let yT := -(g.rise + g.yScale eq * (g.glyph.inkTop - lift))
    let yB := -(g.rise + g.yScale eq * (g.glyph.inkBottom - lift))
    (pen + s * (inkX g.glyph).1, yT, pen + s * (inkX g.glyph).2, yB) :: boxes eq gs (pen + g.penStep)
def row : List RowGlyph :=
  [⟨.lowerRightTriangle, 720, 0, 0⟩, ⟨.blackCircle, 407, 0, 30⟩, ⟨.lowerRightTriangle, 200, 30, -25⟩,
   ⟨.blackCircle, 130, 15, 0⟩, ⟨.lowerRightTriangle, 1000, 30, 2⟩, ⟨.blackCircle, 100, 0, 0⟩,
   ⟨.lowerRightTriangle, 107, 0, 0⟩]
#eval boxes false row 0
#eval boxes true row 0
