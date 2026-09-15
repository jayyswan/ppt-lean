import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # Scratch certificates for task A4 (offset chains / rational offsets)

Nothing here is imported anywhere. These are the two elementary polynomial identities
that make the A4 rational-offset statements true; they are [Lean]-checked instead of
merely [symbolic]. No `Pptc.*` import, so this file is cheap to elaborate.
-/

namespace PptcScratchA4

-- Theorem (parabola rationalisation): with `t = (s²−1)/(4s)`, the square root
-- `√(1+4t²)` becomes rational, `√(1+4t²) = (s²+1)/(2s)`. Equivalently, clearing the
-- denominator, `(1+4t²)·(2s)² = (s²+1)²`.
-- This is exactly why the offset of `y=x²` is a rational curve.
theorem parabola_radicand_is_square (s : ℝ) (hs : s ≠ 0) :
    (1 + 4 * ((s ^ 2 - 1) / (4 * s)) ^ 2) * (2 * s) ^ 2 = (s ^ 2 + 1) ^ 2 := by
  field_simp
  ring

-- Theorem (Tschirnhausen normal is a unit vector): for the planar Pythagorean triple
-- `(1−t², 2t, 1+t²)` of the standard PH cubic, `(1−t²)² + (2t)² = (1+t²)²`. This is the
-- identity behind `speed = 1+t²`, hence behind "the offset of a PH cubic is again PH".
theorem ph_normal_unit (t : ℝ) :
    (1 - t ^ 2) ^ 2 + (2 * t) ^ 2 = (1 + t ^ 2) ^ 2 := by
  ring

-- Theorem (PH-closure for the Tschirnhausen offset): after offsetting by `d`, the squared
-- speed is the square of a rational function.  With `u = (1+t²)²` (and `|v|² = u`,
-- `κ = 2/u`), this is `(1 − d·κ)² · |v|² = ((u−2d)²/u)`, the square `((u−2d)/u)²·u`:
theorem tschirnhausen_offset_speed_square (u d : ℝ) (hu : u ≠ 0) :
    (u - 2 * d) ^ 2 / u = (1 - 2 * d / u) ^ 2 * u := by
  field_simp

end PptcScratchA4
