import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# OffsetB3 scratch

Private scratch file for task B3 (beyond-algebraic offsets). Imported by nothing.
Pure algebraic reductions used in `NOTES-offset-B3.md`.
-/

namespace OffsetB3

-- Theorem: crossing the offset of the sine curve by `d` with the horizontal line `Y = 0`
-- gives the exact algebraic relation `cos⁴x = 1 - d²`, i.e. `x = arccos ((1-d²)^{1/4})`.
--
-- The offset point is `(x - d cos x / w, sin x + d / w)` with `w = √(1 + cos²x)`, so the
-- crossing with `Y = 0` is `sin x + d / w = 0`.  Squaring and using `sin² + cos² = 1`
-- yields `(1 - cos²x)(1 + cos²x) = d²`.
theorem cos_pow_four_of_offset_sine_eq_zero (x d : ℝ)
    (h : Real.sin x + d / Real.sqrt (1 + Real.cos x ^ 2) = 0) :
    Real.cos x ^ 4 = 1 - d ^ 2 := by
  have hc : 0 < 1 + Real.cos x ^ 2 := by positivity
  have hs : Real.sin x = -(d / Real.sqrt (1 + Real.cos x ^ 2)) := by linarith
  have hsq : Real.sin x ^ 2 = d ^ 2 / (1 + Real.cos x ^ 2) := by
    rw [hs]
    rw [show (-(d / Real.sqrt (1 + Real.cos x ^ 2))) ^ 2
          = d ^ 2 / (Real.sqrt (1 + Real.cos x ^ 2)) ^ 2 by ring]
    rw [Real.sq_sqrt hc.le]
  have h1 : 1 - Real.cos x ^ 2 = d ^ 2 / (1 + Real.cos x ^ 2) := by
    have hsincos := Real.sin_sq_add_cos_sq x
    linarith
  have h2 : (1 - Real.cos x ^ 2) * (1 + Real.cos x ^ 2) = d ^ 2 := by
    rw [h1, div_mul_cancel₀ _ (ne_of_gt hc)]
  nlinarith [h2]

end OffsetB3
