import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Pptc/Scratch/OffsetZ.lean — synthesis scratch certificates (imported by nothing)

Independent [Lean] certification of the algebraic identities on which the wave-1 offset
results rest. These deliberately avoid importing `Pptc.*` (so the file is cheap to
elaborate) and restate each identity from its definition:

* `normalForm_speed`      — the identity turning the offset normal form
                            `u²(u'²+v'²) − D²v'²` into `u²(x'²+y'²) − d²v'²`;
* `offsetCross_norm`      — the rationalisation/norm step `E + w·O = 0 ⇒ E² − S·O² = 0`;
* `offsetCrossPoly_normalForm` — the normal form itself, from the perpendicular
                            displacement and the speed relation;
* `recovery_perp`         — the recovery (normal) equation `(X−x)x' + (Y−y)y' = 0`;
* `offsetOffsetE1_of_xeq` — the algebraic reduction of an offset×offset crossing to `E₁ = 0`;
* `ph_normal_unit`        — the Tschirnhausen unit-normal identity (rational-offset fact).

No `sorry`. -/

namespace PptcScratchZ

/-- The speed identity behind the offset normal form: writing
`u' = A x' + B y'`, `v' = B x' − A y'`, one has `u'² + v'² = (A²+B²)(x'²+y'²)`.
Replacing `x'²+y'²` by `u'²+v'²` in the squared crossing equation is exactly the passage
from `u²(x'²+y'²) − d²v'² = 0` to `u²(u'²+v'²) − D²v'² = 0`, `D² = d²(A²+B²)`. -/
theorem normalForm_speed (A B xp yp : ℝ) :
    (A * xp + B * yp) ^ 2 + (B * xp - A * yp) ^ 2 = (A ^ 2 + B ^ 2) * (xp ^ 2 + yp ^ 2) := by
  ring

/-- Rationalisation/norm identity. If `w² = S` and `E + w·O = 0`, then `E² − S·O² = 0`.
This is the step that clears the square root from an offset-crossing equation. -/
theorem offsetCross_norm {E O w S : ℝ} (hS : w ^ 2 = S) (h : E + w * O = 0) :
    E ^ 2 - S * O ^ 2 = 0 := by
  have key : E ^ 2 - S * O ^ 2 = (E + w * O) * (E - w * O) - O ^ 2 * (S - w ^ 2) := by ring
  rw [key, h, hS]
  ring

/-- The sign pattern `g·w + d·h = 0` rationalises to `g²S − d²h² = 0`; with
`S = x'²+y'²`, `g = A x + B y − C` and `h = B x' − A y'` this is `offsetCrossPoly`. -/
theorem offsetCross_norm_mul {g h d w S : ℝ} (hS : w ^ 2 = S) (hcross : g * w + d * h = 0) :
    g ^ 2 * S - d ^ 2 * h ^ 2 = 0 := by
  have h' : (d * h) + w * g = 0 := by
    rw [mul_comm g w] at hcross
    linarith [hcross]
  have hnorm := offsetCross_norm (E := d * h) (O := g) (w := w) (S := S) hS h'
  nlinarith [hnorm]

/-- The offset normal form, from the two geometric inputs: the perpendicular displacement
`u·w + d·v' = 0` (line equation of the offset point) and the speed relation
`(A²+B²)(x'²+y'²) = u'²+v'²`. Conclusion: `u²(u'²+v'²) − D²v'² = 0` with `D² = d²(A²+B²)`. -/
theorem offsetCrossPoly_normalForm {A B d u up vp w xp yp : ℝ}
    (hAB : (A ^ 2 + B ^ 2) * (xp ^ 2 + yp ^ 2) = up ^ 2 + vp ^ 2)
    (hw : w ^ 2 = xp ^ 2 + yp ^ 2)
    (hcross : u * w + d * vp = 0) :
    u ^ 2 * (up ^ 2 + vp ^ 2) - d ^ 2 * (A ^ 2 + B ^ 2) * vp ^ 2 = 0 := by
  have h1 : u ^ 2 * w ^ 2 = d ^ 2 * vp ^ 2 := by
    have huw : u * w = -(d * vp) := by linarith [hcross]
    calc u ^ 2 * w ^ 2 = (u * w) ^ 2 := by ring
      _ = (-(d * vp)) ^ 2 := by rw [huw]
      _ = d ^ 2 * vp ^ 2 := by ring
  calc u ^ 2 * (up ^ 2 + vp ^ 2) - d ^ 2 * (A ^ 2 + B ^ 2) * vp ^ 2
      = u ^ 2 * ((A ^ 2 + B ^ 2) * (xp ^ 2 + yp ^ 2)) - d ^ 2 * (A ^ 2 + B ^ 2) * vp ^ 2 := by
        rw [hAB]
    _ = (A ^ 2 + B ^ 2) * (u ^ 2 * (xp ^ 2 + yp ^ 2) - d ^ 2 * vp ^ 2) := by ring
    _ = (A ^ 2 + B ^ 2) * (u ^ 2 * w ^ 2 - d ^ 2 * vp ^ 2) := by rw [hw]
    _ = 0 := by rw [h1]; ring

/-- The recovery (normal) equation: the displacement from the base point to its offset lies
along the unit normal `(−y', x')/w`, hence is orthogonal to the velocity `(x', y')`. -/
theorem recovery_perp {X Y x y xp yp d w : ℝ} (hw : w ≠ 0)
    (hX : X = x - d * yp / w) (hY : Y = y + d * xp / w) :
    (X - x) * xp + (Y - y) * yp = 0 := by
  rw [hX, hY]
  field_simp
  ring

/-- Offset×offset algebraic reduction. If the two offset points have equal `x`-coordinate,
`x₁ − d₁v₁/w₁ = x₂ − d₂v₂/w₂`, then after clearing `w₁w₂` the first rationalised equation
`(x₁−x₂)w₁w₂ − d₁v₁w₂ + d₂v₂w₁ = 0` holds. This is exactly the `E₁ = 0` step of A3. -/
theorem offsetOffsetE1_of_xeq {x1 x2 v1 v2 d1 d2 w1 w2 : ℝ}
    (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0)
    (h : x1 - d1 * v1 / w1 = x2 - d2 * v2 / w2) :
    (x1 - x2) * w1 * w2 - d1 * v1 * w2 + d2 * v2 * w1 = 0 := by
  have hmul : (x1 - d1 * v1 / w1) * (w1 * w2) = (x2 - d2 * v2 / w2) * (w1 * w2) := by rw [h]
  have e1 : (x1 - d1 * v1 / w1) * (w1 * w2) = x1 * w1 * w2 - d1 * v1 * w2 := by
    field_simp
  have e2 : (x2 - d2 * v2 / w2) * (w1 * w2) = x2 * w1 * w2 - d2 * v2 * w1 := by
    field_simp
  rw [e1, e2] at hmul
  nlinarith [hmul]

/-- Tschirnhausen (PH) unit-normal identity: `(1−t²)² + (2t)² = (1+t²)²`. -/
theorem ph_normal_unit (t : ℝ) :
    (1 - t ^ 2) ^ 2 + (2 * t) ^ 2 = (1 + t ^ 2) ^ 2 := by
  ring

end PptcScratchZ
