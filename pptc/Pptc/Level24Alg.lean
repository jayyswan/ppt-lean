/- Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0; see LICENSE. Part of the Pptc project. -/
import Pptc.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! Generated algebraic core: the two polynomial identities behind the level-24
substitution.  `r2 = √2`, `r3 = √3`; `√6` is written `r2 * r3`. -/

namespace Pconstructible
/-! ### The data of the substitution

`κ` is the parameter (the square of the modulus at which `K'/K = √(3/2)`), `A` the
leading constant, and `S, Q, T, U` the four polynomials.  Everything lives in
`ℚ(√2, √3)`; `√6` is written `√2 * √3`. -/

/-- The parameter `κ = -34 + 24√2 + 20√3 - 14√6 ≈ 0.2892852`. -/
noncomputable def lvPar : ℝ :=
  -34 + 24 * Real.sqrt 2 + 20 * Real.sqrt 3 - 14 * (Real.sqrt 2 * Real.sqrt 3)

/-- The constant `A = -(3 + 2√2)(3 + 2√3) = -(9 + 6√2 + 6√3 + 4√6)`. -/
noncomputable def lvA : ℝ :=
  -(9 + 6 * Real.sqrt 2 + 6 * Real.sqrt 3 + 4 * (Real.sqrt 2 * Real.sqrt 3))

/-- `cot (π/24) = 2 + √2 + √3 + √6`, the number that recurs in every coefficient. -/
noncomputable def lvCot : ℝ := 2 + Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3

/-- The quartic `S`, whose square carries the poles of the substitution. -/
noncomputable def lvS (v : ℝ) : ℝ :=
  v ^ 4 - lvCot * v ^ 3 - (lvCot - 1) * v ^ 2
    - (7 + 5 * Real.sqrt 2 + 4 * Real.sqrt 3 + 3 * (Real.sqrt 2 * Real.sqrt 3)) * v
    + (15 + 10 * Real.sqrt 2 + 8 * Real.sqrt 3 + 6 * (Real.sqrt 2 * Real.sqrt 3))

/-- The quadratic `Q`, whose square carries the double zeros. -/
noncomputable def lvQ (v : ℝ) : ℝ := v ^ 2 + v - lvCot

/-- The quintic `T`: `M - N = (v² + v + 1) T²`. -/
noncomputable def lvT (v : ℝ) : ℝ :=
  v ^ 5 + (2 + 2 * Real.sqrt 2 + 2 * Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3) * v ^ 4
    - (7 + 5 * Real.sqrt 2 + 4 * Real.sqrt 3 + 3 * (Real.sqrt 2 * Real.sqrt 3)) * v ^ 3
    + lvCot * v ^ 2
    + (19 + 13 * Real.sqrt 2 + 11 * Real.sqrt 3 + 8 * (Real.sqrt 2 * Real.sqrt 3)) * v
    - (15 + 10 * Real.sqrt 2 + 8 * Real.sqrt 3 + 6 * (Real.sqrt 2 * Real.sqrt 3))

/-- The sextic `U`: `M - κ N = U²`. -/
noncomputable def lvU (v : ℝ) : ℝ :=
  v ^ 6 + (1 - Real.sqrt 2 - Real.sqrt 3) * v ^ 5
    + (6 + 5 * Real.sqrt 2 + 4 * Real.sqrt 3 + 2 * (Real.sqrt 2 * Real.sqrt 3)) * v ^ 4
    - (7 + 6 * Real.sqrt 2 + 5 * Real.sqrt 3 + 3 * (Real.sqrt 2 * Real.sqrt 3)) * v ^ 2
    - (10 + 5 * Real.sqrt 2 + 4 * Real.sqrt 3 + 4 * (Real.sqrt 2 * Real.sqrt 3)) * v
    + (15 + 10 * Real.sqrt 2 + 8 * Real.sqrt 3 + 6 * (Real.sqrt 2 * Real.sqrt 3))

/-- The denominator of the substitution, `M = (v⁴ - v² + 1) S²`. -/
noncomputable def lvM (v : ℝ) : ℝ := (v ^ 4 - v ^ 2 + 1) * lvS v ^ 2

/-- The numerator of the substitution, `N = A v (v⁴ - 1)(v² - v + 1) Q²`. -/
noncomputable def lvN (v : ℝ) : ℝ := lvA * (v ^ 5 - v) * (v ^ 2 - v + 1) * lvQ v ^ 2

/-! #### Numerical bounds on the two square roots -/

theorem lv_sq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
theorem lv_sq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
theorem lv_2_lb : (1.414 : ℝ) < Real.sqrt 2 := by nlinarith [lv_sq2, Real.sqrt_nonneg 2]
theorem lv_2_ub : Real.sqrt 2 < 1.41422 := by nlinarith [lv_sq2, Real.sqrt_nonneg 2]
theorem lv_3_lb : (1.732 : ℝ) < Real.sqrt 3 := by nlinarith [lv_sq3, Real.sqrt_nonneg 3]
theorem lv_3_ub : Real.sqrt 3 < 1.73206 := by nlinarith [lv_sq3, Real.sqrt_nonneg 3]


/-! #### The two branch identities

These are the whole algebraic content of the substitution.  Written out, each is a
polynomial identity in `v`, `√2` and `√3` that reduces to `0` modulo `√2² = 2` and
`√3² = 3`; the `linear_combination` cofactors below are the quotients. -/

set_option maxHeartbeats 1000000 in
-- Theorem: the first branch identity, `M - N = (v² + v + 1) T²`.
theorem lvM_sub_lvN (v : ℝ) : lvM v - lvN v = (v ^ 2 + v + 1) * lvT v ^ 2 := by
  simp only [lvM, lvN, lvS, lvQ, lvT, lvA, lvCot]
  linear_combination
    (27 * v + -33 * v * Real.sqrt 3 ^ 2 + -14 * v * Real.sqrt 3 ^ 3 + -6 * v * Real.sqrt 2
      + -16 * v * Real.sqrt 2 * Real.sqrt 3 + -14 * v * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -4 * v * Real.sqrt 2 * Real.sqrt 3 ^ 3 + -3 * v ^ 10 + -2 * v ^ 10 * Real.sqrt 3
      + -39 * v ^ 2 + -6 * v ^ 2 * Real.sqrt 3 + 34 * v ^ 2 * Real.sqrt 3 ^ 2
      + 14 * v ^ 2 * Real.sqrt 3 ^ 3 + 6 * v ^ 2 * Real.sqrt 2
      + 16 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 + 14 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 4 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 ^ 3 + 42 * v ^ 3 + 6 * v ^ 3 * Real.sqrt 3
      + -35 * v ^ 3 * Real.sqrt 3 ^ 2 + -14 * v ^ 3 * Real.sqrt 3 ^ 3 + -6 * v ^ 3 * Real.sqrt 2
      + -16 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 + -14 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -4 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 ^ 3 + 2 * v ^ 4 * Real.sqrt 3
      + 1 * v ^ 4 * Real.sqrt 3 ^ 2 + -42 * v ^ 5 + -8 * v ^ 5 * Real.sqrt 3
      + 34 * v ^ 5 * Real.sqrt 3 ^ 2 + 14 * v ^ 5 * Real.sqrt 3 ^ 3 + 6 * v ^ 5 * Real.sqrt 2
      + 16 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 + 14 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 4 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 ^ 3 + 48 * v ^ 6 + 8 * v ^ 6 * Real.sqrt 3
      + -36 * v ^ 6 * Real.sqrt 3 ^ 2 + -14 * v ^ 6 * Real.sqrt 3 ^ 3 + -6 * v ^ 6 * Real.sqrt 2
      + -16 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 + -14 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -4 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 ^ 3 + -30 * v ^ 7 + 34 * v ^ 7 * Real.sqrt 3 ^ 2
      + 14 * v ^ 7 * Real.sqrt 3 ^ 3 + 6 * v ^ 7 * Real.sqrt 2
      + 16 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 + 14 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 4 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 ^ 3 + -3 * v ^ 8 + -2 * v ^ 8 * Real.sqrt 3
      + 6 * v ^ 9 + 2 * v ^ 9 * Real.sqrt 3 + -1 * v ^ 9 * Real.sqrt 3 ^ 2) * lv_sq2
    + (-51 * v + -34 * v * Real.sqrt 3 + -36 * v * Real.sqrt 2
      + -24 * v * Real.sqrt 2 * Real.sqrt 3 + -3 * v ^ 10 + -2 * v ^ 10 * Real.sqrt 2
      + 56 * v ^ 2 + 34 * v ^ 2 * Real.sqrt 3 + 40 * v ^ 2 * Real.sqrt 2
      + 24 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 + -62 * v ^ 3 + -34 * v ^ 3 * Real.sqrt 3
      + -44 * v ^ 3 * Real.sqrt 2 + -24 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 + 3 * v ^ 4
      + 2 * v ^ 4 * Real.sqrt 2 + 56 * v ^ 5 + 34 * v ^ 5 * Real.sqrt 3
      + 40 * v ^ 5 * Real.sqrt 2 + 24 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 + -62 * v ^ 6
      + -34 * v ^ 6 * Real.sqrt 3 + -44 * v ^ 6 * Real.sqrt 2
      + -24 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 + 51 * v ^ 7 + 34 * v ^ 7 * Real.sqrt 3
      + 36 * v ^ 7 * Real.sqrt 2 + 24 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3) * lv_sq3

set_option maxHeartbeats 1000000 in
-- Theorem: the second branch identity, `M - κ N = U²`.
theorem lvM_sub_par_lvN (v : ℝ) : lvM v - lvPar * lvN v = lvU v ^ 2 := by
  simp only [lvM, lvN, lvS, lvQ, lvU, lvA, lvCot, lvPar]
  linear_combination
    (-606 * v + -648 * v * Real.sqrt 3 + 34 * v * Real.sqrt 3 ^ 2 + 216 * v * Real.sqrt 3 ^ 3
      + 56 * v * Real.sqrt 3 ^ 4 + -588 * v * Real.sqrt 2 + -938 * v * Real.sqrt 2 * Real.sqrt 3
      + -148 * v * Real.sqrt 2 * Real.sqrt 3 ^ 2 + 318 * v * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + 116 * v * Real.sqrt 2 * Real.sqrt 3 ^ 4 + -144 * v * Real.sqrt 2 ^ 2
      + -300 * v * Real.sqrt 2 ^ 2 * Real.sqrt 3 + -112 * v * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + 100 * v * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3 + 56 * v * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4
      + 144 * v ^ 10 + 14 * v ^ 10 * Real.sqrt 3 + -55 * v ^ 10 * Real.sqrt 3 ^ 2 + 144 * v ^ 11
      + 12 * v ^ 11 * Real.sqrt 3 + -56 * v ^ 11 * Real.sqrt 3 ^ 2 + 1206 * v ^ 2
      + 1002 * v ^ 2 * Real.sqrt 3 + -245 * v ^ 2 * Real.sqrt 3 ^ 2
      + -336 * v ^ 2 * Real.sqrt 3 ^ 3 + -56 * v ^ 2 * Real.sqrt 3 ^ 4
      + 876 * v ^ 2 * Real.sqrt 2 + 1250 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3
      + 60 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -430 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + -116 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + 144 * v ^ 2 * Real.sqrt 2 ^ 2
      + 300 * v ^ 2 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + 112 * v ^ 2 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + -100 * v ^ 2 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + -56 * v ^ 2 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + -720 * v ^ 3
      + -654 * v ^ 3 * Real.sqrt 3 + 84 * v ^ 3 * Real.sqrt 3 ^ 2
      + 216 * v ^ 3 * Real.sqrt 3 ^ 3 + 56 * v ^ 3 * Real.sqrt 3 ^ 4
      + -588 * v ^ 3 * Real.sqrt 2 + -938 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3
      + -148 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 318 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + 116 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + -144 * v ^ 3 * Real.sqrt 2 ^ 2
      + -300 * v ^ 3 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + -112 * v ^ 3 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + 100 * v ^ 3 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + 56 * v ^ 3 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + -174 * v ^ 4 + -8 * v ^ 4 * Real.sqrt 3
      + 69 * v ^ 4 * Real.sqrt 3 ^ 2 + 1188 * v ^ 5 + 1004 * v ^ 5 * Real.sqrt 3
      + -238 * v ^ 5 * Real.sqrt 3 ^ 2 + -336 * v ^ 5 * Real.sqrt 3 ^ 3
      + -56 * v ^ 5 * Real.sqrt 3 ^ 4 + 876 * v ^ 5 * Real.sqrt 2
      + 1250 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 + 60 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -430 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + -116 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + 144 * v ^ 5 * Real.sqrt 2 ^ 2
      + 300 * v ^ 5 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + 112 * v ^ 5 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + -100 * v ^ 5 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + -56 * v ^ 5 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + -1305 * v ^ 6
      + -1016 * v ^ 6 * Real.sqrt 3 + 285 * v ^ 6 * Real.sqrt 3 ^ 2
      + 336 * v ^ 6 * Real.sqrt 3 ^ 3 + 56 * v ^ 6 * Real.sqrt 3 ^ 4
      + -876 * v ^ 6 * Real.sqrt 2 + -1250 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3
      + -60 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 430 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + 116 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + -144 * v ^ 6 * Real.sqrt 2 ^ 2
      + -300 * v ^ 6 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + -112 * v ^ 6 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + 100 * v ^ 6 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + 56 * v ^ 6 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + 582 * v ^ 7 + 642 * v ^ 7 * Real.sqrt 3
      + -30 * v ^ 7 * Real.sqrt 3 ^ 2 + -216 * v ^ 7 * Real.sqrt 3 ^ 3
      + -56 * v ^ 7 * Real.sqrt 3 ^ 4 + 588 * v ^ 7 * Real.sqrt 2
      + 938 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 + 148 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -318 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + -116 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + 144 * v ^ 7 * Real.sqrt 2 ^ 2
      + 300 * v ^ 7 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + 112 * v ^ 7 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + -100 * v ^ 7 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + -56 * v ^ 7 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + 129 * v ^ 8 + 8 * v ^ 8 * Real.sqrt 3
      + -54 * v ^ 8 * Real.sqrt 3 ^ 2 + -588 * v ^ 9 + -356 * v ^ 9 * Real.sqrt 3
      + 206 * v ^ 9 * Real.sqrt 3 ^ 2 + 120 * v ^ 9 * Real.sqrt 3 ^ 3
      + -288 * v ^ 9 * Real.sqrt 2 + -312 * v ^ 9 * Real.sqrt 2 * Real.sqrt 3
      + 88 * v ^ 9 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 112 * v ^ 9 * Real.sqrt 2 * Real.sqrt 3 ^ 3) * lv_sq2
    + (-34 * v + -24 * v * Real.sqrt 3 + -8 * v * Real.sqrt 3 ^ 2 + -20 * v * Real.sqrt 2
      + -22 * v * Real.sqrt 2 * Real.sqrt 3 + -4 * v * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 10 * v ^ 10 + -2 * v ^ 10 * Real.sqrt 2 + 8 * v ^ 11 + -4 * v ^ 11 * Real.sqrt 2
      + 44 * v ^ 2 + 24 * v ^ 2 * Real.sqrt 3 + 8 * v ^ 2 * Real.sqrt 3 ^ 2
      + 16 * v ^ 2 * Real.sqrt 2 + 30 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3
      + 4 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + -38 * v ^ 3 + -24 * v ^ 3 * Real.sqrt 3
      + -8 * v ^ 3 * Real.sqrt 3 ^ 2 + -14 * v ^ 3 * Real.sqrt 2
      + -22 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 + -4 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 2 * v ^ 4 + 10 * v ^ 4 * Real.sqrt 2 + 52 * v ^ 5 + 24 * v ^ 5 * Real.sqrt 3
      + 8 * v ^ 5 * Real.sqrt 3 ^ 2 + 22 * v ^ 5 * Real.sqrt 2
      + 30 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 + 4 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -60 * v ^ 6 + -24 * v ^ 6 * Real.sqrt 3 + -8 * v ^ 6 * Real.sqrt 3 ^ 2
      + -18 * v ^ 6 * Real.sqrt 2 + -30 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3
      + -4 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + 22 * v ^ 7 + 24 * v ^ 7 * Real.sqrt 3
      + 8 * v ^ 7 * Real.sqrt 3 ^ 2 + 12 * v ^ 7 * Real.sqrt 2
      + 22 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 + 4 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 4 * v ^ 8 + -6 * v ^ 8 * Real.sqrt 2 + -10 * v ^ 9 + 4 * v ^ 9 * Real.sqrt 2
      + -8 * v ^ 9 * Real.sqrt 2 * Real.sqrt 3) * lv_sq3
/-! #### Positivity on the open unit interval -/

theorem lvPar_pos : 0 < lvPar := by
  simp only [lvPar]; nlinarith [lv_2_lb, lv_2_ub, lv_3_lb, lv_3_ub, Real.sqrt_nonneg 2]

theorem lvPar_lt_one : lvPar < 1 := by
  simp only [lvPar]; nlinarith [lv_2_lb, lv_2_ub, lv_3_lb, lv_3_ub, Real.sqrt_nonneg 2]

theorem lvA_neg : lvA < 0 := by
  simp only [lvA]; nlinarith [lv_2_lb, lv_3_lb, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]

theorem lvCot_bounds : (7.59 : ℝ) < lvCot ∧ lvCot < 7.6 := by
  constructor <;> · simp only [lvCot]; nlinarith [lv_2_lb, lv_2_ub, lv_3_lb, lv_3_ub]

theorem lv_quartic_pos (v : ℝ) : 0 < v ^ 4 - v ^ 2 + 1 := by nlinarith [sq_nonneg (v ^ 2 - 1)]

theorem lv_C3_pos (v : ℝ) : 0 < v ^ 2 + v + 1 := by nlinarith [sq_nonneg (2 * v + 1)]

theorem lv_V2_pos (v : ℝ) : 0 < v ^ 2 - v + 1 := by nlinarith [sq_nonneg (2 * v - 1)]

theorem lvQ_neg {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : lvQ v < 0 := by
  have := lvCot_bounds.1
  simp only [lvQ]; nlinarith

theorem lv_6_lb : (2.449 : ℝ) < Real.sqrt 2 * Real.sqrt 3 := by
  nlinarith [lv_2_lb, lv_3_lb, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]

theorem lv_6_ub : Real.sqrt 2 * Real.sqrt 3 < 2.4495 := by
  have h : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [h]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]

theorem lvS_pos {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 < lvS v := by
  have hc := lvCot_bounds
  have hp3 : v ^ 3 ≤ 1 := pow_le_one₀ hv0 hv1
  have hp2 : v ^ 2 ≤ 1 := pow_le_one₀ hv0 hv1
  have hp4 : (0 : ℝ) ≤ v ^ 4 := by positivity
  have e1 : lvCot * v ^ 3 ≤ lvCot := by nlinarith [hc.1]
  have e2 : (lvCot - 1) * v ^ 2 ≤ lvCot - 1 := by nlinarith [hc.1]
  have e3 : (7 + 5 * Real.sqrt 2 + 4 * Real.sqrt 3 + 3 * (Real.sqrt 2 * Real.sqrt 3)) * v
      ≤ 7 + 5 * Real.sqrt 2 + 4 * Real.sqrt 3 + 3 * (Real.sqrt 2 * Real.sqrt 3) := by
    nlinarith [lv_2_lb, lv_3_lb, lv_6_lb]
  simp only [lvS]
  nlinarith [lv_2_lb, lv_2_ub, lv_3_lb, lv_3_ub, hc.1, hc.2, lv_6_lb, lv_6_ub]

theorem lv_v13_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : 0 < v - v ^ 13 := by
  have h : v ^ 13 < v ^ 1 := pow_lt_pow_right_of_lt_one₀ hv0 hv1 (by norm_num)
  simpa using h

theorem lvM_pos {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 < lvM v :=
  mul_pos (lv_quartic_pos v) (pow_pos (lvS_pos hv0 hv1) 2)

theorem lvN_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : 0 < lvN v := by
  have hQ := lvQ_neg hv0.le hv1.le
  have hq : 0 < lvQ v ^ 2 := by nlinarith
  have h5 : v ^ 5 - v < 0 := by
    have := pow_lt_pow_right_of_lt_one₀ hv0 hv1 (by norm_num : 1 < 5)
    simpa using this
  have hA : 0 < lvA * (v ^ 5 - v) := mul_pos_of_neg_of_neg lvA_neg h5
  have hrw : lvN v = lvA * (v ^ 5 - v) * ((v ^ 2 - v + 1) * lvQ v ^ 2) := by
    simp only [lvN]; ring
  rw [hrw]
  exact mul_pos hA (mul_pos (lv_V2_pos v) hq)


/-! ### The amplitude

`cos` of the amplitude is `-T √G / W`, where `G = (v² + v + 1)(v⁴ - v² + 1)` and
`W = S (v⁴ - v² + 1)`.  It runs from `1` at `v = 0` to `-1` at `v = 1`, so the amplitude
itself runs from `0` to `π` and the substitution needs no splitting: the whole of
`(0, 1)` maps onto a half period in one piece.  Writing it with `arccos` rather than
`arcsin` is what buys that. -/

/-- `D = v⁴ - v² + 1`, the cyclotomic factor `Φ₁₂` carrying the simple poles. -/
noncomputable def lvD (v : ℝ) : ℝ := v ^ 4 - v ^ 2 + 1

/-- `G = (v² + v + 1) D = v⁶ + v⁵ - v³ + v + 1`. -/
noncomputable def lvG (v : ℝ) : ℝ := (v ^ 2 + v + 1) * lvD v

/-- `W = S D`, the denominator of `cos`. -/
noncomputable def lvW (v : ℝ) : ℝ := lvS v * lvD v

/-- The shape of the differential, `1 + (√3 + √6) v² + (3 + √6) v³ + cot(π/24) v⁵`. -/
noncomputable def lvShape (v : ℝ) : ℝ :=
  1 + (Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3) * v ^ 2
    + (3 + Real.sqrt 2 * Real.sqrt 3) * v ^ 3 + lvCot * v ^ 5

/-- The derivative of `S`. -/
noncomputable def lvSd (v : ℝ) : ℝ :=
  4 * v ^ 3 - 3 * lvCot * v ^ 2 - 2 * (lvCot - 1) * v
    - (7 + 5 * Real.sqrt 2 + 4 * Real.sqrt 3 + 3 * (Real.sqrt 2 * Real.sqrt 3))

/-- The derivative of `T`. -/
noncomputable def lvTd (v : ℝ) : ℝ :=
  5 * v ^ 4 + 4 * (2 + 2 * Real.sqrt 2 + 2 * Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3) * v ^ 3
    - 3 * (7 + 5 * Real.sqrt 2 + 4 * Real.sqrt 3 + 3 * (Real.sqrt 2 * Real.sqrt 3)) * v ^ 2
    + 2 * lvCot * v
    + (19 + 13 * Real.sqrt 2 + 11 * Real.sqrt 3 + 8 * (Real.sqrt 2 * Real.sqrt 3))

/-- The derivative of `D`. -/
noncomputable def lvDd (v : ℝ) : ℝ := 4 * v ^ 3 - 2 * v

/-- The derivative of `G`. -/
noncomputable def lvGd (v : ℝ) : ℝ := 6 * v ^ 5 + 5 * v ^ 4 - 3 * v ^ 2 + 1

/-- The derivative of `W`. -/
noncomputable def lvWd (v : ℝ) : ℝ := lvSd v * lvD v + lvS v * lvDd v

theorem hasDerivAt_lvD (v : ℝ) : HasDerivAt lvD (lvDd v) v := by
  unfold lvD lvDd
  refine (((hasDerivAt_pow 4 v).sub (hasDerivAt_pow 2 v)).add_const 1).congr_deriv ?_
  push_cast; ring

theorem hasDerivAt_lvS (v : ℝ) : HasDerivAt lvS (lvSd v) v := by
  unfold lvS lvSd
  refine ((((hasDerivAt_pow 4 v).sub ((hasDerivAt_pow 3 v).const_mul lvCot)).sub
    ((hasDerivAt_pow 2 v).const_mul (lvCot - 1))).sub ((hasDerivAt_id v).const_mul
      (7 + 5 * Real.sqrt 2 + 4 * Real.sqrt 3 + 3 * (Real.sqrt 2 * Real.sqrt 3)))).add_const
      (15 + 10 * Real.sqrt 2 + 8 * Real.sqrt 3 + 6 * (Real.sqrt 2 * Real.sqrt 3))
      |>.congr_deriv ?_
  push_cast; ring

theorem hasDerivAt_lvT (v : ℝ) : HasDerivAt lvT (lvTd v) v := by
  unfold lvT lvTd
  refine (((((hasDerivAt_pow 5 v).add ((hasDerivAt_pow 4 v).const_mul
      (2 + 2 * Real.sqrt 2 + 2 * Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3))).sub
      ((hasDerivAt_pow 3 v).const_mul
        (7 + 5 * Real.sqrt 2 + 4 * Real.sqrt 3 + 3 * (Real.sqrt 2 * Real.sqrt 3)))).add
      ((hasDerivAt_pow 2 v).const_mul lvCot)).add ((hasDerivAt_id v).const_mul
      (19 + 13 * Real.sqrt 2 + 11 * Real.sqrt 3 + 8 * (Real.sqrt 2 * Real.sqrt 3)))).sub_const
      (15 + 10 * Real.sqrt 2 + 8 * Real.sqrt 3 + 6 * (Real.sqrt 2 * Real.sqrt 3))
      |>.congr_deriv ?_
  push_cast; ring

theorem hasDerivAt_lvG (v : ℝ) : HasDerivAt lvG (lvGd v) v := by
  unfold lvG lvGd lvD
  refine ((((hasDerivAt_pow 2 v).add (hasDerivAt_id v)).add_const 1).mul
    (((hasDerivAt_pow 4 v).sub (hasDerivAt_pow 2 v)).add_const 1)).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, id_eq]
  push_cast; ring

theorem hasDerivAt_lvW (v : ℝ) : HasDerivAt lvW (lvWd v) v :=
  (hasDerivAt_lvS v).mul (hasDerivAt_lvD v)

theorem lvD_pos (v : ℝ) : 0 < lvD v := lv_quartic_pos v

theorem lvG_pos (v : ℝ) : 0 < lvG v := mul_pos (lv_C3_pos v) (lvD_pos v)

theorem lvW_pos {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 < lvW v :=
  mul_pos (lvS_pos hv0 hv1) (lvD_pos v)


set_option maxHeartbeats 2000000 in
-- Theorem: the differential identity.  Multiplied by `cot(π/24)` to clear the one
-- denominator, this says that the numerator of `(cos amp)'` is `-A` times
-- `Q U D` against the shape of the differential.  It is what makes the substitution
-- collapse the elliptic integrand onto `P(v)/√(v - v¹³)`.
theorem lv_identity_three (v : ℝ) :
    lvCot * (2 * lvT v * lvG v * lvWd v
        - (2 * lvTd v * lvG v + lvT v * lvGd v) * lvW v)
      = -lvA * (lvQ v * lvU v * lvD v * lvShape v) := by
  simp only [lvT, lvG, lvW, lvWd, lvTd, lvGd, lvQ, lvU, lvD, lvDd, lvShape, lvA, lvS, lvSd,
    lvCot]
  linear_combination
    (45 * v + 72 * v * Real.sqrt 3 + 33 * v * Real.sqrt 3 ^ 2 + 4 * v * Real.sqrt 3 ^ 3
      + 30 * v * Real.sqrt 2 + 52 * v * Real.sqrt 2 * Real.sqrt 3
      + 24 * v * Real.sqrt 2 * Real.sqrt 3 ^ 2 + 2 * v * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + -165 * v ^ 10 + -105 * v ^ 10 * Real.sqrt 3 + -30 * v ^ 10 * Real.sqrt 3 ^ 2
      + -103 * v ^ 10 * Real.sqrt 3 ^ 3 + -52 * v ^ 10 * Real.sqrt 3 ^ 4
      + -180 * v ^ 10 * Real.sqrt 2 + -254 * v ^ 10 * Real.sqrt 2 * Real.sqrt 3
      + -186 * v ^ 10 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -106 * v ^ 10 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + -28 * v ^ 10 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + -36 * v ^ 10 * Real.sqrt 2 ^ 2
      + -84 * v ^ 10 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + -76 * v ^ 10 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + -36 * v ^ 10 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + -8 * v ^ 10 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + 873 * v ^ 11
      + 1049 * v ^ 11 * Real.sqrt 3 + -206 * v ^ 11 * Real.sqrt 3 ^ 2
      + -631 * v ^ 11 * Real.sqrt 3 ^ 3 + -192 * v ^ 11 * Real.sqrt 3 ^ 4
      + -57 * v ^ 11 * Real.sqrt 2 + -263 * v ^ 11 * Real.sqrt 2 * Real.sqrt 3
      + -447 * v ^ 11 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -309 * v ^ 11 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + -74 * v ^ 11 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + -66 * v ^ 11 * Real.sqrt 2 ^ 2
      + -182 * v ^ 11 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + -182 * v ^ 11 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + -78 * v ^ 11 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + -12 * v ^ 11 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + 84 * v ^ 12
      + 89 * v ^ 12 * Real.sqrt 3 + -11 * v ^ 12 * Real.sqrt 3 ^ 2
      + -15 * v ^ 12 * Real.sqrt 3 ^ 3 + 4 * v ^ 12 * Real.sqrt 3 ^ 4
      + 48 * v ^ 12 * Real.sqrt 2 + 43 * v ^ 12 * Real.sqrt 2 * Real.sqrt 3
      + 11 * v ^ 12 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + 2 * v ^ 12 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + 6 * v ^ 12 * Real.sqrt 2 ^ 2 + 10 * v ^ 12 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + 4 * v ^ 12 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2 + -402 * v ^ 13
      + -512 * v ^ 13 * Real.sqrt 3 + 113 * v ^ 13 * Real.sqrt 3 ^ 2
      + 338 * v ^ 13 * Real.sqrt 3 ^ 3 + 104 * v ^ 13 * Real.sqrt 3 ^ 4
      + 33 * v ^ 13 * Real.sqrt 2 + 153 * v ^ 13 * Real.sqrt 2 * Real.sqrt 3
      + 257 * v ^ 13 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 179 * v ^ 13 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + 44 * v ^ 13 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + 30 * v ^ 13 * Real.sqrt 2 ^ 2
      + 92 * v ^ 13 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + 102 * v ^ 13 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + 48 * v ^ 13 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + 8 * v ^ 13 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + 66 * v ^ 14 + 67 * v ^ 14 * Real.sqrt 3
      + -21 * v ^ 14 * Real.sqrt 3 ^ 2 + -45 * v ^ 14 * Real.sqrt 3 ^ 3
      + -14 * v ^ 14 * Real.sqrt 3 ^ 4 + -18 * v ^ 14 * Real.sqrt 2
      + -36 * v ^ 14 * Real.sqrt 2 * Real.sqrt 3 + -34 * v ^ 14 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -18 * v ^ 14 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + -4 * v ^ 14 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + -6 * v ^ 14 * Real.sqrt 2 ^ 2
      + -16 * v ^ 14 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + -14 * v ^ 14 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + -4 * v ^ 14 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3 + -15 * v ^ 15
      + -10 * v ^ 15 * Real.sqrt 3 + 9 * v ^ 15 * Real.sqrt 3 ^ 2 + 6 * v ^ 15 * Real.sqrt 3 ^ 3
      + -6 * v ^ 15 * Real.sqrt 2 + -5 * v ^ 15 * Real.sqrt 2 * Real.sqrt 3
      + 4 * v ^ 15 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + 3 * v ^ 15 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + 2 * v ^ 16 * Real.sqrt 3 + 8 * v ^ 16 * Real.sqrt 3 ^ 2 + 4 * v ^ 16 * Real.sqrt 3 ^ 3
      + 6 * v ^ 16 * Real.sqrt 2 + 10 * v ^ 16 * Real.sqrt 2 * Real.sqrt 3
      + 4 * v ^ 16 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + -1344 * v ^ 2 + -1713 * v ^ 2 * Real.sqrt 3
      + 110 * v ^ 2 * Real.sqrt 3 ^ 2 + 819 * v ^ 2 * Real.sqrt 3 ^ 3
      + 256 * v ^ 2 * Real.sqrt 3 ^ 4 + -267 * v ^ 2 * Real.sqrt 2
      + -224 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 + 339 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 420 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + 116 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + 60 * v ^ 2 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + 136 * v ^ 2 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + 100 * v ^ 2 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + 24 * v ^ 2 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + 144 * v ^ 3 + 121 * v ^ 3 * Real.sqrt 3
      + 17 * v ^ 3 * Real.sqrt 3 ^ 2 + 17 * v ^ 3 * Real.sqrt 3 ^ 3
      + 12 * v ^ 3 * Real.sqrt 3 ^ 4 + 60 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3
      + 135 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + 93 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + 20 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + 30 * v ^ 3 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + 62 * v ^ 3 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + 40 * v ^ 3 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + 8 * v ^ 3 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + 2760 * v ^ 4
      + 3400 * v ^ 4 * Real.sqrt 3 + -277 * v ^ 4 * Real.sqrt 3 ^ 2
      + -1616 * v ^ 4 * Real.sqrt 3 ^ 3 + -494 * v ^ 4 * Real.sqrt 3 ^ 4
      + 609 * v ^ 4 * Real.sqrt 2 + 495 * v ^ 4 * Real.sqrt 2 * Real.sqrt 3
      + -719 * v ^ 4 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -869 * v ^ 4 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + -234 * v ^ 4 * Real.sqrt 2 * Real.sqrt 3 ^ 4
      + -126 * v ^ 4 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + -288 * v ^ 4 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + -214 * v ^ 4 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + -52 * v ^ 4 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + -1254 * v ^ 5
      + -1258 * v ^ 5 * Real.sqrt 3 + 313 * v ^ 5 * Real.sqrt 3 ^ 2
      + 622 * v ^ 5 * Real.sqrt 3 ^ 3 + 152 * v ^ 5 * Real.sqrt 3 ^ 4
      + -42 * v ^ 5 * Real.sqrt 2 + 82 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3
      + 298 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 218 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 ^ 3 + 46 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 ^ 4
      + 60 * v ^ 5 * Real.sqrt 2 ^ 2 + 130 * v ^ 5 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + 96 * v ^ 5 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + 30 * v ^ 5 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + 4 * v ^ 5 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + -2841 * v ^ 6
      + -3418 * v ^ 6 * Real.sqrt 3 + 228 * v ^ 6 * Real.sqrt 3 ^ 2
      + 1494 * v ^ 6 * Real.sqrt 3 ^ 3 + 446 * v ^ 6 * Real.sqrt 3 ^ 4
      + -747 * v ^ 6 * Real.sqrt 2 + -716 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3
      + 540 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 765 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + 206 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + -30 * v ^ 6 * Real.sqrt 2 ^ 2
      + 52 * v ^ 6 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + 216 * v ^ 6 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + 178 * v ^ 6 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + 44 * v ^ 6 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + 1770 * v ^ 7
      + 1867 * v ^ 7 * Real.sqrt 3 + -373 * v ^ 7 * Real.sqrt 3 ^ 2
      + -911 * v ^ 7 * Real.sqrt 3 ^ 3 + -240 * v ^ 7 * Real.sqrt 3 ^ 4
      + 48 * v ^ 7 * Real.sqrt 2 + -140 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3
      + -464 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -346 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + -76 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + -96 * v ^ 7 * Real.sqrt 2 ^ 2
      + -220 * v ^ 7 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + -176 * v ^ 7 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + -60 * v ^ 7 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + -8 * v ^ 7 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + 1647 * v ^ 8
      + 1861 * v ^ 8 * Real.sqrt 3 + -150 * v ^ 8 * Real.sqrt 3 ^ 2
      + -735 * v ^ 8 * Real.sqrt 3 ^ 3 + -200 * v ^ 8 * Real.sqrt 3 ^ 4
      + 510 * v ^ 8 * Real.sqrt 2 + 499 * v ^ 8 * Real.sqrt 2 * Real.sqrt 3
      + -224 * v ^ 8 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -361 * v ^ 8 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + -94 * v ^ 8 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + 30 * v ^ 8 * Real.sqrt 2 ^ 2
      + 2 * v ^ 8 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + -90 * v ^ 8 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + -82 * v ^ 8 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + -20 * v ^ 8 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4 + -1998 * v ^ 9
      + -2196 * v ^ 9 * Real.sqrt 3 + 545 * v ^ 9 * Real.sqrt 3 ^ 2
      + 1276 * v ^ 9 * Real.sqrt 3 ^ 3 + 356 * v ^ 9 * Real.sqrt 3 ^ 4 + 9 * v ^ 9 * Real.sqrt 2
      + 400 * v ^ 9 * Real.sqrt 2 * Real.sqrt 3 + 884 * v ^ 9 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 623 * v ^ 9 * Real.sqrt 2 * Real.sqrt 3 ^ 3
      + 140 * v ^ 9 * Real.sqrt 2 * Real.sqrt 3 ^ 4 + 126 * v ^ 9 * Real.sqrt 2 ^ 2
      + 342 * v ^ 9 * Real.sqrt 2 ^ 2 * Real.sqrt 3
      + 340 * v ^ 9 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2
      + 148 * v ^ 9 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 3
      + 24 * v ^ 9 * Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 4) * lv_sq2
    + (15 * v + 8 * v * Real.sqrt 3 + 10 * v * Real.sqrt 2 + 6 * v * Real.sqrt 2 * Real.sqrt 3
      + 13 * v ^ 10 + -153 * v ^ 10 * Real.sqrt 3 + -110 * v ^ 10 * Real.sqrt 3 ^ 2
      + 8 * v ^ 10 * Real.sqrt 2 + -108 * v ^ 10 * Real.sqrt 2 * Real.sqrt 3
      + -78 * v ^ 10 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + -1097 * v ^ 11
      + -1401 * v ^ 11 * Real.sqrt 3 + -444 * v ^ 11 * Real.sqrt 3 ^ 2
      + -777 * v ^ 11 * Real.sqrt 2 + -991 * v ^ 11 * Real.sqrt 2 * Real.sqrt 3
      + -314 * v ^ 11 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + -81 * v ^ 12
      + -33 * v ^ 12 * Real.sqrt 3 + 14 * v ^ 12 * Real.sqrt 3 ^ 2 + -56 * v ^ 12 * Real.sqrt 2
      + -24 * v ^ 12 * Real.sqrt 2 * Real.sqrt 3 + 10 * v ^ 12 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 546 * v ^ 13 + 715 * v ^ 13 * Real.sqrt 3 + 232 * v ^ 13 * Real.sqrt 3 ^ 2
      + 386 * v ^ 13 * Real.sqrt 2 + 506 * v ^ 13 * Real.sqrt 2 * Real.sqrt 3
      + 164 * v ^ 13 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + -92 * v ^ 14
      + -113 * v ^ 14 * Real.sqrt 3 + -34 * v ^ 14 * Real.sqrt 3 ^ 2
      + -66 * v ^ 14 * Real.sqrt 2 + -80 * v ^ 14 * Real.sqrt 2 * Real.sqrt 3
      + -24 * v ^ 14 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + 15 * v ^ 15 + 10 * v ^ 15 * Real.sqrt 3
      + 10 * v ^ 15 * Real.sqrt 2 + 7 * v ^ 15 * Real.sqrt 2 * Real.sqrt 3 + 20 * v ^ 16
      + 14 * v ^ 16 * Real.sqrt 3 + 14 * v ^ 16 * Real.sqrt 2
      + 10 * v ^ 16 * Real.sqrt 2 * Real.sqrt 3 + 1291 * v ^ 2 + 1704 * v ^ 2 * Real.sqrt 3
      + 560 * v ^ 2 * Real.sqrt 3 ^ 2 + 913 * v ^ 2 * Real.sqrt 2
      + 1205 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 + 396 * v ^ 2 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -210 * v ^ 3 + -137 * v ^ 3 * Real.sqrt 3 + -148 * v ^ 3 * Real.sqrt 2
      + -97 * v ^ 3 * Real.sqrt 2 * Real.sqrt 3 + -2483 * v ^ 4 + -3263 * v ^ 4 * Real.sqrt 3
      + -1066 * v ^ 4 * Real.sqrt 3 ^ 2 + -1758 * v ^ 4 * Real.sqrt 2
      + -2306 * v ^ 4 * Real.sqrt 2 * Real.sqrt 3 + -754 * v ^ 4 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + 1423 * v ^ 5 + 1519 * v ^ 5 * Real.sqrt 3 + 376 * v ^ 5 * Real.sqrt 3 ^ 2
      + 1007 * v ^ 5 * Real.sqrt 2 + 1073 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3
      + 266 * v ^ 5 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + 2395 * v ^ 6 + 3063 * v ^ 6 * Real.sqrt 3
      + 970 * v ^ 6 * Real.sqrt 3 ^ 2 + 1696 * v ^ 6 * Real.sqrt 2
      + 2164 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 + 686 * v ^ 6 * Real.sqrt 2 * Real.sqrt 3 ^ 2
      + -1959 * v ^ 7 + -2197 * v ^ 7 * Real.sqrt 3 + -588 * v ^ 7 * Real.sqrt 3 ^ 2
      + -1388 * v ^ 7 * Real.sqrt 2 + -1552 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3
      + -416 * v ^ 7 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + -1277 * v ^ 8
      + -1505 * v ^ 8 * Real.sqrt 3 + -430 * v ^ 8 * Real.sqrt 3 ^ 2
      + -905 * v ^ 8 * Real.sqrt 2 + -1063 * v ^ 8 * Real.sqrt 2 * Real.sqrt 3
      + -304 * v ^ 8 * Real.sqrt 2 * Real.sqrt 3 ^ 2 + 2325 * v ^ 9 + 2793 * v ^ 9 * Real.sqrt 3
      + 820 * v ^ 9 * Real.sqrt 3 ^ 2 + 1646 * v ^ 9 * Real.sqrt 2
      + 1974 * v ^ 9 * Real.sqrt 2 * Real.sqrt 3
      + 580 * v ^ 9 * Real.sqrt 2 * Real.sqrt 3 ^ 2) * lv_sq3

end Pconstructible
