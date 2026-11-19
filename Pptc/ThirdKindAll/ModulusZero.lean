/-
Copyright (c) 2024 Lean Community. All rights reserved.

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
import Pptc.ThirdKindAll.Standard

/-! # Pptc.ThirdKindAll.ModulusZero

The modulus-zero reduction: when `c = 0` the third-kind integrand is elementary,
`1 / (1 - n sin²θ)`. -/

namespace Pconstructible

/-! ### The elementary antiderivatives

For `b > 0` the three quadratic denominators that occur below have the antiderivatives
`arctan (√b u) / √b`, `arctan (u / √b) / √b` and `artanh (√b u) / √b`. -/

/-- `∫₀^U du / (1 + b u²) = arctan (√b U) / √b` for `b > 0`. -/
theorem integral_one_div_one_add_mul_sq {b U : ℝ} (hb : 0 < b) :
    (∫ u in (0 : ℝ)..U, 1 / (1 + b * u ^ 2))
      = (1 / Real.sqrt b) * Real.arctan (Real.sqrt b * U) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hs2 : ∀ u : ℝ, (Real.sqrt b * u) ^ 2 = b * u ^ 2 := by
    intro u
    rw [mul_pow, Real.sq_sqrt hb.le]
  have hderiv : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => (1 / Real.sqrt b) * Real.arctan (Real.sqrt b * v))
      (1 / (1 + b * u ^ 2)) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => Real.sqrt b * v) (Real.sqrt b) u := by
      simpa using (hasDerivAt_id u).const_mul (Real.sqrt b)
    have h1 := (Real.hasDerivAt_arctan (Real.sqrt b * u)).comp u hlin
    have h2 := h1.const_mul (1 / Real.sqrt b)
    refine h2.congr_deriv ?_
    rw [hs2 u]
    field_simp [hsb.ne']
  have hcont : Continuous fun u : ℝ => 1 / (1 + b * u ^ 2) := by
    refine Continuous.div continuous_const (by fun_prop) ?_
    intro u
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := U)
    (fun u _ => hderiv u) (hcont.intervalIntegrable 0 U)]
  simp [Real.arctan_zero]

/-- `∫₀^U du / (b + u²) = arctan (U / √b) / √b` for `b > 0`. -/
theorem integral_one_div_add_sq {b U : ℝ} (hb : 0 < b) :
    (∫ u in (0 : ℝ)..U, 1 / (b + u ^ 2))
      = (1 / Real.sqrt b) * Real.arctan (U / Real.sqrt b) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hderiv : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => (1 / Real.sqrt b) * Real.arctan (v / Real.sqrt b))
      (1 / (b + u ^ 2)) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => v / Real.sqrt b) (1 / Real.sqrt b) u := by
      simpa using (hasDerivAt_id u).div_const (Real.sqrt b)
    have h1 := (Real.hasDerivAt_arctan (u / Real.sqrt b)).comp u hlin
    have h2 := h1.const_mul (1 / Real.sqrt b)
    refine h2.congr_deriv ?_
    rw [div_pow, Real.sq_sqrt hb.le]
    field_simp [hsb.ne', Real.mul_self_sqrt hb.le]; rw [Real.sq_sqrt hb.le]
  have hcont : Continuous fun u : ℝ => 1 / (b + u ^ 2) := by
    refine Continuous.div continuous_const (by fun_prop) ?_
    intro u
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := U)
    (fun u _ => hderiv u) (hcont.intervalIntegrable 0 U)]
  simp [Real.arctan_zero]

/-- `∫₀^U du / (1 - b u²) = artanh (√b U) / √b` for `b > 0`, as long as `|√b U| < 1`. -/
theorem integral_one_div_one_sub_mul_sq {b U : ℝ} (hb : 0 < b)
    (hU : |Real.sqrt b * U| < 1) :
    (∫ u in (0 : ℝ)..U, 1 / (1 - b * u ^ 2))
      = (1 / Real.sqrt b) * Real.artanh (Real.sqrt b * U) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hs2 : ∀ u : ℝ, (Real.sqrt b * u) ^ 2 = b * u ^ 2 := by
    intro u
    rw [mul_pow, Real.sq_sqrt hb.le]
  have hmem : ∀ u ∈ Set.uIcc (0 : ℝ) U, |Real.sqrt b * u| < 1 := by
    intro u hu
    have hle : |u| ≤ |U| := by
      rw [Set.mem_uIcc] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos h2, abs_of_nonpos (by linarith)]
        linarith
    calc |Real.sqrt b * u| = Real.sqrt b * |u| := by
          rw [abs_mul, abs_of_nonneg hsb.le]
      _ ≤ Real.sqrt b * |U| := mul_le_mul_of_nonneg_left hle hsb.le
      _ = |Real.sqrt b * U| := by rw [abs_mul, abs_of_nonneg hsb.le]
      _ < 1 := hU
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) U, HasDerivAt
      (fun v : ℝ => (1 / Real.sqrt b) * Real.artanh (Real.sqrt b * v))
      (1 / (1 - b * u ^ 2)) u := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := abs_lt.mp (hmem u hu)
    have hlin : HasDerivAt (fun v : ℝ => Real.sqrt b * v) (Real.sqrt b) u := by
      simpa using (hasDerivAt_id u).const_mul (Real.sqrt b)
    have h1 := (hasDerivAt_artanh hu1 hu2).comp u hlin
    have h2 := h1.const_mul (1 / Real.sqrt b)
    refine h2.congr_deriv ?_
    rw [hs2 u]
    field_simp [hsb.ne']
  have hint : IntervalIntegrable (fun u : ℝ => 1 / (1 - b * u ^ 2))
      MeasureTheory.volume 0 U := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro u hu
    have h2 : (Real.sqrt b * u) ^ 2 < 1 := by
      have := abs_lt.mp (hmem u hu)
      nlinarith [this.1, this.2]
    rw [hs2 u] at h2
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := U) hderiv hint]
  simp [Real.artanh_zero]

/-! ### The `tan` form of the modulus-zero integrand

At `c = 0` the second-kind factor is `1`, and `1 - n sin²θ = cos²θ (1 + (1 - n) tan²θ)`. -/

/-- The modulus-zero integrand written in terms of `tan`. -/
theorem ellipticPiIntegrand_zero_eq_tan {n θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (hne : 1 - n * Real.sin θ ^ 2 ≠ 0) :
    ellipticPiIntegrand 0 n θ
      = (1 / Real.cos θ ^ 2) * (1 / (1 + (1 - n) * Real.tan θ ^ 2)) := by
  have hE : ellipticEIntegrand 0 θ = 1 := by simp [ellipticEIntegrand]
  have hkey : 1 + (1 - n) * Real.tan θ ^ 2 = (1 - n * Real.sin θ ^ 2) / Real.cos θ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    linear_combination Real.sin_sq_add_cos_sq θ
  rw [ellipticPiIntegrand, hE, mul_one, hkey]
  field_simp [hcos, hne]

/-! ### The three modulus-zero closed forms

`∫₀^Φ dθ / (1 - n sin²θ)` is `arctan (√(1-n) tan Φ) / √(1-n)` for `n < 1`,
`tan Φ` at `n = 1`, and `artanh (√(n-1) tan Φ) / √(n-1)` for `n > 1` while the argument
stays below `1`. -/

/-- The `n < 1` closed form: the antiderivative is `arctan (√(1-n) tan θ) / √(1-n)`. -/
theorem ellipticPiInc_zero_eq_arctan {n Φ : ℝ} (hn : n < 1) (hΦ : |Φ| < Real.pi / 2) :
    ellipticPiInc 0 n Φ
      = (1 / Real.sqrt (1 - n)) * Real.arctan (Real.sqrt (1 - n) * Real.tan Φ) := by
  have hb : 0 < 1 - n := by linarith
  have hsb : 0 < Real.sqrt (1 - n) := Real.sqrt_pos.mpr hb
  have hs2 : ∀ u : ℝ, (Real.sqrt (1 - n) * u) ^ 2 = (1 - n) * u ^ 2 := by
    intro u
    rw [mul_pow, Real.sq_sqrt hb.le]
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, HasDerivAt
      (fun v : ℝ => (1 / Real.sqrt (1 - n)) * Real.arctan (Real.sqrt (1 - n) * Real.tan v))
      (ellipticPiIntegrand 0 n θ) θ := by
    intro θ hθ
    have hc : Real.cos θ ≠ 0 := (cos_pos_of_mem_uIcc hΦ hθ).ne'
    have h1 := (Real.hasDerivAt_arctan (Real.sqrt (1 - n) * Real.tan θ)).comp θ
      ((Real.hasDerivAt_tan hc).const_mul (Real.sqrt (1 - n)))
    have h2 := h1.const_mul (1 / Real.sqrt (1 - n))
    refine h2.congr_deriv ?_
    rw [hs2 (Real.tan θ), ellipticPiIntegrand_zero_eq_tan hc (one_sub_mul_sin_sq_pos hn θ).ne']
    field_simp [hsb.ne']
  have hint : IntervalIntegrable (ellipticPiIntegrand 0 n) MeasureTheory.volume 0 Φ := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact ((by fun_prop : Continuous fun θ : ℝ => 1 - n * Real.sin θ ^ 2).continuousOn).mul
        (continuous_ellipticEIntegrand 0).continuousOn
    · intro θ _
      have hE : ellipticEIntegrand 0 θ = 1 := by simp [ellipticEIntegrand]
      rw [hE, mul_one]
      exact (one_sub_mul_sin_sq_pos hn θ).ne'
  rw [ellipticPiInc, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [Real.tan_zero, Real.arctan_zero]

/-- The `n = 1` closed form: the integrand is `1 / cos²θ`. -/
theorem ellipticPiInc_zero_one_eq {Φ : ℝ} (hΦ : |Φ| < Real.pi / 2) :
    ellipticPiInc 0 1 Φ = Real.tan Φ := by
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ,
      HasDerivAt Real.tan (ellipticPiIntegrand 0 1 θ) θ := by
    intro θ hθ
    have hc : Real.cos θ ≠ 0 := (cos_pos_of_mem_uIcc hΦ hθ).ne'
    have h : ellipticPiIntegrand 0 1 θ = 1 / Real.cos θ ^ 2 := by
      rw [ellipticPiIntegrand,
        show ellipticEIntegrand 0 θ = 1 by simp [ellipticEIntegrand], mul_one]
      congr 1
      linear_combination -Real.sin_sq_add_cos_sq θ
    rw [h]
    exact Real.hasDerivAt_tan hc
  have hint : IntervalIntegrable (ellipticPiIntegrand 0 1) MeasureTheory.volume 0 Φ := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact ((by fun_prop : Continuous fun θ : ℝ => 1 - 1 * Real.sin θ ^ 2).continuousOn).mul
        (continuous_ellipticEIntegrand 0).continuousOn
    · intro θ hθ
      have hE : ellipticEIntegrand 0 θ = 1 := by simp [ellipticEIntegrand]
      rw [hE, mul_one]
      have h : (1 : ℝ) - 1 * Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
        linear_combination -Real.sin_sq_add_cos_sq θ
      rw [h]
      exact pow_ne_zero 2 (cos_pos_of_mem_uIcc hΦ hθ).ne'
  rw [ellipticPiInc, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [Real.tan_zero]

/-- The `n > 1` closed form, valid while `1 - n sin²` has no zero on `[0, Φ]`. -/
theorem ellipticPiInc_zero_eq_artanh {n Φ : ℝ} (hn : 1 < n) (hΦ0 : 0 ≤ Φ)
    (hΦ : Φ < Real.pi / 2)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    ellipticPiInc 0 n Φ
      = (1 / Real.sqrt (n - 1)) * Real.artanh (Real.sqrt (n - 1) * Real.tan Φ) := by
  have hb : 0 < n - 1 := by linarith
  have hsb : 0 < Real.sqrt (n - 1) := Real.sqrt_pos.mpr hb
  have hs2 : ∀ u : ℝ, (Real.sqrt (n - 1) * u) ^ 2 = (n - 1) * u ^ 2 := by
    intro u
    rw [mul_pow, Real.sq_sqrt hb.le]
  have hΦabs : |Φ| < Real.pi / 2 := by rwa [abs_of_nonneg hΦ0]
  have hspos : n * Real.sin Φ ^ 2 < 1 := gtOne_sin_sq_lt_one hΦ0 hne
  -- On `[0, Φ]` the denominator stays positive, so `1 - (n-1) tan²θ > 0`.
  have hpos : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 0 < 1 - (n - 1) * Real.tan θ ^ 2 := by
    intro θ hθ
    rw [Set.uIcc_of_le hΦ0] at hθ
    obtain ⟨hθ0, hθΦ⟩ := hθ
    have hsin_le : Real.sin θ ≤ Real.sin Φ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith) hθΦ
    have hsinθ0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
    have hsinΦ0 : 0 ≤ Real.sin Φ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hΦ0 (by linarith [Real.pi_pos])
    have hssq : Real.sin θ ^ 2 ≤ Real.sin Φ ^ 2 := by nlinarith
    have hnle : n * Real.sin θ ^ 2 ≤ n * Real.sin Φ ^ 2 :=
      mul_le_mul_of_nonneg_left hssq (by linarith)
    have hlt : n * Real.sin θ ^ 2 < 1 := lt_of_le_of_lt hnle hspos
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hkey : (1 : ℝ) - (n - 1) * Real.tan θ ^ 2
        = (1 - n * Real.sin θ ^ 2) / Real.cos θ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      linear_combination Real.sin_sq_add_cos_sq θ
    rw [hkey]
    exact div_pos (by linarith) (by positivity)
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, HasDerivAt
      (fun v : ℝ => (1 / Real.sqrt (n - 1)) * Real.artanh (Real.sqrt (n - 1) * Real.tan v))
      (ellipticPiIntegrand 0 n θ) θ := by
    intro θ hθ
    have hc : Real.cos θ ≠ 0 := (cos_pos_of_mem_uIcc hΦabs hθ).ne'
    have hp := hpos θ hθ
    have hsq : (Real.sqrt (n - 1) * Real.tan θ) ^ 2 < (1 : ℝ) ^ 2 := by
      rw [hs2 (Real.tan θ), one_pow]
      linarith
    obtain ⟨h1, h2⟩ := abs_lt_of_sq_lt_sq' hsq zero_le_one
    have h3 := (hasDerivAt_artanh h1 h2).comp θ
      ((Real.hasDerivAt_tan hc).const_mul (Real.sqrt (n - 1)))
    have h4 := h3.const_mul (1 / Real.sqrt (n - 1))
    refine h4.congr_deriv ?_
    rw [hs2 (Real.tan θ), ellipticPiIntegrand_zero_eq_tan hc (hne θ hθ)]
    have hpt : (1 : ℝ) + Real.tan θ ^ 2 * (1 - n) ≠ 0 := by
      have h := (hpos θ hθ).ne'
      rwa [show (1 : ℝ) - (n - 1) * Real.tan θ ^ 2
        = 1 + Real.tan θ ^ 2 * (1 - n) by ring] at h
    field_simp [hsb.ne', hpt]
    ring
  have hint : IntervalIntegrable (ellipticPiIntegrand 0 n) MeasureTheory.volume 0 Φ := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact ((by fun_prop : Continuous fun θ : ℝ => 1 - n * Real.sin θ ^ 2).continuousOn).mul
        (continuous_ellipticEIntegrand 0).continuousOn
    · intro θ hθ
      have hE : ellipticEIntegrand 0 θ = 1 := by simp [ellipticEIntegrand]
      rw [hE, mul_one]
      exact hne θ hθ
  rw [ellipticPiInc, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [Real.tan_zero, Real.artanh_zero]

/-- For `n < 1` and `|Φ| < π/2`,
`∫₀^Φ dθ / (1 - n cos²θ) = arctan (tan Φ / √(1-n)) / √(1-n)`. -/
theorem integral_one_div_one_sub_mul_cos_sq {n Φ : ℝ} (hn : n < 1)
    (hΦ : |Φ| < Real.pi / 2) :
    (∫ θ in (0 : ℝ)..Φ, 1 / (1 - n * Real.cos θ ^ 2))
      = (1 / Real.sqrt (1 - n)) * Real.arctan (Real.tan Φ / Real.sqrt (1 - n)) := by
  have hb : 0 < 1 - n := by linarith
  have hsb : 0 < Real.sqrt (1 - n) := Real.sqrt_pos.mpr hb
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, HasDerivAt
      (fun v : ℝ => (1 / Real.sqrt (1 - n)) * Real.arctan (Real.tan v / Real.sqrt (1 - n)))
      (1 / (1 - n * Real.cos θ ^ 2)) θ := by
    intro θ hθ
    have hc : Real.cos θ ≠ 0 := (cos_pos_of_mem_uIcc hΦ hθ).ne'
    have hcos2 : 0 < Real.cos θ ^ 2 := by positivity
    have hden : (1 : ℝ) - n * Real.cos θ ^ 2 ≠ 0 := by
      have : (1 : ℝ) - n * Real.cos θ ^ 2 = Real.sin θ ^ 2 + (1 - n) * Real.cos θ ^ 2 := by
        linear_combination -Real.sin_sq_add_cos_sq θ
      rw [this]
      positivity
    have hlin : HasDerivAt (fun v : ℝ => Real.tan v / Real.sqrt (1 - n))
        ((1 / Real.cos θ ^ 2) / Real.sqrt (1 - n)) θ :=
      (Real.hasDerivAt_tan hc).div_const (Real.sqrt (1 - n))
    have h1 := (Real.hasDerivAt_arctan (Real.tan θ / Real.sqrt (1 - n))).comp θ hlin
    have h2 := h1.const_mul (1 / Real.sqrt (1 - n))
    refine h2.congr_deriv ?_
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hsb.ne', hc, hden]
    rw [Real.sq_sqrt hb.le]
    linear_combination -Real.sin_sq_add_cos_sq θ
  have hint : IntervalIntegrable (fun θ : ℝ => 1 / (1 - n * Real.cos θ ^ 2))
      MeasureTheory.volume 0 Φ := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro θ hθ
    have hc : Real.cos θ ≠ 0 := (cos_pos_of_mem_uIcc hΦ hθ).ne'
    have h : (1 : ℝ) - n * Real.cos θ ^ 2 = Real.sin θ ^ 2 + (1 - n) * Real.cos θ ^ 2 := by
      linear_combination -Real.sin_sq_add_cos_sq θ
    rw [h]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := Φ) hderiv hint]
  simp [Real.tan_zero, Real.arctan_zero]

/-- The complete integral at modulus zero: split `[0, π/2]` at `π/4` and use the two
`tan`/`cot` antiderivatives on the halves. -/
theorem ellipticPi_zero_modulus_eq {n : ℝ} (hn : n < 1) :
    ellipticPi 0 n
      = (1 / Real.sqrt (1 - n)) * Real.arctan (Real.sqrt (1 - n))
        + (1 / Real.sqrt (1 - n)) * Real.arctan (1 / Real.sqrt (1 - n)) := by
  have hcont : Continuous (ellipticPiIntegrand 0 n) :=
    continuous_ellipticPiIntegrand (c := 0) (by norm_num) hn
  have hq : |Real.pi / 4| < Real.pi / 2 := by
    rw [abs_of_pos (by positivity)]
    linarith [Real.pi_pos]
  have hfirst : (∫ θ in (0 : ℝ)..Real.pi / 4, ellipticPiIntegrand 0 n θ)
      = (1 / Real.sqrt (1 - n)) * Real.arctan (Real.sqrt (1 - n)) := by
    have h := ellipticPiInc_zero_eq_arctan (n := n) hn hq
    rw [ellipticPiInc] at h
    rwa [Real.tan_pi_div_four, mul_one] at h
  have hsecond : (∫ θ in Real.pi / 4..Real.pi / 2, ellipticPiIntegrand 0 n θ)
      = (1 / Real.sqrt (1 - n)) * Real.arctan (1 / Real.sqrt (1 - n)) := by
    have hsub := (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 4)
      (f := ellipticPiIntegrand 0 n) (Real.pi / 2)).symm
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
      show Real.pi / 2 - 0 = Real.pi / 2 by ring] at hsub
    rw [hsub]
    have hcongr : (∫ θ in (0 : ℝ)..Real.pi / 4, ellipticPiIntegrand 0 n (Real.pi / 2 - θ))
        = ∫ θ in (0 : ℝ)..Real.pi / 4, 1 / (1 - n * Real.cos θ ^ 2) := by
      refine intervalIntegral.integral_congr fun θ _ => ?_
      rw [ellipticPiIntegrand,
        show ellipticEIntegrand 0 (Real.pi / 2 - θ) = 1 by simp [ellipticEIntegrand], mul_one,
        Real.sin_pi_div_two_sub]
    rw [hcongr, integral_one_div_one_sub_mul_cos_sq hn hq, Real.tan_pi_div_four]
  rw [ellipticPi, ← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 (Real.pi / 4))
    (hcont.intervalIntegrable (Real.pi / 4) (Real.pi / 2)), hfirst, hsecond]

/-- The complete modulus-zero integral is P-constructible for `n < 1`. -/
theorem ellipticPi_zero_modulus_Pconstructible {n : ℝ} (hnP : PConstructible n)
    (hn : n < 1) : PConstructible (ellipticPi 0 n) := by
  rw [ellipticPi_zero_modulus_eq hn]
  have h1 : PConstructible (Real.sqrt (1 - n)) := by pconstructible
  have h2 : PConstructible (1 / Real.sqrt (1 - n)) := by pconstructible
  refine PConstructible.add ?_ ?_
  · exact PConstructible.mul h2 (arctan_Pconstructible h1)
  · exact PConstructible.mul h2 (arctan_Pconstructible h2)

/-- The `1 ≤ n`, `0 ≤ Φ` case of the modulus-zero theorem. -/
theorem ellipticPiInc_zero_Pconstructible_of_le_half_pi {n Φ : ℝ}
    (hnP : PConstructible n) (hΦP : PConstructible Φ) (hn : 1 ≤ n) (hΦ0 : 0 ≤ Φ)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc 0 n Φ) := by
  have hΦlt : Φ < Real.pi / 2 := one_le_phi_lt_pi_div_two hn hΦ0 hne
  have hΦabs : |Φ| < Real.pi / 2 := by rwa [abs_of_nonneg hΦ0]
  rcases lt_or_eq_of_le hn with h1 | h1
  · rw [ellipticPiInc_zero_eq_artanh h1 hΦ0 hΦlt hne]
    have hb : 0 < n - 1 := by linarith
    have hspos : n * Real.sin Φ ^ 2 < 1 := gtOne_sin_sq_lt_one hΦ0 hne
    have hcosΦ : 0 < Real.cos Φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hkey : 1 - (n - 1) * Real.tan Φ ^ 2
        = (1 - n * Real.sin Φ ^ 2) / Real.cos Φ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      linear_combination Real.sin_sq_add_cos_sq Φ
    have htan : (n - 1) * Real.tan Φ ^ 2 < 1 := by
      have hpos : 0 < (1 - n * Real.sin Φ ^ 2) / Real.cos Φ ^ 2 :=
        div_pos (by linarith) (by positivity)
      rw [← hkey] at hpos
      linarith
    have hsq : (Real.sqrt (n - 1) * Real.tan Φ) ^ 2 < (1 : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hb.le, one_pow]
      exact htan
    obtain ⟨hb1, hb2⟩ := abs_lt_of_sq_lt_sq' hsq zero_le_one
    have hsP : PConstructible (Real.sqrt (n - 1)) := by pconstructible
    have hinvP : PConstructible (1 / Real.sqrt (n - 1)) := by pconstructible
    exact PConstructible.mul hinvP
      (artanh_Pconstructible (PConstructible.mul hsP (tan_Pconstructible hΦP)) hb1 hb2)
  · subst h1
    rw [ellipticPiInc_zero_one_eq hΦabs]
    exact tan_Pconstructible hΦP

/-- **The modulus-zero reduction.** At `c = 0` the third-kind integrand is the elementary
`1 / (1 - n sin²θ)`, so the incomplete integral is P-constructible for every P-constructible
characteristic `n` and upper limit `Φ`, provided there is no pole on `[0, Φ]`. -/
theorem ellipticPiInc_zero_modulus_Pconstructible {n Φ : ℝ}
    (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc 0 n Φ) := by
  rcases lt_or_ge n 1 with hn | hn
  · -- `n < 1`: reduce to the first quarter turn, with the complete integral supplied.
    refine ellipticPiInc_Pconstructible_of_base' (c := 0) (n := n) (Φ := Φ)
      zero_Pconstructible hnP hΦP (by norm_num) hn
      (ellipticPi_zero_modulus_Pconstructible hnP hn) ?_
    intro θ hθP hθ0 hθlt
    have habs : |θ| < Real.pi / 2 := by rwa [abs_of_nonneg hθ0]
    rw [ellipticPiInc_zero_eq_arctan hn habs]
    have h1 : PConstructible (Real.sqrt (1 - n)) := by pconstructible
    have h2 : PConstructible (1 / Real.sqrt (1 - n)) := by pconstructible
    exact PConstructible.mul h2
      (arctan_Pconstructible (PConstructible.mul h1 (tan_Pconstructible hθP)))
  · -- `1 ≤ n`: the upper limit is below the quarter turn; use oddness for `Φ < 0`.
    rcases lt_or_ge Φ 0 with hneg | hnonneg
    · have hpos' : 0 < -Φ := by linarith
      have hne' : ∀ θ ∈ Set.uIcc (0 : ℝ) (-Φ), 1 - n * Real.sin θ ^ 2 ≠ 0 := by
        intro θ hθ
        have hmem : -θ ∈ Set.uIcc (0 : ℝ) Φ := by
          rw [Set.uIcc_of_ge (le_of_lt hneg)]
          rw [Set.uIcc_of_le hpos'.le] at hθ
          constructor <;> linarith [hθ.1, hθ.2]
        have := hne (-θ) hmem
        simpa [Real.sin_neg] using this
      have h := ellipticPiInc_zero_Pconstructible_of_le_half_pi hnP (neg_Pconstructible hΦP)
        hn hpos'.le hne'
      have heq : ellipticPiInc 0 n Φ = -ellipticPiInc 0 n (-Φ) := by
        simpa using (ellipticPiInc_neg 0 n (-Φ))
      rw [heq]
      exact neg_Pconstructible h
    · exact ellipticPiInc_zero_Pconstructible_of_le_half_pi hnP hΦP hn hnonneg hne

end Pconstructible
