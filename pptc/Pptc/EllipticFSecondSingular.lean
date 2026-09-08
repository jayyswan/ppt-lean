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

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
import Pptc.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # The second singular value of `K`

`K(k₂) = √(√2 + 1) · Γ(1/8) Γ(3/8) / (2 ^ (13/4) √π)` at `k₂ = √2 - 1`.
-/

open MeasureTheory Set

namespace Pconstructible

/-! ### The modulus `k₂ = √2 - 1` and its reciprocal -/

/-- The second singular modulus `k₂ = √2 - 1`. -/
noncomputable def singMod : ℝ := Real.sqrt 2 - 1

/-- Its reciprocal `k₂⁻¹ = √2 + 1`. -/
noncomputable def singModInv : ℝ := Real.sqrt 2 + 1

theorem sq_sqrt_two : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  nlinarith [sq_sqrt_two, Real.sqrt_nonneg 2]

theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [sq_sqrt_two, Real.sqrt_nonneg 2]

theorem singMod_pos : 0 < singMod := by
  have := one_lt_sqrt_two
  simp only [singMod]; linarith

theorem singMod_lt_one : singMod < 1 := by
  have := sqrt_two_lt_two
  simp only [singMod]; linarith

theorem singModInv_pos : 0 < singModInv := by
  have := Real.sqrt_nonneg 2
  simp only [singModInv]; linarith

theorem singMod_mul_singModInv : singMod * singModInv = 1 := by
  simp only [singMod, singModInv]
  nlinarith [sq_sqrt_two]

theorem one_sub_singMod_sq : 1 - singMod ^ 2 = 2 * singMod := by
  simp only [singMod]
  nlinarith [sq_sqrt_two]

/-! ### The substitution -/

theorem sqrt_one_add_sq_pos (v : ℝ) : 0 < Real.sqrt (1 + v ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

theorem sq_sqrt_one_add_sq (v : ℝ) : Real.sqrt (1 + v ^ 2) ^ 2 = 1 + v ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `sin` of the amplitude attached to the parameter `v`. -/
noncomputable def singSin (v : ℝ) : ℝ := singModInv * (singMod - v) / Real.sqrt (1 + v ^ 2)

theorem singSin_sq (v : ℝ) :
    singSin v ^ 2 = singModInv ^ 2 * (singMod - v) ^ 2 / (1 + v ^ 2) := by
  rw [singSin, div_pow, sq_sqrt_one_add_sq, mul_pow]

theorem one_sub_singSin_sq (v : ℝ) :
    1 - singSin v ^ 2 = 2 * singModInv * v * (1 - v) / (1 + v ^ 2) := by
  have h : (0 : ℝ) < 1 + v ^ 2 := by positivity
  rw [singSin_sq]
  simp only [singMod, singModInv]
  field_simp
  linear_combination (-(Real.sqrt 2) ^ 2 + 2 * v * (Real.sqrt 2 + 1) - v ^ 2) * sq_sqrt_two

theorem one_sub_singPar_mul_singSin_sq (v : ℝ) :
    1 - singMod ^ 2 * singSin v ^ 2 = 2 * singMod * (1 + v) / (1 + v ^ 2) := by
  have h : (0 : ℝ) < 1 + v ^ 2 := by positivity
  rw [singSin_sq]
  simp only [singMod, singModInv]
  field_simp
  linear_combination (-((Real.sqrt 2 ^ 2 - 2) ^ 2
      + (Real.sqrt 2 ^ 2 - 2) * (3 - 2 * Real.sqrt 2 - 2 * (Real.sqrt 2 - 1) * v + v ^ 2)
      + 2 * (Real.sqrt 2 ^ 2 - 2)
      + 2 * (3 - 2 * Real.sqrt 2 - 2 * (Real.sqrt 2 - 1) * v + v ^ 2) + 1)) * sq_sqrt_two

theorem singSin_sq_lt_one {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : singSin v ^ 2 < 1 := by
  have h := one_sub_singSin_sq v
  have hpos : 0 < 2 * singModInv * v * (1 - v) / (1 + v ^ 2) :=
    div_pos (mul_pos (mul_pos (by linarith [singModInv_pos]) hv0) (by linarith)) (by positivity)
  linarith

theorem singSin_lt_one {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : singSin v < 1 := by
  nlinarith [singSin_sq_lt_one hv0 hv1]

theorem neg_one_lt_singSin {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : -1 < singSin v := by
  nlinarith [singSin_sq_lt_one hv0 hv1]

theorem singSin_pos {v : ℝ} (hv : v < singMod) : 0 < singSin v :=
  div_pos (mul_pos singModInv_pos (by linarith)) (sqrt_one_add_sq_pos v)

theorem singSin_zero : singSin 0 = 1 := by
  have h : Real.sqrt (1 + (0 : ℝ) ^ 2) = 1 := by norm_num
  rw [singSin, h, sub_zero, div_one, mul_comm, singMod_mul_singModInv]

theorem singSin_singMod : singSin singMod = 0 := by
  rw [singSin, sub_self, mul_zero, zero_div]

theorem continuous_singSin : Continuous singSin := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  exact fun v => (sqrt_one_add_sq_pos v).ne'

theorem hasDerivAt_singSin (v : ℝ) :
    HasDerivAt singSin (-(singModInv + v) / ((1 + v ^ 2) * Real.sqrt (1 + v ^ 2))) v := by
  have hpos : (0 : ℝ) < 1 + v ^ 2 := by positivity
  have hne := (sqrt_one_add_sq_pos v).ne'
  have hs := sq_sqrt_one_add_sq v
  have hsq : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * v) v := by
    simpa using (hasDerivAt_pow 2 v).const_add 1
  have hroot : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
      (1 / (2 * Real.sqrt (1 + v ^ 2)) * (2 * v)) v :=
    (Real.hasDerivAt_sqrt hpos.ne').comp v hsq
  have hnum : HasDerivAt (fun x : ℝ => singModInv * (singMod - x)) (singModInv * (-1)) v := by
    simpa using ((hasDerivAt_id v).const_sub singMod).const_mul singModInv
  have hd := hnum.div hroot hne
  refine hd.congr_deriv ?_
  field_simp
  rw [hs]
  linear_combination (-v - v ^ 3) * singMod_mul_singModInv

/-- The amplitude attached to the parameter `v`: the angle whose sine is `singSin v`. -/
noncomputable def singAmp (v : ℝ) : ℝ := Real.arcsin (singSin v)

theorem sin_singAmp {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : Real.sin (singAmp v) = singSin v :=
  Real.sin_arcsin (neg_one_lt_singSin hv0 hv1).le (singSin_lt_one hv0 hv1).le

theorem singAmp_zero : singAmp 0 = Real.pi / 2 := by
  rw [singAmp, singSin_zero, Real.arcsin_one]

theorem singAmp_singMod : singAmp singMod = 0 := by
  rw [singAmp, singSin_singMod, Real.arcsin_zero]

theorem continuous_singAmp : Continuous singAmp :=
  Real.continuous_arcsin.comp continuous_singSin

theorem sqrt_singSin_compl {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    Real.sqrt (1 - singSin v ^ 2)
      = Real.sqrt (2 * singModInv * v * (1 - v)) / Real.sqrt (1 + v ^ 2) := by
  have hnn : (0 : ℝ) <= 2 * singModInv * v * (1 - v) :=
    le_of_lt (mul_pos (mul_pos (by linarith [singModInv_pos]) hv0) (by linarith))
  rw [one_sub_singSin_sq, Real.sqrt_div hnn]

theorem sqrt_singSin_compl_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    0 < Real.sqrt (2 * singModInv * v * (1 - v)) :=
  Real.sqrt_pos.mpr
    (mul_pos (mul_pos (by linarith [singModInv_pos]) hv0) (by linarith))

theorem hasDerivAt_singAmp {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt singAmp
      (-(singModInv + v) / ((1 + v ^ 2) * Real.sqrt (2 * singModInv * v * (1 - v)))) v := by
  have h1 : singSin v ≠ -1 := ne_of_gt (neg_one_lt_singSin hv0 hv1)
  have h2 : singSin v ≠ 1 := ne_of_lt (singSin_lt_one hv0 hv1)
  have hc : HasDerivAt singAmp
      (1 / Real.sqrt (1 - singSin v ^ 2)
        * (-(singModInv + v) / ((1 + v ^ 2) * Real.sqrt (1 + v ^ 2)))) v :=
    (Real.hasDerivAt_arcsin h1 h2).comp v (hasDerivAt_singSin v)
  refine hc.congr_deriv ?_
  rw [sqrt_singSin_compl hv0 hv1]
  have hA := (sqrt_one_add_sq_pos v).ne'
  have hB := (sqrt_singSin_compl_pos hv0 hv1).ne'
  field_simp

theorem singAmp_image : singAmp '' (Ioo 0 singMod) = Ioo 0 (Real.pi / 2) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hv1 : v < 1 := lt_trans hv.2 singMod_lt_one
    exact ⟨Real.arcsin_pos.mpr (singSin_pos hv.2),
      Real.arcsin_lt_pi_div_two.mpr (singSin_lt_one hv.1 hv1)⟩
  · have h := intermediate_value_Ioo' singMod_pos.le continuous_singAmp.continuousOn
    simpa [singAmp_zero, singAmp_singMod] using h

theorem singAmp_injOn : InjOn singAmp (Ioo 0 singMod) := by
  intro x hx y hy hxy
  have hx1 : x < 1 := lt_trans hx.2 singMod_lt_one
  have hy1 : y < 1 := lt_trans hy.2 singMod_lt_one
  have hs : singSin x = singSin y := by
    rw [← sin_singAmp hx.1 hx1, ← sin_singAmp hy.1 hy1, hxy]
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hkey : 2 * singMod * (1 + x) / (1 + x ^ 2) = 2 * singMod * (1 + y) / (1 + y ^ 2) := by
    rw [← one_sub_singPar_mul_singSin_sq, ← one_sub_singPar_mul_singSin_sq, hs]
  rw [div_eq_div_iff h1.ne' h2.ne'] at hkey
  have hfac : 2 * singMod * ((y - x) * (x + y + x * y - 1)) = 0 := by linear_combination hkey
  have hA : (2 : ℝ) * singMod ≠ 0 := by
    have := singMod_pos; positivity
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h hA
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exfalso
    have hAsq : singMod ^ 2 = 1 - 2 * singMod := by linarith [one_sub_singMod_sq]
    nlinarith [hx.1, hx.2, hy.1, hy.2, singMod_pos]

/-! ### The collapse of the integrand -/

/-- The `v`-side integrand `(k₂⁻¹ + v) / (2 √(v - v⁵))`. -/
noncomputable def quinticIntegrand (v : ℝ) : ℝ := (singModInv + v) / (2 * Real.sqrt (v - v ^ 5))

/-- The derivative of the amplitude, as a function. -/
noncomputable def singAmpDeriv (v : ℝ) : ℝ :=
  -(singModInv + v) / ((1 + v ^ 2) * Real.sqrt (2 * singModInv * v * (1 - v)))

theorem eq_of_sq_eq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, h]

theorem quintic_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : 0 < v - v ^ 5 := by
  have h4 : v ^ 4 < 1 := pow_lt_one₀ hv0.le hv1 (by norm_num)
  nlinarith

theorem sqrt_singPar_compl_pos {v : ℝ} (hv0 : 0 < v) : 0 < Real.sqrt (2 * singMod * (1 + v)) :=
  Real.sqrt_pos.mpr (mul_pos (by linarith [singMod_pos]) (by linarith))

theorem singSin_compl_arg_nonneg {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    (0 : ℝ) ≤ 2 * singModInv * v * (1 - v) :=
  le_of_lt (mul_pos (mul_pos (by linarith [singModInv_pos]) hv0) (by linarith))

theorem singPar_compl_arg_nonneg {v : ℝ} (hv0 : 0 < v) : (0 : ℝ) ≤ 2 * singMod * (1 + v) :=
  le_of_lt (mul_pos (by linarith [singMod_pos]) (by linarith))

/-- The three square roots coming out of the substitution multiply to `2 √(v - v⁵)`: this is
where `k₂ · k₂⁻¹ = 1` does its work. -/
theorem sqrt_triple {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    Real.sqrt (2 * singModInv * v * (1 - v)) * Real.sqrt (2 * singMod * (1 + v))
        * Real.sqrt (1 + v ^ 2)
      = 2 * Real.sqrt (v - v ^ 5) := by
  refine eq_of_sq_eq_of_nonneg (by positivity) (by positivity) ?_
  have e1 : Real.sqrt (2 * singModInv * v * (1 - v)) ^ 2 = 2 * singModInv * v * (1 - v) :=
    Real.sq_sqrt (singSin_compl_arg_nonneg hv0 hv1)
  have e2 : Real.sqrt (2 * singMod * (1 + v)) ^ 2 = 2 * singMod * (1 + v) :=
    Real.sq_sqrt (singPar_compl_arg_nonneg hv0)
  have e3 : Real.sqrt (1 + v ^ 2) ^ 2 = 1 + v ^ 2 := sq_sqrt_one_add_sq v
  have e4 : Real.sqrt (v - v ^ 5) ^ 2 = v - v ^ 5 := Real.sq_sqrt (quintic_pos hv0 hv1).le
  rw [mul_pow, mul_pow, e1, e2, e3, mul_pow, e4]
  linear_combination (4 * v * (1 - v) * (1 + v) * (1 + v ^ 2)) * singMod_mul_singModInv

theorem singAmp_integrand_eq {v : ℝ} (hv : v ∈ Ioo 0 singMod) :
    |singAmpDeriv v| • ellipticFIntegrand (singMod ^ 2) (singAmp v) = quinticIntegrand v := by
  obtain ⟨hv0, hvA⟩ := hv
  have hv1 : v < 1 := lt_trans hvA singMod_lt_one
  have hP := sqrt_singSin_compl_pos hv0 hv1
  have hQ := sqrt_singPar_compl_pos hv0
  have hR := sqrt_one_add_sq_pos v
  have hS : 0 < Real.sqrt (v - v ^ 5) := Real.sqrt_pos.mpr (quintic_pos hv0 hv1)
  have hBv : 0 < singModInv + v := by linarith [singModInv_pos]
  have hsq : (0 : ℝ) < 1 + v ^ 2 := by positivity
  have habs : |singAmpDeriv v|
      = (singModInv + v) / ((1 + v ^ 2) * Real.sqrt (2 * singModInv * v * (1 - v))) := by
    rw [singAmpDeriv, abs_div, abs_neg, abs_of_pos hBv, abs_of_pos (mul_pos hsq hP)]
  have hE : ellipticFIntegrand (singMod ^ 2) (singAmp v)
      = Real.sqrt (1 + v ^ 2) / Real.sqrt (2 * singMod * (1 + v)) := by
    rw [ellipticFIntegrand, ellipticEIntegrand, sin_singAmp hv0 hv1,
      one_sub_singPar_mul_singSin_sq, Real.sqrt_div (singPar_compl_arg_nonneg hv0), inv_div]
  have htriple := sqrt_triple hv0 hv1
  have hR2 := sq_sqrt_one_add_sq v
  rw [smul_eq_mul, habs, hE, quinticIntegrand, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hsq.ne' hP.ne') hQ.ne') (by positivity)]
  refine mul_right_cancel₀ hR.ne' ?_
  linear_combination (-(singModInv + v) * (1 + v ^ 2)) * htriple
    + (2 * (singModInv + v) * Real.sqrt (v - v ^ 5)) * hR2

/-! ### `K` as an integral over `(0, k₂)` -/

-- Theorem: the substitution itself. `K` at the second singular parameter is the integral
-- of `(k₂⁻¹ + v) / (2 √(v - v⁵))` over `(0, k₂)`.
theorem ellipticF_eq_quintic_integral :
    ellipticF (singMod ^ 2) (Real.pi / 2) = ∫ v in Ioo (0 : ℝ) singMod, quinticIntegrand v := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := singAmp) (f' := singAmpDeriv)
    (s := Ioo (0 : ℝ) singMod) measurableSet_Ioo
    (fun x hx => (hasDerivAt_singAmp hx.1 (lt_trans hx.2 singMod_lt_one)).hasDerivWithinAt)
    singAmp_injOn (ellipticFIntegrand (singMod ^ 2))
  rw [singAmp_image] at h
  rw [ellipticF, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
    integral_Ioc_eq_integral_Ioo, h,
    setIntegral_congr_fun measurableSet_Ioo (fun v hv => singAmp_integrand_eq hv)]

/-! ### The reflection `v ↦ (1 - v)/(1 + v)` -/

/-- The involution exchanging `(0, k₂)` and `(k₂, 1)`. -/
noncomputable def singFlip (v : ℝ) : ℝ := (1 - v) / (1 + v)

theorem singModInv_sq : singModInv ^ 2 = 2 * singModInv + 1 := by
  simp only [singModInv]
  nlinarith [sq_sqrt_two]

theorem singFlip_zero : singFlip 0 = 1 := by norm_num [singFlip]

theorem singFlip_singMod : singFlip singMod = singMod := by
  have h1 : (0 : ℝ) < 1 + singMod := by linarith [singMod_pos]
  rw [singFlip, div_eq_iff h1.ne']
  nlinarith [one_sub_singMod_sq]

theorem singFlip_mem {v : ℝ} (hv : v ∈ Ioo 0 singMod) : singFlip v ∈ Ioo singMod 1 := by
  obtain ⟨hv0, hvA⟩ := hv
  have h1 : (0 : ℝ) < 1 + v := by linarith
  constructor
  · rw [singFlip, lt_div_iff₀ h1]
    nlinarith [one_sub_singMod_sq, singMod_pos]
  · rw [singFlip, div_lt_one h1]
    linarith

theorem continuous_singFlip_on {s : Set ℝ} (hs : ∀ v ∈ s, (0 : ℝ) < 1 + v) :
    ContinuousOn singFlip s := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  exact fun v hv => (hs v hv).ne'

theorem singFlip_image : singFlip '' (Ioo 0 singMod) = Ioo singMod 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact singFlip_mem hv
  · have hcont : ContinuousOn singFlip (Icc 0 singMod) :=
      continuous_singFlip_on (fun v hv => by linarith [hv.1])
    have h := intermediate_value_Ioo' singMod_pos.le hcont
    simpa [singFlip_zero, singFlip_singMod] using h

theorem singFlip_injOn : InjOn singFlip (Ioo 0 singMod) := by
  intro x hx y hy hxy
  have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (0 : ℝ) < 1 + y := by linarith [hy.1]
  rw [singFlip, singFlip, div_eq_div_iff h1.ne' h2.ne'] at hxy
  linarith

theorem hasDerivAt_singFlip {v : ℝ} (hv : (0 : ℝ) < 1 + v) :
    HasDerivAt singFlip (-2 / (1 + v) ^ 2) v := by
  have hnum : HasDerivAt (fun x : ℝ => 1 - x) (-1) v := by
    simpa using (hasDerivAt_id v).const_sub 1
  have hden : HasDerivAt (fun x : ℝ => 1 + x) 1 v := by
    simpa using (hasDerivAt_id v).const_add 1
  refine (hnum.div hden hv.ne').congr_deriv ?_
  field_simp
  ring

theorem sq_div_two_sqrt {x f : ℝ} (hf : 0 ≤ f) :
    (x / (2 * Real.sqrt f)) ^ 2 = x ^ 2 / (4 * f) := by
  rw [div_pow, mul_pow, Real.sq_sqrt hf]
  norm_num

theorem singModInv_sub_one_sq : (singModInv - 1) ^ 2 = 2 := by
  linear_combination singModInv_sq

theorem singModInv_add_singFlip {v : ℝ} (hv : (0 : ℝ) < 1 + v) :
    singModInv + singFlip v = (singModInv - 1) * (singModInv + v) / (1 + v) := by
  rw [singFlip, eq_div_iff hv.ne']
  field_simp
  linear_combination -singModInv_sq

theorem singFlip_quintic {v : ℝ} (hv : (0 : ℝ) < 1 + v) :
    singFlip v - singFlip v ^ 5 = 8 * (v - v ^ 5) / (1 + v) ^ 6 := by
  rw [singFlip]
  field_simp
  ring

theorem singFlip_integrand_eq {v : ℝ} (hv : v ∈ Ioo 0 singMod) :
    |(-2 / (1 + v) ^ 2)| • quinticIntegrand (singFlip v) = quinticIntegrand v := by
  obtain ⟨hv0, hvA⟩ := hv
  have hv1 : v < 1 := lt_trans hvA singMod_lt_one
  have h1 : (0 : ℝ) < 1 + v := by linarith
  have hf := singFlip_mem ⟨hv0, hvA⟩
  have hf0 : 0 < singFlip v := lt_trans singMod_pos hf.1
  have hqf : 0 < singFlip v - singFlip v ^ 5 := quintic_pos hf0 hf.2
  have hqv : 0 < v - v ^ 5 := quintic_pos hv0 hv1
  have hnum : 0 < singModInv + singFlip v := by linarith [singModInv_pos]
  have hnum2 : 0 < singModInv + v := by linarith [singModInv_pos]
  have habs : |(-2 / (1 + v) ^ 2)| = 2 / (1 + v) ^ 2 := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by positivity)]
  rw [smul_eq_mul, habs, quinticIntegrand, quinticIntegrand]
  refine eq_of_sq_eq_of_nonneg
    (le_of_lt (mul_pos (by positivity) (div_pos hnum (by positivity))))
    (le_of_lt (div_pos hnum2 (by positivity))) ?_
  rw [mul_pow, sq_div_two_sqrt hqf.le, sq_div_two_sqrt hqv.le, singModInv_add_singFlip h1,
    singFlip_quintic h1]
  have hq6 : ((1 : ℝ) + v) ^ 6 ≠ 0 := by positivity
  field_simp [hqv.ne', h1.ne']
  linear_combination (4 / (1 - v ^ 4)) * singModInv_sub_one_sq

/-! ### Doubling: the two halves of `(0, 1)` contribute equally -/

theorem singPar_lt_one : singMod ^ 2 < 1 := by
  nlinarith [singMod_pos, singMod_lt_one]

-- Theorem: the reflection carries the integral over `(k₂, 1)` to the one over `(0, k₂)`.
theorem quintic_integral_flip :
    (∫ v in Ioo singMod 1, quinticIntegrand v)
      = ∫ v in Ioo (0 : ℝ) singMod, quinticIntegrand v := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := singFlip)
    (f' := fun v => -2 / (1 + v) ^ 2) (s := Ioo (0 : ℝ) singMod) measurableSet_Ioo
    (fun x hx => (hasDerivAt_singFlip (by linarith [hx.1])).hasDerivWithinAt)
    singFlip_injOn quinticIntegrand
  rw [singFlip_image] at h
  rw [h, setIntegral_congr_fun measurableSet_Ioo (fun v hv => singFlip_integrand_eq hv)]

theorem integrableOn_quintic_left : IntegrableOn quinticIntegrand (Ioo (0 : ℝ) singMod) := by
  have hcont : IntegrableOn (ellipticFIntegrand (singMod ^ 2)) (Ioo 0 (Real.pi / 2)) :=
    ((continuous_ellipticFIntegrand singPar_lt_one).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := singAmp) (f' := singAmpDeriv)
    (s := Ioo (0 : ℝ) singMod) measurableSet_Ioo
    (fun x hx => (hasDerivAt_singAmp hx.1 (lt_trans hx.2 singMod_lt_one)).hasDerivWithinAt)
    singAmp_injOn (ellipticFIntegrand (singMod ^ 2))
  rw [singAmp_image] at h
  exact (h.mp hcont).congr_fun (fun v hv => singAmp_integrand_eq hv) measurableSet_Ioo

theorem integrableOn_quintic_right : IntegrableOn quinticIntegrand (Ioo singMod 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := singFlip)
    (f' := fun v => -2 / (1 + v) ^ 2) (s := Ioo (0 : ℝ) singMod) measurableSet_Ioo
    (fun x hx => (hasDerivAt_singFlip (by linarith [hx.1])).hasDerivWithinAt)
    singFlip_injOn quinticIntegrand
  rw [singFlip_image] at h
  exact h.mpr (integrableOn_quintic_left.congr_fun
    (fun v hv => (singFlip_integrand_eq hv).symm) measurableSet_Ioo)

-- Theorem: hence the whole of `(0, 1)` contributes twice the left half, and `K` is half of it.
theorem quintic_integral_one :
    (∫ v in Ioo (0 : ℝ) 1, quinticIntegrand v)
      = 2 * ellipticF (singMod ^ 2) (Real.pi / 2) := by
  have hleft : IntervalIntegrable quinticIntegrand volume 0 singMod := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le singMod_pos.le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact integrableOn_quintic_left
  have hright : IntervalIntegrable quinticIntegrand volume singMod 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le singMod_lt_one.le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact integrableOn_quintic_right
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [intervalIntegral.integral_of_le singMod_pos.le,
    intervalIntegral.integral_of_le singMod_lt_one.le,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo] at hadd
  rw [← hadd, quintic_integral_flip, ellipticF_eq_quintic_integral]
  ring

/-! ### Down to two Beta integrals -/

/-- The Beta-side integrand `(k₂⁻¹ x ^ (-7/8) + x ^ (-5/8)) (1 - x) ^ (-1/2)`. -/
noncomputable def betaSum (x : ℝ) : ℝ :=
  (singModInv * x ^ (-(7 : ℝ) / 8) + x ^ (-(5 : ℝ) / 8)) * (1 - x) ^ (-(1 : ℝ) / 2)

theorem hasDerivAt_quartic (v : ℝ) : HasDerivAt (fun x : ℝ => x ^ 4) (4 * v ^ 3) v := by
  simpa using hasDerivAt_pow 4 v

theorem quartic_injOn : InjOn (fun x : ℝ => x ^ 4) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  simp only at hxy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy (ne_of_lt (pow_lt_pow_left₀ h hx.1.le (by norm_num)))
  · exact h
  · exact absurd hxy.symm (ne_of_lt (pow_lt_pow_left₀ h hy.1.le (by norm_num)))

theorem quartic_image : (fun x : ℝ => x ^ 4) '' (Ioo (0 : ℝ) 1) = Ioo (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨pow_pos hv.1 4, pow_lt_one₀ hv.1.le hv.2 (by norm_num)⟩
  · have hcont : ContinuousOn (fun x : ℝ => x ^ 4) (Icc 0 1) := (continuous_pow 4).continuousOn
    have h := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hcont
    simpa using h

theorem quartic_integrand_eq {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    |4 * v ^ 3| • betaSum (v ^ 4) = 8 * quinticIntegrand v := by
  obtain ⟨hv0, hv1⟩ := hv
  have hs : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv0.le
  have hs0 : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have h4 : (0 : ℝ) < 1 - v ^ 4 := by
    have := pow_lt_one₀ hv0.le hv1 (by norm_num : 4 ≠ 0)
    linarith
  have hr : (0 : ℝ) < Real.sqrt (1 - v ^ 4) := Real.sqrt_pos.mpr h4
  have hsq : Real.sqrt (v - v ^ 5) = Real.sqrt v * Real.sqrt (1 - v ^ 4) := by
    rw [← Real.sqrt_mul hv0.le]
    congr 1
    ring
  have e7 : (v ^ 4 : ℝ) ^ (-(7 : ℝ) / 8) = (Real.sqrt v ^ 7)⁻¹ := by
    rw [← hs, ← pow_mul, show 2 * 4 = 8 from rfl, ← Real.rpow_natCast (Real.sqrt v) 8,
      ← Real.rpow_mul hs0.le, show ((8 : ℕ) : ℝ) * (-(7 : ℝ) / 8) = -(7 : ℝ) by norm_num,
      Real.rpow_neg hs0.le, hs]
    norm_num [Real.rpow_natCast]
  have e5 : (v ^ 4 : ℝ) ^ (-(5 : ℝ) / 8) = (Real.sqrt v ^ 5)⁻¹ := by
    rw [← hs, ← pow_mul, show 2 * 4 = 8 from rfl, ← Real.rpow_natCast (Real.sqrt v) 8,
      ← Real.rpow_mul hs0.le, show ((8 : ℕ) : ℝ) * (-(5 : ℝ) / 8) = -(5 : ℝ) by norm_num,
      Real.rpow_neg hs0.le, hs]
    norm_num [Real.rpow_natCast]
  have e2 : ((1 : ℝ) - v ^ 4) ^ (-(1 : ℝ) / 2) = (Real.sqrt (1 - v ^ 4))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h4.le]
    norm_num
  have habs : |4 * v ^ 3| = 4 * v ^ 3 := abs_of_pos (by positivity)
  rw [smul_eq_mul, habs, betaSum, e7, e5, e2, quinticIntegrand, hsq]
  field_simp
  rw [show Real.sqrt v ^ 6 = (Real.sqrt v ^ 2) ^ 3 by ring, hs]
  ring

-- Theorem: the quartic substitution `x = v⁴` turns the two Beta integrands into the
-- `v`-side integrand, so their sum integrates to `16 K`.
theorem betaSum_integral :
    (∫ x in Ioo (0 : ℝ) 1, betaSum x) = 16 * ellipticF (singMod ^ 2) (Real.pi / 2) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ => x ^ 4)
    (f' := fun x : ℝ => 4 * x ^ 3) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (fun x _ => (hasDerivAt_quartic x).hasDerivWithinAt) quartic_injOn betaSum
  rw [quartic_image] at h
  rw [h, setIntegral_congr_fun measurableSet_Ioo (fun v hv => quartic_integrand_eq hv),
    integral_const_mul, quintic_integral_one]
  ring

/-- The Beta integrand `Β(1/8, 1/2)`. -/
noncomputable def betaOne (x : ℝ) : ℝ := x ^ (-(7 : ℝ) / 8) * (1 - x) ^ (-(1 : ℝ) / 2)

/-- The Beta integrand `Β(3/8, 1/2)`. -/
noncomputable def betaThree (x : ℝ) : ℝ := x ^ (-(5 : ℝ) / 8) * (1 - x) ^ (-(1 : ℝ) / 2)

theorem betaSum_eq (x : ℝ) : betaSum x = singModInv * betaOne x + betaThree x := by
  rw [betaSum, betaOne, betaThree]; ring

theorem betaOne_nonneg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ betaOne x :=
  mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.rpow_nonneg (by linarith [hx.2]) _)

theorem betaThree_nonneg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ betaThree x :=
  mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.rpow_nonneg (by linarith [hx.2]) _)

theorem continuousOn_betaOne : ContinuousOn betaOne (Ioo (0 : ℝ) 1) := by
  unfold betaOne
  refine ContinuousOn.mul (ContinuousOn.rpow_const (by fun_prop) ?_)
    (ContinuousOn.rpow_const (by fun_prop) ?_)
  · exact fun x hx => Or.inl (ne_of_gt hx.1)
  · refine fun x hx => Or.inl ?_
    have h := hx.2
    intro hc
    linarith

theorem continuousOn_betaThree : ContinuousOn betaThree (Ioo (0 : ℝ) 1) := by
  unfold betaThree
  refine ContinuousOn.mul (ContinuousOn.rpow_const (by fun_prop) ?_)
    (ContinuousOn.rpow_const (by fun_prop) ?_)
  · exact fun x hx => Or.inl (ne_of_gt hx.1)
  · refine fun x hx => Or.inl ?_
    have h := hx.2
    intro hc
    linarith

theorem integrableOn_quintic_one : IntegrableOn quinticIntegrand (Ioo (0 : ℝ) 1) := by
  have hleft : IntervalIntegrable quinticIntegrand volume 0 singMod := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le singMod_pos.le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact integrableOn_quintic_left
  have hright : IntervalIntegrable quinticIntegrand volume singMod 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le singMod_lt_one.le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact integrableOn_quintic_right
  have h := hleft.trans hright
  rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integrableOn_Ioc_iff_integrableOn_Ioo] at h

theorem integrableOn_betaSum : IntegrableOn betaSum (Ioo (0 : ℝ) 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := fun x : ℝ => x ^ 4)
    (f' := fun x : ℝ => 4 * x ^ 3) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (fun x _ => (hasDerivAt_quartic x).hasDerivWithinAt) quartic_injOn betaSum
  rw [quartic_image] at h
  exact h.mpr (IntegrableOn.congr_fun (integrableOn_quintic_one.const_mul 8)
    (fun v hv => (quartic_integrand_eq hv).symm) measurableSet_Ioo)

theorem integrableOn_betaOne : IntegrableOn betaOne (Ioo (0 : ℝ) 1) := by
  have hB := singModInv_pos
  refine Integrable.mono' (g := fun x => singModInv⁻¹ * betaSum x)
    (integrableOn_betaSum.const_mul _)
    (continuousOn_betaOne.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (betaOne_nonneg hx), betaSum_eq, mul_add,
    inv_mul_cancel_left₀ hB.ne']
  have := mul_nonneg (inv_pos.mpr hB).le (betaThree_nonneg hx)
  linarith

theorem integrableOn_betaThree : IntegrableOn betaThree (Ioo (0 : ℝ) 1) := by
  have hB := singModInv_pos
  refine Integrable.mono' (g := betaSum) integrableOn_betaSum
    (continuousOn_betaThree.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (betaThree_nonneg hx), betaSum_eq]
  have := mul_nonneg hB.le (betaOne_nonneg hx)
  linarith

-- Theorem: the `16 K` of the previous section, split into its two Beta integrals.
theorem beta_combination :
    singModInv * (∫ x in Ioo (0 : ℝ) 1, betaOne x) + (∫ x in Ioo (0 : ℝ) 1, betaThree x)
      = 16 * ellipticF (singMod ^ 2) (Real.pi / 2) := by
  rw [← betaSum_integral,
    setIntegral_congr_fun measurableSet_Ioo (fun x _ => betaSum_eq x),
    integral_add (integrableOn_betaOne.const_mul _) integrableOn_betaThree, integral_const_mul]

/-! ### From the Beta integrals to `Γ` -/

theorem betaIntegral_one_eighth :
    Complex.betaIntegral (1 / 8) (1 / 2) = ((∫ x in Ioo (0 : ℝ) 1, betaOne x : ℝ) : ℂ) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_ofReal, Complex.betaIntegral]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx1 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
  rw [betaOne]
  push_cast
  rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow hx1]
  push_cast
  norm_num

theorem betaIntegral_three_eighths :
    Complex.betaIntegral (3 / 8) (1 / 2) = ((∫ x in Ioo (0 : ℝ) 1, betaThree x : ℝ) : ℂ) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_ofReal, Complex.betaIntegral]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx1 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
  rw [betaThree]
  push_cast
  rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow hx1]
  push_cast
  norm_num

theorem gamma_beta_one_eighth :
    Real.Gamma (1 / 8) * Real.sqrt Real.pi
      = Real.Gamma (5 / 8) * ∫ x in Ioo (0 : ℝ) 1, betaOne x := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (1 / 8 : ℂ)) (t := (1 / 2 : ℂ))
    (by norm_num) (by norm_num)
  rw [betaIntegral_one_eighth, show ((1 : ℂ) / 8 + 1 / 2) = ((5 / 8 : ℝ) : ℂ) by norm_num,
    show ((1 : ℂ) / 8) = ((1 / 8 : ℝ) : ℂ) by norm_num,
    show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  rw [← Real.Gamma_one_half_eq]
  exact_mod_cast h

theorem gamma_beta_three_eighths :
    Real.Gamma (3 / 8) * Real.sqrt Real.pi
      = Real.Gamma (7 / 8) * ∫ x in Ioo (0 : ℝ) 1, betaThree x := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (3 / 8 : ℂ)) (t := (1 / 2 : ℂ))
    (by norm_num) (by norm_num)
  rw [betaIntegral_three_eighths, show ((3 : ℂ) / 8 + 1 / 2) = ((7 / 8 : ℝ) : ℂ) by norm_num,
    show ((3 : ℂ) / 8) = ((3 / 8 : ℝ) : ℂ) by norm_num,
    show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  rw [← Real.Gamma_one_half_eq]
  exact_mod_cast h

/-! ### The elementary constants -/

theorem sqrt_two_sub_eq :
    Real.sqrt (2 - Real.sqrt 2) = (Real.sqrt 2 - 1) * Real.sqrt (2 + Real.sqrt 2) := by
  have h2 : (0 : ℝ) < 2 - Real.sqrt 2 := by linarith [sqrt_two_lt_two]
  have h3 : (0 : ℝ) < 2 + Real.sqrt 2 := by positivity
  refine eq_of_sq_eq_of_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (by linarith [one_lt_sqrt_two]) (Real.sqrt_nonneg _)) ?_
  rw [Real.sq_sqrt h2.le, mul_pow, Real.sq_sqrt h3.le]
  linear_combination -Real.sqrt 2 * sq_sqrt_two

theorem two_rpow_key :
    Real.sqrt 2 * Real.sqrt (2 + Real.sqrt 2) * (2 : ℝ) ^ ((13 : ℝ) / 4)
      = 16 * Real.sqrt (Real.sqrt 2 + 1) := by
  have h2 : (0 : ℝ) < 2 + Real.sqrt 2 := by positivity
  have h3 : (0 : ℝ) < Real.sqrt 2 + 1 := by positivity
  refine eq_of_sq_eq_of_nonneg (by positivity) (by positivity) ?_
  have e4 : ((2 : ℝ) ^ ((13 : ℝ) / 4)) ^ 2 = 2 ^ ((13 : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((13 : ℝ) / 4)) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  have e5 : (2 : ℝ) ^ ((13 : ℝ) / 2) = 64 * Real.sqrt 2 := by
    rw [show (13 : ℝ) / 2 = 6 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
      ← Real.sqrt_eq_rpow]
    norm_num
  rw [mul_pow, mul_pow, sq_sqrt_two, Real.sq_sqrt h2.le, e4, e5, mul_pow, Real.sq_sqrt h3.le]
  linear_combination (128 : ℝ) * sq_sqrt_two

/-! ### The second singular value -/

-- Theorem: `K(k₂) = √(√2 + 1) Γ(1/8) Γ(3/8) / (2 ^ (13/4) √π)`.
theorem ellipticF_secondSingular :
    ellipticF ((Real.sqrt 2 - 1) ^ 2) (Real.pi / 2)
      = Real.sqrt (Real.sqrt 2 + 1) * (Real.Gamma (1 / 8) * Real.Gamma (3 / 8))
          / ((2 : ℝ) ^ ((13 : ℝ) / 4) * Real.sqrt Real.pi) := by
  have hmod : (Real.sqrt 2 - 1 : ℝ) = singMod := rfl
  have hpi := Real.pi_pos
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hspsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hpi.le
  have h1 := gamma_beta_one_eighth
  have h3 := gamma_beta_three_eighths
  have hmain := beta_combination
  have hs1 : Real.sin (Real.pi * (1 / 8)) = Real.sqrt (2 - Real.sqrt 2) / 2 := by
    rw [show Real.pi * (1 / 8) = Real.pi / 8 by ring, Real.sin_pi_div_eight]
  have hs3 : Real.sin (Real.pi * (3 / 8)) = Real.sqrt (2 + Real.sqrt 2) / 2 := by
    rw [show Real.pi * (3 / 8) = Real.pi / 2 - Real.pi / 8 by ring, Real.sin_pi_div_two_sub,
      Real.cos_pi_div_eight]
  have hsin1 : 0 < Real.sin (Real.pi * (1 / 8)) := by
    rw [hs1]
    exact div_pos (Real.sqrt_pos.mpr (by linarith [sqrt_two_lt_two])) two_pos
  have hsin3 : 0 < Real.sin (Real.pi * (3 / 8)) := by
    rw [hs3]
    exact div_pos (Real.sqrt_pos.mpr (by positivity)) two_pos
  have hprod1 : Real.Gamma (1 / 8) * Real.Gamma (7 / 8) * Real.sin (Real.pi * (1 / 8))
      = Real.pi := by
    have h := Real.Gamma_mul_Gamma_one_sub (1 / 8 : ℝ)
    rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num] at h
    rw [h, div_mul_cancel₀ _ hsin1.ne']
  have hprod3 : Real.Gamma (3 / 8) * Real.Gamma (5 / 8) * Real.sin (Real.pi * (3 / 8))
      = Real.pi := by
    have h := Real.Gamma_mul_Gamma_one_sub (3 / 8 : ℝ)
    rw [show (1 : ℝ) - 3 / 8 = 5 / 8 by norm_num] at h
    rw [h, div_mul_cancel₀ _ hsin3.ne']
  have e1 : Real.pi * (∫ x in Ioo (0 : ℝ) 1, betaOne x)
      = Real.sin (Real.pi * (3 / 8)) * (Real.Gamma (1 / 8) * Real.Gamma (3 / 8))
        * Real.sqrt Real.pi := by
    linear_combination (-Real.sin (Real.pi * (3 / 8)) * Real.Gamma (3 / 8)) * h1
      + (-(∫ x in Ioo (0 : ℝ) 1, betaOne x)) * hprod3
  have e3 : Real.pi * (∫ x in Ioo (0 : ℝ) 1, betaThree x)
      = Real.sin (Real.pi * (1 / 8)) * (Real.Gamma (1 / 8) * Real.Gamma (3 / 8))
        * Real.sqrt Real.pi := by
    linear_combination (-Real.sin (Real.pi * (1 / 8)) * Real.Gamma (1 / 8)) * h3
      + (-(∫ x in Ioo (0 : ℝ) 1, betaThree x)) * hprod1
  have hBs : singModInv * Real.sin (Real.pi * (3 / 8)) + Real.sin (Real.pi * (1 / 8))
      = Real.sqrt 2 * Real.sqrt (2 + Real.sqrt 2) := by
    rw [hs1, hs3, sqrt_two_sub_eq, singModInv]
    ring
  have hbig : Real.pi * (16 * ellipticF (singMod ^ 2) (Real.pi / 2))
      = Real.sqrt 2 * Real.sqrt (2 + Real.sqrt 2)
        * (Real.Gamma (1 / 8) * Real.Gamma (3 / 8)) * Real.sqrt Real.pi := by
    linear_combination (-Real.pi) * hmain + singModInv * e1 + e3
      + (Real.Gamma (1 / 8) * Real.Gamma (3 / 8) * Real.sqrt Real.pi) * hBs
  have h4 : Real.sqrt Real.pi * (16 * ellipticF (singMod ^ 2) (Real.pi / 2))
      = Real.sqrt 2 * Real.sqrt (2 + Real.sqrt 2)
        * (Real.Gamma (1 / 8) * Real.Gamma (3 / 8)) := by
    refine mul_right_cancel₀ hsp.ne' ?_
    linear_combination hbig + (16 * ellipticF (singMod ^ 2) (Real.pi / 2)) * hspsq
  rw [hmod, eq_div_iff (mul_pos (Real.rpow_pos_of_pos two_pos _) hsp).ne']
  linear_combination ((2 : ℝ) ^ ((13 : ℝ) / 4) / 16) * h4
    + (Real.Gamma (1 / 8) * Real.Gamma (3 / 8) / 16) * two_rpow_key

end Pconstructible
