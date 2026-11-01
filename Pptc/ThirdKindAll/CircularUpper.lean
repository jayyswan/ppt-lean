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

import Pptc.ThirdKindAll.Circular
import Pptc.ThirdKindAll.Pseudo
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # Pptc.ThirdKindAll.CircularUpper

The circular range `c < n < 1`, reduced to `n < 0` by DLMF 19.7.9. -/

namespace Pconstructible

/-- The transformed characteristic `n' = (c-n)/(1-n) < 0`. -/
noncomputable def circUpperNu (c n : ℝ) : ℝ := (c - n) / (1 - n)

/-- The complementary amplitude `φ' = arcsin(cos φ / Δ(φ))`. -/
noncomputable def circUpperPhi (c φ : ℝ) : ℝ :=
  Real.arcsin (Real.cos φ / ellipticEIntegrand c φ)

/-- The right-hand side of DLMF 19.7.9. -/
noncomputable def circUpperRHS (c n φ : ℝ) : ℝ :=
  c / (c - n) * ellipticF c φ
    - n * (1 - c) / ((1 - n) * (c - n)) *
        (ellipticPi c (circUpperNu c n)
          - ellipticPiInc c (circUpperNu c n) (circUpperPhi c φ))

theorem circUpperNu_neg {c n : ℝ} (hc : c < n) (hn : n < 1) :
    circUpperNu c n < 0 := by
  unfold circUpperNu
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

theorem circUpperNu_lt_one {c n : ℝ} (hc : c < n) (hn : n < 1) :
    circUpperNu c n < 1 := by
  have h := circUpperNu_neg hc hn
  linarith

theorem circUpperPhi_zero {c : ℝ} (hc : c < 1) : circUpperPhi c 0 = Real.pi / 2 := by
  unfold circUpperPhi
  simp [ellipticEIntegrand, Real.arcsin_one]

theorem circUpperArg_bounds {c φ : ℝ} (hc : c < 1) (h0 : 0 < φ)
    (hπ : φ < Real.pi / 2) :
    -1 < Real.cos φ / ellipticEIntegrand c φ
      ∧ Real.cos φ / ellipticEIntegrand c φ < 1 := by
  have hE := ellipticEIntegrand_pos hc φ
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [hπ, Real.pi_pos])
  have hcos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  constructor
  · have := div_nonneg hcos.le hE.le
    linarith
  · rw [div_lt_one hE]
    have hΔ2 := ellipticEIntegrand_sq hc φ
    have hs2 := Real.sin_sq_add_cos_sq φ
    have hs2pos : 0 < Real.sin φ ^ 2 := by positivity
    have hsq : Real.cos φ ^ 2 < ellipticEIntegrand c φ ^ 2 := by
      rw [hΔ2]; nlinarith
    nlinarith

theorem circUpperPhi_sin {c φ : ℝ} (hc : c < 1) (h0 : 0 < φ) (hπ : φ < Real.pi / 2) :
    Real.sin (circUpperPhi c φ)
      = Real.cos φ / ellipticEIntegrand c φ := by
  obtain ⟨hA1, hA2⟩ := circUpperArg_bounds hc h0 hπ
  unfold circUpperPhi
  exact Real.sin_arcsin hA1.le hA2.le

theorem circUpperPhi_cos {c φ : ℝ} (hc : c < 1) (h0 : 0 < φ) (hπ : φ < Real.pi / 2) :
    Real.cos (circUpperPhi c φ)
      = Real.sqrt (1 - c) * Real.sin φ / ellipticEIntegrand c φ := by
  have hE := ellipticEIntegrand_pos hc φ
  have hs : 0 ≤ Real.sin φ := (Real.sin_pos_of_pos_of_lt_pi h0
    (by linarith [hπ, Real.pi_pos])).le
  unfold circUpperPhi
  rw [Real.cos_arcsin]
  have hΔ2 := ellipticEIntegrand_sq hc φ
  have h1mA2 : 1 - (Real.cos φ / ellipticEIntegrand c φ) ^ 2
      = (1 - c) * Real.sin φ ^ 2 / ellipticEIntegrand c φ ^ 2 := by
    field_simp [hE.ne']
    nlinarith [Real.sin_sq_add_cos_sq φ]
  rw [h1mA2, Real.sqrt_div (by positivity), Real.sqrt_mul (by linarith),
    Real.sqrt_sq hs, Real.sqrt_sq hE.le]

/-- The complementary amplitude has derivative `-k'/Δ²`. -/
theorem hasDerivAt_circUpperPhi {c φ : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (h0 : 0 < φ) (hπ : φ < Real.pi / 2) :
    HasDerivAt (circUpperPhi c) (-Real.sqrt (1 - c) / ellipticEIntegrand c φ ^ 2) φ := by
  obtain ⟨hA1, hA2⟩ := circUpperArg_bounds hc h0 hπ
  have hE := ellipticEIntegrand_pos hc φ
  have hΔ' : HasDerivAt (ellipticEIntegrand c) (-(2 * c * Real.sin φ * Real.cos φ)
      / (2 * ellipticEIntegrand c φ)) φ :=
    hasDerivAt_ellipticEIntegrand c φ (one_sub_mul_sin_sq_pos hc φ).ne'
  have hA := (Real.hasDerivAt_cos φ).div hΔ' hE.ne'
  have hcomp := (Real.hasDerivAt_arcsin (ne_of_gt hA1) (ne_of_lt hA2)).comp φ hA
  refine (hcomp.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.EventuallyEq.of_eq (by
      funext y
      unfold circUpperPhi
      simp only [Function.comp_apply, Pi.div_apply])
  · have hΔ2 := ellipticEIntegrand_sq hc φ
    have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [hπ, Real.pi_pos])
    have h1mA2 : 1 - (Real.cos φ / ellipticEIntegrand c φ) ^ 2
        = (1 - c) * Real.sin φ ^ 2 / ellipticEIntegrand c φ ^ 2 := by
      field_simp [hE.ne']
      nlinarith [Real.sin_sq_add_cos_sq φ]
    have hsqrt : Real.sqrt (1 - (Real.cos φ / ellipticEIntegrand c φ) ^ 2)
        = Real.sqrt (1 - c) * Real.sin φ / ellipticEIntegrand c φ := by
      rw [h1mA2, Real.sqrt_div (by positivity), Real.sqrt_mul (by linarith),
        Real.sqrt_sq hs.le, Real.sqrt_sq hE.le]
    rw [hsqrt]
    field_simp [hE.ne', hs.ne',
      Real.sqrt_pos.mpr (by linarith : 0 < 1 - c) |>.ne']
    rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - c), hΔ2]
    nlinarith [Real.sin_sq_add_cos_sq φ]

/-- The DLMF 19.7.9 right-hand side has the third-kind integrand as derivative. -/
theorem hasDerivAt_circUpperRHS {c n φ : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (hcn : c < n) (hn : n < 1) (h0 : 0 < φ) (hπ : φ < Real.pi / 2) :
    HasDerivAt (circUpperRHS c n) (ellipticPiIntegrand c n φ) φ := by
  have hn' := circUpperNu_neg hcn hn
  have hn'1 := circUpperNu_lt_one hcn hn
  have hν : 1 - n ≠ 0 := by linarith
  have hD : c - n ≠ 0 := by linarith
  have hF := hasDerivAt_ellipticF hc φ
  have hPhi := hasDerivAt_circUpperPhi hc0 hc h0 hπ
  have hPi := (hasDerivAt_ellipticPiInc hc hn'1 (circUpperPhi c φ)).comp φ hPhi
  have hbracket := (hasDerivAt_const (x := φ) (ellipticPi c (circUpperNu c n))).sub hPi
  have htotal := (hF.const_mul (c / (c - n))).sub (hbracket.const_mul
    (n * (1 - c) / ((1 - n) * (c - n))))
  refine (htotal.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.EventuallyEq.of_eq (by
      funext y
      unfold circUpperRHS
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Function.comp_apply])
  ·
    have hE := ellipticEIntegrand_pos hc φ
    have hΔ2 := ellipticEIntegrand_sq hc φ
    have hs := circUpperPhi_sin hc h0 hπ
    have hν_def : circUpperNu c n = (c - n) / (1 - n) := rfl
    have hν_pole : 1 - circUpperNu c n * Real.sin (circUpperPhi c φ) ^ 2
        = (1 - c) * (1 - n * Real.sin φ ^ 2) / ((1 - n) * ellipticEIntegrand c φ ^ 2) := by
      rw [hs, hν_def]
      field_simp [hE.ne', hν]
      rw [hΔ2, show Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 by
        linarith [Real.sin_sq_add_cos_sq φ]]
      ring
    have hΔphi : ellipticEIntegrand c (circUpperPhi c φ)
        = Real.sqrt (1 - c) / ellipticEIntegrand c φ := by
      unfold ellipticEIntegrand
      have hinside : 1 - c * (Real.cos φ / ellipticEIntegrand c φ) ^ 2
          = (1 - c) / ellipticEIntegrand c φ ^ 2 := by
        field_simp [hE.ne']
        nlinarith [hΔ2, Real.sin_sq_add_cos_sq φ]
      rw [hs, hinside, Real.sqrt_div (by linarith), Real.sqrt_sq hE.le]
      rfl
    have hWne : 1 - n * Real.sin φ ^ 2 ≠ 0 := by
      have hpos : 0 < 1 - n * Real.sin φ ^ 2 := by
        nlinarith [Real.sin_sq_le_one φ, hn]
      exact hpos.ne'
    simp only [ellipticPiIntegrand, hΔphi, hν_pole, ellipticFIntegrand]
    field_simp [hE.ne', hν, hD, hWne,
      (by linarith : (1 : ℝ) - c ≠ 0),
      Real.sqrt_pos.mpr (by linarith : 0 < 1 - c) |>.ne']
    ring_nf
    nlinarith [hΔ2]

theorem continuous_circUpperRHS {c n : ℝ} (hc : c < 1) (hcn : c < n) (hn : n < 1) :
    Continuous (circUpperRHS c n) := by
  have hν := circUpperNu_neg hcn hn
  have hν1 := circUpperNu_lt_one hcn hn
  have hcontPiInc : Continuous (ellipticPiInc c (circUpperNu c n)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_ellipticPiInc hc hν1 x).continuousAt
  have hcontF : Continuous (ellipticF c) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_ellipticF hc x).continuousAt
  have hcontPhi : Continuous (circUpperPhi c) := by
    unfold circUpperPhi ellipticEIntegrand
    refine Real.continuous_arcsin.comp ?_
    exact Real.continuous_cos.div (Real.continuous_sqrt.comp (by fun_prop))
      (fun x => (Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos hc x)).ne')
  unfold circUpperRHS
  exact (continuous_const.mul hcontF).sub
    (continuous_const.mul (continuous_const.sub (hcontPiInc.comp hcontPhi)))

/-- DLMF 19.7.9, for `0 ≤ φ ≤ π/2`. -/
theorem ellipticPiInc_eq_circUpper {c n φ : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (hcn : c < n) (hn : n < 1) (h0 : 0 ≤ φ) (hπ : φ ≤ Real.pi / 2) :
    ellipticPiInc c n φ = circUpperRHS c n φ := by
  rcases eq_or_lt_of_le h0 with rfl | h0pos
  · rw [ellipticPiInc, circUpperRHS, circUpperPhi_zero hc]
    rw [ellipticPi_eq_inc]
    simp [ellipticF]
  · have hν := circUpperNu_neg hcn hn
    have hν1 := circUpperNu_lt_one hcn hn
    have hcont := continuous_circUpperRHS hc hcn hn
    have hderiv : ∀ ψ ∈ Set.Ioo (0 : ℝ) φ,
        HasDerivAt (circUpperRHS c n) (ellipticPiIntegrand c n ψ) ψ := by
      intro ψ hψ
      exact hasDerivAt_circUpperRHS hc0 hc hcn hn hψ.1
        (by linarith [hψ.2, hπ])
    have hint : IntervalIntegrable (ellipticPiIntegrand c n) MeasureTheory.volume 0 φ :=
      (continuous_ellipticPiIntegrand hc hn).intervalIntegrable 0 φ
    have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (a := (0 : ℝ)) (b := φ) h0pos hderiv hint
      (hcont.continuousAt.tendsto.mono_left inf_le_left)
      (hcont.continuousAt.tendsto.mono_left inf_le_left)
    have hz : circUpperRHS c n 0 = 0 := by
      rw [circUpperRHS, circUpperPhi_zero hc]
      rw [ellipticPi_eq_inc]
      simp [ellipticF]
    rw [ellipticPiInc, hkey, hz, sub_zero]

/-! ### The same connection for `0 < n < c`

DLMF 19.7.9 is an involution `n ↦ (c-n)/(1-n)`; its proof only needs the transformed
parameter to stay below `1`, not below `0`. The following copies therefore cover the
hyperbolic range as well. -/

theorem circUpperNu_lt_one_of_lt {c n : ℝ} (hc : c < 1) (hnc : n < c) :
    circUpperNu c n < 1 := by
  unfold circUpperNu
  rw [div_lt_one (by linarith)]
  linarith

theorem hasDerivAt_circUpperRHS_of_lt {c n φ : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (hnc : n < c) (h0 : 0 < φ) (hπ : φ < Real.pi / 2) :
    HasDerivAt (circUpperRHS c n) (ellipticPiIntegrand c n φ) φ := by
  have hn := lt_trans hnc hc
  have hn'1 := circUpperNu_lt_one_of_lt hc hnc
  have hν : 1 - n ≠ 0 := by linarith
  have hD : c - n ≠ 0 := by linarith
  have hF := hasDerivAt_ellipticF hc φ
  have hPhi := hasDerivAt_circUpperPhi hc0 hc h0 hπ
  have hPi := (hasDerivAt_ellipticPiInc hc hn'1 (circUpperPhi c φ)).comp φ hPhi
  have hbracket := (hasDerivAt_const (x := φ) (ellipticPi c (circUpperNu c n))).sub hPi
  have htotal := (hF.const_mul (c / (c - n))).sub (hbracket.const_mul
    (n * (1 - c) / ((1 - n) * (c - n))))
  refine (htotal.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.EventuallyEq.of_eq (by
      funext y
      unfold circUpperRHS
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Function.comp_apply])
  ·
    have hE := ellipticEIntegrand_pos hc φ
    have hΔ2 := ellipticEIntegrand_sq hc φ
    have hs := circUpperPhi_sin hc h0 hπ
    have hν_def : circUpperNu c n = (c - n) / (1 - n) := rfl
    have hν_pole : 1 - circUpperNu c n * Real.sin (circUpperPhi c φ) ^ 2
        = (1 - c) * (1 - n * Real.sin φ ^ 2) / ((1 - n) * ellipticEIntegrand c φ ^ 2) := by
      rw [hs, hν_def]
      field_simp [hE.ne', hν]
      rw [hΔ2, show Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 by
        linarith [Real.sin_sq_add_cos_sq φ]]
      ring
    have hΔphi : ellipticEIntegrand c (circUpperPhi c φ)
        = Real.sqrt (1 - c) / ellipticEIntegrand c φ := by
      unfold ellipticEIntegrand
      have hinside : 1 - c * (Real.cos φ / ellipticEIntegrand c φ) ^ 2
          = (1 - c) / ellipticEIntegrand c φ ^ 2 := by
        field_simp [hE.ne']
        nlinarith [hΔ2, Real.sin_sq_add_cos_sq φ]
      rw [hs, hinside, Real.sqrt_div (by linarith), Real.sqrt_sq hE.le]
      rfl
    have hWne : 1 - n * Real.sin φ ^ 2 ≠ 0 := by
      have hpos : 0 < 1 - n * Real.sin φ ^ 2 := by
        nlinarith [Real.sin_sq_le_one φ, hn]
      exact hpos.ne'
    simp only [ellipticPiIntegrand, hΔphi, hν_pole, ellipticFIntegrand]
    field_simp [hE.ne', hν, hD, hWne,
      (by linarith : (1 : ℝ) - c ≠ 0),
      Real.sqrt_pos.mpr (by linarith : 0 < 1 - c) |>.ne']
    ring_nf
    nlinarith [hΔ2]

theorem continuous_circUpperRHS_of_lt {c n : ℝ} (hc : c < 1) (hnc : n < c) :
    Continuous (circUpperRHS c n) := by
  have hn := lt_trans hnc hc
  have hν1 := circUpperNu_lt_one_of_lt hc hnc
  have hcontPiInc : Continuous (ellipticPiInc c (circUpperNu c n)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_ellipticPiInc hc hν1 x).continuousAt
  have hcontF : Continuous (ellipticF c) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_ellipticF hc x).continuousAt
  have hcontPhi : Continuous (circUpperPhi c) := by
    unfold circUpperPhi ellipticEIntegrand
    refine Real.continuous_arcsin.comp ?_
    exact Real.continuous_cos.div (Real.continuous_sqrt.comp (by fun_prop))
      (fun x => (Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos hc x)).ne')
  unfold circUpperRHS
  exact (continuous_const.mul hcontF).sub
    (continuous_const.mul (continuous_const.sub (hcontPiInc.comp hcontPhi)))

/-- DLMF 19.7.9, for `0 < n < c` and `0 ≤ φ ≤ π/2`. -/
theorem ellipticPiInc_eq_circUpper_of_lt {c n φ : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (hnc : n < c) (h0 : 0 ≤ φ) (hπ : φ ≤ Real.pi / 2) :
    ellipticPiInc c n φ = circUpperRHS c n φ := by
  rcases eq_or_lt_of_le h0 with rfl | h0pos
  · rw [ellipticPiInc, circUpperRHS, circUpperPhi_zero hc]
    rw [ellipticPi_eq_inc]
    simp [ellipticF]
  · have hn := lt_trans hnc hc
    have hν1 := circUpperNu_lt_one_of_lt hc hnc
    have hcont := continuous_circUpperRHS_of_lt hc hnc
    have hderiv : ∀ ψ ∈ Set.Ioo (0 : ℝ) φ,
        HasDerivAt (circUpperRHS c n) (ellipticPiIntegrand c n ψ) ψ := by
      intro ψ hψ
      exact hasDerivAt_circUpperRHS_of_lt hc0 hc hnc hψ.1
        (by linarith [hψ.2, hπ])
    have hint : IntervalIntegrable (ellipticPiIntegrand c n) MeasureTheory.volume 0 φ :=
      (continuous_ellipticPiIntegrand hc hn).intervalIntegrable 0 φ
    have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (a := (0 : ℝ)) (b := φ) h0pos hderiv hint
      (hcont.continuousAt.tendsto.mono_left inf_le_left)
      (hcont.continuousAt.tendsto.mono_left inf_le_left)
    have hz : circUpperRHS c n 0 = 0 := by
      rw [circUpperRHS, circUpperPhi_zero hc]
      rw [ellipticPi_eq_inc]
      simp [ellipticF]
    rw [ellipticPiInc, hkey, hz, sub_zero]

theorem ellipticPiInc_Pconstructible_circ_upper_Icc {c n φ : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) (hφP : PConstructible φ) (hc0 : 0 < c) (hc : c < 1)
    (hcn : c < n) (hn : n < 1) (h0 : 0 ≤ φ) (hπ : φ ≤ Real.pi / 2) :
    PConstructible (ellipticPiInc c n φ) := by
  rw [ellipticPiInc_eq_circUpper hc0 hc hcn hn h0 hπ]
  unfold circUpperRHS
  have hn'P : PConstructible (circUpperNu c n) := by
    unfold circUpperNu; pconstructible
  have hn'neg : circUpperNu c n < 0 := circUpperNu_neg hcn hn
  have hn'1 : circUpperNu c n < 1 := circUpperNu_lt_one hcn hn
  have hΔP : PConstructible (ellipticEIntegrand c φ) :=
    ellipticEIntegrand_Pconstructible hcP hφP
  have hφ'P : PConstructible (circUpperPhi c φ) := by
    unfold circUpperPhi
    refine arcsin_Pconstructible ?_
    pconstructible
  have hPiP : PConstructible (ellipticPiInc c (circUpperNu c n) (circUpperPhi c φ)) :=
    ellipticPiInc_Pconstructible_neg hcP hn'P hφ'P hc0 hc hn'neg
  have hcomplete : PConstructible (ellipticPi c (circUpperNu c n)) :=
    ellipticPi_Pconstructible hcP hn'P hc0 hc hn'1
  have hF : PConstructible (ellipticF c φ) := ellipticF_Pconstructible hcP hφP hc
  pconstructible

theorem ellipticPiIntegrand_pi_sub (c n x : ℝ) :
    ellipticPiIntegrand c n (Real.pi - x) = ellipticPiIntegrand c n x := by
  simp [ellipticPiIntegrand, ellipticEIntegrand]

/-- Reflection about the quarter turn. -/
theorem ellipticPiInc_eq_two_complete_sub {c n θ : ℝ} (hc : c < 1) (hn : n < 1)
    (h1 : Real.pi / 2 ≤ θ) (h2 : θ ≤ Real.pi) :
    ellipticPiInc c n θ = 2 * ellipticPi c n - ellipticPiInc c n (Real.pi - θ) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (ellipticPiIntegrand c n)
      MeasureTheory.volume a b :=
    fun a b => (continuous_ellipticPiIntegrand hc hn).intervalIntegrable a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (f := ellipticPiIntegrand c n)
    (a := (0 : ℝ)) (b := Real.pi / 2) (c := θ) (hint 0 _) (hint _ _)
  change (∫ x in (0 : ℝ)..θ, ellipticPiIntegrand c n x)
    = 2 * ellipticPi c n - ellipticPiInc c n (Real.pi - θ)
  rw [← hsplit]
  have hsecond : (∫ x in Real.pi / 2..θ, ellipticPiIntegrand c n x)
      = ellipticPi c n - ellipticPiInc c n (Real.pi - θ) := by
    calc (∫ x in Real.pi / 2..θ, ellipticPiIntegrand c n x)
        = ∫ x in Real.pi / 2..θ, ellipticPiIntegrand c n (Real.pi - x) := by
          refine intervalIntegral.integral_congr fun x _ => ?_
          exact (ellipticPiIntegrand_pi_sub c n x).symm
      _ = ∫ x in Real.pi - θ..Real.pi - Real.pi / 2,
            ellipticPiIntegrand c n x :=
          intervalIntegral.integral_comp_sub_left
            (a := Real.pi / 2) (b := θ) (ellipticPiIntegrand c n) Real.pi
      _ = ∫ x in Real.pi - θ..Real.pi / 2, ellipticPiIntegrand c n x := by
          rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
      _ = (∫ x in (0 : ℝ)..Real.pi / 2, ellipticPiIntegrand c n x)
            - (∫ x in (0 : ℝ)..Real.pi - θ, ellipticPiIntegrand c n x) := by
          have h := intervalIntegral.integral_add_adjacent_intervals
            (μ := MeasureTheory.volume) (f := ellipticPiIntegrand c n)
            (a := (0 : ℝ)) (b := Real.pi - θ) (c := Real.pi / 2)
            (hint 0 _) (hint _ _)
          rw [eq_sub_iff_add_eq]
          simpa [add_comm] using h
      _ = ellipticPi c n - ellipticPiInc c n (Real.pi - θ) := by
          change (∫ x in (0 : ℝ)..Real.pi / 2, ellipticPiIntegrand c n x)
              - (∫ x in (0 : ℝ)..Real.pi - θ, ellipticPiIntegrand c n x)
            = (∫ x in (0 : ℝ)..Real.pi / 2, ellipticPiIntegrand c n x)
              - (∫ x in (0 : ℝ)..Real.pi - θ, ellipticPiIntegrand c n x)
          rfl
  rw [hsecond]
  change ellipticPi c n + (ellipticPi c n - ellipticPiInc c n (Real.pi - θ))
    = 2 * ellipticPi c n - ellipticPiInc c n (Real.pi - θ)
  ring

theorem ellipticPiInc_Pconstructible_circ_upper {c n Φ : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) (hΦP : PConstructible Φ) (hc0 : 0 < c) (hc : c < 1)
    (hcn : c < n) (hn : n < 1) : PConstructible (ellipticPiInc c n Φ) := by
  obtain ⟨m, h0, hpi⟩ := exists_int_half_turns Φ
  set θ := Φ - m * Real.pi with hθdef
  have hθP : PConstructible θ := by
    rw [hθdef]
    exact PConstructible.sub hΦP (PConstructible.mul (int_Pconstructible m) pi_Pconstructible)
  have hkey := ellipticPiInc_add_int_mul_pi hc hn θ m
  have hΦ_eq : θ + m * Real.pi = Φ := by rw [hθdef]; ring
  rw [hΦ_eq] at hkey
  have hK : PConstructible (ellipticPi c n) :=
    ellipticPi_Pconstructible hcP hnP hc0 hc hn
  have hterm : PConstructible (m * (2 * ellipticPi c n)) :=
    PConstructible.mul (int_Pconstructible m)
      (PConstructible.mul two_Pconstructible hK)
  rw [hkey]
  rcases le_or_gt θ (Real.pi / 2) with hle | hgt
  · exact PConstructible.add
      (ellipticPiInc_Pconstructible_circ_upper_Icc hcP hnP hθP hc0 hc hcn hn h0 hle) hterm
  · have h1 : Real.pi / 2 ≤ θ := hgt.le
    have hsym := ellipticPiInc_eq_two_complete_sub hc hn h1 hpi
    rw [hsym]
    have hθ'P : PConstructible (Real.pi - θ) :=
      PConstructible.sub pi_Pconstructible hθP
    have hpart : PConstructible (ellipticPiInc c n (Real.pi - θ)) :=
      ellipticPiInc_Pconstructible_circ_upper_Icc hcP hnP hθ'P hc0 hc hcn hn
        (by linarith) (by linarith)
    exact PConstructible.add
      (PConstructible.sub (PConstructible.mul two_Pconstructible hK) hpart) hterm

end Pconstructible
