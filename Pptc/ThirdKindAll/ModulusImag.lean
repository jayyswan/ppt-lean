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
import Mathlib.Topology.Order.OrderClosed

/-! # Pptc.ThirdKindAll.ModulusImag

The imaginary-modulus transformation. For `c < 0` the substitution

  `tan ψ = √(1 - c) · tan θ`

carries the third-kind differential at `(c, n)` to

  `dψ · Δ'(ψ) / (1 - n' sin²ψ)`,   `c' = c/(c-1)`,  `n' = (n-c)/(1-c)`.

The extra factor `Δ'` — absent for the first kind — splits the transformed integrand into a
first-kind and a third-kind piece:

  `Π(c, n, θ) = (1/√(1-c)) · ( (n/(n-c)) Π(c', n', ψ) - (c/(n-c)) F(c', ψ) )`.

Since `c' ∈ (0, 1)`, this reduces every negative modulus to the standard case. The
substitution is smooth only for `|θ| < π/2`; for `n < 1` the periodic reduction
(`ellipticPiInc_Pconstructible_of_base'`) handles the remaining upper limits, while for
`n ≥ 1` the no-pole hypothesis already forces `|Φ| < π/2`. -/

namespace Pconstructible

open Filter
open scoped Topology

/-- The imaginary-modulus scale `√(1 - c)`, which exceeds `1` for `c < 0`. -/
noncomputable def imagLam (c : ℝ) : ℝ := Real.sqrt (1 - c)

/-- The transformed modulus `c / (c - 1)`, in `(0, 1)` for `c < 0`. -/
noncomputable def imagC (c : ℝ) : ℝ := c / (c - 1)

/-- The transformed characteristic `(n - c) / (1 - c)`. -/
noncomputable def imagN (c n : ℝ) : ℝ := (n - c) / (1 - c)

/-- The transformed angle, `arctan (√(1-c) tan θ)`. -/
noncomputable def imagPsi (c θ : ℝ) : ℝ := Real.arctan (imagLam c * Real.tan θ)

theorem imagLam_sq {c : ℝ} (hc : c < 0) : imagLam c ^ 2 = 1 - c := by
  rw [imagLam, Real.sq_sqrt (by linarith)]

theorem imagLam_pos {c : ℝ} (hc : c < 0) : 0 < imagLam c :=
  Real.sqrt_pos.mpr (by linarith)

theorem imagC_pos {c : ℝ} (hc : c < 0) : 0 < imagC c := by
  rw [imagC]
  exact div_pos_of_neg_of_neg hc (by linarith)

theorem imagC_lt_one {c : ℝ} (hc : c < 0) : imagC c < 1 := by
  have h : imagC c = 1 + 1 / (c - 1) := by
    rw [imagC]
    have hc1 : c - 1 ≠ 0 := by linarith
    field_simp [hc1]
    ring
  rw [h]
  have hneg : 1 / (c - 1) < 0 := div_neg_of_pos_of_neg one_pos (by linarith)
  linarith

theorem imagN_lt_one {c n : ℝ} (hc : c < 0) (hn : n < 1) : imagN c n < 1 := by
  rw [imagN, div_lt_one (by linarith)]
  linarith

theorem imagPsi_zero (c : ℝ) : imagPsi c 0 = 0 := by
  simp [imagPsi]

theorem one_sub_mul_sin_sq_pos_of_neg {c θ : ℝ} (hc : c < 0) :
    0 < 1 - c * Real.sin θ ^ 2 := by
  have hs := Real.sin_sq_le_one θ
  have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  nlinarith

private theorem continuous_one_sub_mul_sin_sq (a : ℝ) :
    Continuous (fun x : ℝ => 1 - a * Real.sin x ^ 2) :=
  continuous_const.sub (continuous_const.mul (Real.continuous_sin.pow 2))

/-- For `n < 1` the third-kind denominator never vanishes: `1 - n sin²ψ ≥ 1 - n > 0`. -/
theorem one_sub_mul_sin_sq_ne_zero_of_lt_one {n ψ : ℝ} (hn : n < 1) :
    1 - n * Real.sin ψ ^ 2 ≠ 0 := by
  have hpos : 0 < 1 - n * Real.sin ψ ^ 2 := by
    rcases le_total n 0 with hn0 | hn0
    · nlinarith [sq_nonneg (Real.sin ψ)]
    · have := mul_le_mul_of_nonneg_left (Real.sin_sq_le_one ψ) hn0
      nlinarith
  exact hpos.ne'

/-- The denominator appearing in the derivative of `imagPsi`. -/
theorem one_add_imagLam_mul_tan_sq {c θ : ℝ} (hc : c < 0) (hcos : Real.cos θ ≠ 0) :
    1 + (imagLam c * Real.tan θ) ^ 2
      = (1 - c * Real.sin θ ^ 2) / Real.cos θ ^ 2 := by
  rw [Real.tan_eq_sin_div_cos, mul_pow, div_pow, imagLam_sq hc]
  have hw : Real.cos θ ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  field_simp [hw]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The sine of the transformed angle. -/
theorem sin_imagPsi {c θ : ℝ} (hc : c < 0) (hcos : 0 < Real.cos θ) :
    Real.sin (imagPsi c θ) = imagLam c * Real.sin θ / ellipticEIntegrand c θ := by
  have hden : 0 < 1 - c * Real.sin θ ^ 2 := one_sub_mul_sin_sq_pos_of_neg hc
  have hE : 0 < ellipticEIntegrand c θ := Real.sqrt_pos.mpr hden
  rw [imagPsi, Real.sin_arctan, one_add_imagLam_mul_tan_sq hc hcos.ne']
  rw [show (1 - c * Real.sin θ ^ 2) / Real.cos θ ^ 2
      = (ellipticEIntegrand c θ / Real.cos θ) ^ 2 by
    rw [div_pow, ellipticEIntegrand, Real.sq_sqrt hden.le]]
  rw [Real.sqrt_sq (by positivity), Real.tan_eq_sin_div_cos]
  field_simp [hcos.ne', hE.ne']

/-- The cosine of the transformed angle. -/
theorem cos_imagPsi {c θ : ℝ} (hc : c < 0) (hcos : 0 < Real.cos θ) :
    Real.cos (imagPsi c θ) = Real.cos θ / ellipticEIntegrand c θ := by
  have hden : 0 < 1 - c * Real.sin θ ^ 2 := one_sub_mul_sin_sq_pos_of_neg hc
  have hE : 0 < ellipticEIntegrand c θ := Real.sqrt_pos.mpr hden
  rw [imagPsi, Real.cos_arctan, one_add_imagLam_mul_tan_sq hc hcos.ne']
  rw [show (1 - c * Real.sin θ ^ 2) / Real.cos θ ^ 2
      = (ellipticEIntegrand c θ / Real.cos θ) ^ 2 by
    rw [div_pow, ellipticEIntegrand, Real.sq_sqrt hden.le]]
  rw [Real.sqrt_sq (by positivity)]
  field_simp [hE.ne', hcos.ne']

/-- `sin²` of the transformed angle. -/
theorem sin_imagPsi_sq {c θ : ℝ} (hc : c < 0) (hcos : 0 < Real.cos θ) :
    Real.sin (imagPsi c θ) ^ 2
      = (1 - c) * Real.sin θ ^ 2 / (1 - c * Real.sin θ ^ 2) := by
  have hden : 0 < 1 - c * Real.sin θ ^ 2 := one_sub_mul_sin_sq_pos_of_neg hc
  rw [sin_imagPsi hc hcos, div_pow, mul_pow, ellipticEIntegrand, Real.sq_sqrt hden.le,
    imagLam_sq hc]

/-- The characteristic numerator transforms exactly. -/
theorem one_sub_imagN_mul_sin_sq {c n θ : ℝ} (hc : c < 0) (hcos : 0 < Real.cos θ) :
    1 - imagN c n * Real.sin (imagPsi c θ) ^ 2
      = (1 - n * Real.sin θ ^ 2) / (1 - c * Real.sin θ ^ 2) := by
  rw [sin_imagPsi_sq hc hcos, imagN]
  have hden : 1 - c * Real.sin θ ^ 2 ≠ 0 := (one_sub_mul_sin_sq_pos_of_neg hc).ne'
  have h1c : (1 : ℝ) - c ≠ 0 := by linarith
  field_simp [hden, h1c]
  ring

/-- The modulus numerator transforms to a reciprocal. -/
theorem one_sub_imagC_mul_sin_sq {c θ : ℝ} (hc : c < 0) (hcos : 0 < Real.cos θ) :
    1 - imagC c * Real.sin (imagPsi c θ) ^ 2 = 1 / (1 - c * Real.sin θ ^ 2) := by
  rw [sin_imagPsi_sq hc hcos, imagC]
  have hden : 1 - c * Real.sin θ ^ 2 ≠ 0 := (one_sub_mul_sin_sq_pos_of_neg hc).ne'
  have hcne : c ≠ 0 := ne_of_lt hc
  have hc1 : c - 1 ≠ 0 := by linarith
  field_simp [hden, hcne, hc1]
  ring

/-- The transformed `Δ` is the reciprocal of the original one. -/
theorem ellipticEIntegrand_imagC_imagPsi {c θ : ℝ} (hc : c < 0) (hcos : 0 < Real.cos θ) :
    ellipticEIntegrand (imagC c) (imagPsi c θ) = 1 / ellipticEIntegrand c θ := by
  simp only [ellipticEIntegrand, one_sub_imagC_mul_sin_sq hc hcos, one_div, Real.sqrt_inv]

/-- The derivative of the transformed angle: `ψ' = √(1-c) / Δ²`. -/
theorem hasDerivAt_imagPsi {c θ : ℝ} (hc : c < 0) (hcos : Real.cos θ ≠ 0) :
    HasDerivAt (imagPsi c) (imagLam c / ellipticEIntegrand c θ ^ 2) θ := by
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos
  have harg : HasDerivAt (fun x : ℝ => imagLam c * Real.tan x)
      (imagLam c * (1 / Real.cos θ ^ 2)) θ := htan.const_mul (imagLam c)
  have harc := (Real.hasDerivAt_arctan (imagLam c * Real.tan θ)).comp θ harg
  refine harc.congr_deriv ?_
  have hden : 0 < 1 - c * Real.sin θ ^ 2 := one_sub_mul_sin_sq_pos_of_neg hc
  have hE : 0 < ellipticEIntegrand c θ := Real.sqrt_pos.mpr hden
  rw [one_add_imagLam_mul_tan_sq hc hcos, ellipticEIntegrand, Real.sq_sqrt hden.le]
  field_simp [hcos, hden.ne', hE.ne']

/-- The transformed angle is monotone on the path. -/
theorem imagPsi_monotoneOn {c Φ : ℝ} (hc : c < 0) (hΦ : |Φ| < Real.pi / 2) :
    MonotoneOn (imagPsi c) (Set.uIcc (0 : ℝ) Φ) := by
  have hcont : ContinuousOn (imagPsi c) (Set.uIcc (0 : ℝ) Φ) := fun θ hθ =>
    (hasDerivAt_imagPsi hc (cos_pos_of_mem_uIcc hΦ hθ).ne').continuousAt.continuousWithinAt
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun θ : ℝ => imagLam c / ellipticEIntegrand c θ ^ 2)
    (convex_uIcc (0 : ℝ) Φ) hcont ?_ ?_
  · intro θ hθ
    exact (hasDerivAt_imagPsi hc
      (cos_pos_of_mem_uIcc hΦ (interior_subset hθ)).ne').hasDerivWithinAt
  · intro θ hθ
    exact div_nonneg (imagLam_pos hc).le (sq_nonneg _)

/-- The image of the path is the interval between the endpoint images. -/
theorem imagPsi_image_uIcc {c Φ : ℝ} (hc : c < 0) (hΦ : |Φ| < Real.pi / 2) :
    imagPsi c '' Set.uIcc (0 : ℝ) Φ = Set.uIcc 0 (imagPsi c Φ) := by
  have hcont : ContinuousOn (imagPsi c) (Set.uIcc (0 : ℝ) Φ) := fun θ hθ =>
    (hasDerivAt_imagPsi hc (cos_pos_of_mem_uIcc hΦ hθ).ne').continuousAt.continuousWithinAt
  simpa [imagPsi_zero] using hcont.image_uIcc_of_monotoneOn (imagPsi_monotoneOn hc hΦ)

/-- The pointwise splitting of the transformed integrand into first and third kind. -/
theorem imag_g_eq {c n σ : ℝ} (hc : c < 0) (hnc : n ≠ c)
    (hne' : 1 - imagN c n * Real.sin σ ^ 2 ≠ 0) :
    ellipticEIntegrand (imagC c) σ / (1 - imagN c n * Real.sin σ ^ 2)
      = (n / (n - c)) * ellipticPiIntegrand (imagC c) (imagN c n) σ
        - (c / (n - c)) * ellipticFIntegrand (imagC c) σ := by
  have hEpos := ellipticEIntegrand_pos (imagC_lt_one hc) σ
  have hnsub : n - c ≠ 0 := sub_ne_zero.mpr hnc
  have hc1 : c - 1 ≠ 0 := by linarith
  have h1c : (1 : ℝ) - c ≠ 0 := by linarith
  have hcoef : -imagC c * (n - c) = c * imagN c n := by
    rw [imagC, imagN]
    field_simp [hc1, h1c]
    ring
  have hcoef' : -imagC c * n + imagC c * c - c * imagN c n = 0 := by
    linear_combination hcoef
  have hnum : ellipticEIntegrand (imagC c) σ ^ 2 * (n - c)
      = n - c + c * imagN c n * Real.sin σ ^ 2 := by
    rw [ellipticEIntegrand_sq (imagC_lt_one hc)]
    linear_combination (Real.sin σ ^ 2) * hcoef
  rw [ellipticPiIntegrand, ellipticFIntegrand]
  field_simp [hne', hEpos.ne', hnsub]
  rw [ellipticEIntegrand_sq (imagC_lt_one hc)]
  nlinarith [hcoef']

/-- **The imaginary-modulus transformation.** For `c < 0`, `n ≠ c` and `|Φ| < π/2`,
`Π(c,n,Φ) = (1/√(1-c)) ((n/(n-c)) Π(c',n',ψ) - (c/(n-c)) F(c',ψ))`. -/
theorem ellipticPiInc_imag_of_abs_lt {c n Φ : ℝ} (hc : c < 0) (hnc : n ≠ c)
    (hΦ : |Φ| < Real.pi / 2)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    ellipticPiInc c n Φ
      = (1 / imagLam c) * ((n / (n - c))
            * ellipticPiInc (imagC c) (imagN c n) (imagPsi c Φ)
          - (c / (n - c)) * ellipticF (imagC c) (imagPsi c Φ)) := by
  have hcos : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 0 < Real.cos θ :=
    fun θ hθ => cos_pos_of_mem_uIcc hΦ hθ
  have hc' : imagC c < 1 := imagC_lt_one hc
  have hne' : ∀ σ ∈ Set.uIcc (0 : ℝ) (imagPsi c Φ),
      1 - imagN c n * Real.sin σ ^ 2 ≠ 0 := by
    intro σ hσ
    rw [← imagPsi_image_uIcc hc hΦ] at hσ
    obtain ⟨θ, hθ, rfl⟩ := hσ
    rw [one_sub_imagN_mul_sin_sq hc (hcos θ hθ)]
    exact div_ne_zero (hne θ hθ) (one_sub_mul_sin_sq_pos_of_neg hc).ne'
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ,
      HasDerivAt (imagPsi c) (imagLam c / ellipticEIntegrand c θ ^ 2) θ :=
    fun θ hθ => hasDerivAt_imagPsi hc (hcos θ hθ).ne'
  have hcont : ContinuousOn (fun θ : ℝ => imagLam c / ellipticEIntegrand c θ ^ 2)
      (Set.uIcc (0 : ℝ) Φ) := by
    refine ContinuousOn.div continuousOn_const (by
      exact (continuous_ellipticEIntegrand c).continuousOn.pow 2) ?_
    intro θ _
    exact pow_ne_zero 2 (Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos_of_neg hc)).ne'
  have hg : ContinuousOn (fun σ : ℝ => ellipticEIntegrand (imagC c) σ
        / (1 - imagN c n * Real.sin σ ^ 2)) (imagPsi c '' Set.uIcc (0 : ℝ) Φ) := by
    rintro σ ⟨θ, hθ, rfl⟩
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div (continuous_ellipticEIntegrand (imagC c)).continuousAt ?_ ?_
    · exact (continuous_one_sub_mul_sin_sq (imagN c n)).continuousAt
    · rw [one_sub_imagN_mul_sin_sq hc (hcos θ hθ)]
      exact div_ne_zero (hne θ hθ) (one_sub_mul_sin_sq_pos_of_neg hc).ne'
  have hsub := intervalIntegral.integral_deriv_smul_comp' (a := (0 : ℝ)) (b := Φ)
    (f := imagPsi c) (f' := fun θ : ℝ => imagLam c / ellipticEIntegrand c θ ^ 2)
    (g := fun σ : ℝ => ellipticEIntegrand (imagC c) σ
      / (1 - imagN c n * Real.sin σ ^ 2)) hderiv hcont hg
  have hsub' : (∫ θ in (0 : ℝ)..Φ, (imagLam c / ellipticEIntegrand c θ ^ 2)
      * (ellipticEIntegrand (imagC c) (imagPsi c θ)
          / (1 - imagN c n * Real.sin (imagPsi c θ) ^ 2)))
      = ∫ σ in (0 : ℝ)..imagPsi c Φ,
        ellipticEIntegrand (imagC c) σ / (1 - imagN c n * Real.sin σ ^ 2) := by
    simpa [imagPsi_zero, Function.comp_apply, smul_eq_mul] using hsub
  have hcongr : (∫ θ in (0 : ℝ)..Φ, (imagLam c / ellipticEIntegrand c θ ^ 2)
      * (ellipticEIntegrand (imagC c) (imagPsi c θ)
          / (1 - imagN c n * Real.sin (imagPsi c θ) ^ 2)))
      = ∫ θ in (0 : ℝ)..Φ, imagLam c * ellipticPiIntegrand c n θ := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    have hE : 0 < ellipticEIntegrand c θ := Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos_of_neg hc)
    rw [ellipticEIntegrand_imagC_imagPsi hc (hcos θ hθ),
      one_sub_imagN_mul_sin_sq hc (hcos θ hθ), ellipticPiIntegrand]
    field_simp [hE.ne', hne θ hθ, (hcos θ hθ).ne', (one_sub_mul_sin_sq_pos_of_neg hc).ne']
    rw [ellipticEIntegrand, Real.sq_sqrt (one_sub_mul_sin_sq_pos_of_neg hc).le]
    ring
  have hIntPi : IntervalIntegrable (ellipticPiIntegrand (imagC c) (imagN c n))
      MeasureTheory.volume 0 (imagPsi c Φ) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (continuous_one_sub_mul_sin_sq (imagN c n)).continuousOn.mul
        (continuous_ellipticEIntegrand (imagC c)).continuousOn
    · exact fun σ hσ => mul_ne_zero (hne' σ hσ)
        (ellipticEIntegrand_pos hc' σ).ne'
  have hIntF : IntervalIntegrable (ellipticFIntegrand (imagC c)) MeasureTheory.volume 0
      (imagPsi c Φ) :=
    (continuous_ellipticFIntegrand hc').intervalIntegrable _ _
  have hgval : (∫ σ in (0 : ℝ)..imagPsi c Φ,
        ellipticEIntegrand (imagC c) σ / (1 - imagN c n * Real.sin σ ^ 2))
      = (n / (n - c)) * ellipticPiInc (imagC c) (imagN c n) (imagPsi c Φ)
        - (c / (n - c)) * ellipticF (imagC c) (imagPsi c Φ) := by
    rw [show (∫ σ in (0 : ℝ)..imagPsi c Φ,
          ellipticEIntegrand (imagC c) σ / (1 - imagN c n * Real.sin σ ^ 2))
        = ∫ σ in (0 : ℝ)..imagPsi c Φ,
          ((n / (n - c)) * ellipticPiIntegrand (imagC c) (imagN c n) σ
            - (c / (n - c)) * ellipticFIntegrand (imagC c) σ) from
      intervalIntegral.integral_congr fun σ hσ => imag_g_eq hc hnc (hne' σ hσ)]
    rw [intervalIntegral.integral_sub (hIntPi.const_mul _) (hIntF.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      ellipticPiInc, ellipticF]
  have hkey : imagLam c * ellipticPiInc c n Φ
      = (n / (n - c)) * ellipticPiInc (imagC c) (imagN c n) (imagPsi c Φ)
        - (c / (n - c)) * ellipticF (imagC c) (imagPsi c Φ) := by
    calc imagLam c * ellipticPiInc c n Φ
        = ∫ θ in (0 : ℝ)..Φ, imagLam c * ellipticPiIntegrand c n θ := by
          rw [ellipticPiInc, intervalIntegral.integral_const_mul]
      _ = ∫ θ in (0 : ℝ)..Φ, (imagLam c / ellipticEIntegrand c θ ^ 2)
            * (ellipticEIntegrand (imagC c) (imagPsi c θ)
              / (1 - imagN c n * Real.sin (imagPsi c θ) ^ 2)) := by rw [hcongr]
      _ = _ := hsub'
      _ = _ := hgval
  rw [eq_comm, ← hkey]
  field_simp [(imagLam_pos hc).ne']

/-- **The complete integral at imaginary modulus.** -/
theorem ellipticPi_imag {c n : ℝ} (hc : c < 0) (hn : n < 1) (hnc : n ≠ c) :
    ellipticPi c n = (1 / imagLam c) *
      ((n / (n - c)) * ellipticPi (imagC c) (imagN c n)
        - (c / (n - c)) * ellipticF (imagC c) (Real.pi / 2)) := by
  have hne_pi : 1 - n * Real.sin (Real.pi / 2) ^ 2 ≠ 0 := by
    rw [Real.sin_pi_div_two]
    nlinarith
  have hcont : Continuous (ellipticPiIntegrand c n) :=
    continuous_ellipticPiIntegrand (by linarith) hn
  have hL0 := hasDerivAt_ellipticPiInc_of_ne (c := c) (n := n) (θ := Real.pi / 2)
    (by linarith) (hcont.intervalIntegrable 0 _) hne_pi
  have hL : Tendsto (ellipticPiInc c n) (𝓝[<] (Real.pi / 2))
      (𝓝 (ellipticPi c n)) := by
    simpa [ellipticPi, ellipticPiInc] using
      hL0.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hn' : imagN c n < 1 := imagN_lt_one hc hn
  have hne_pi' : 1 - imagN c n * Real.sin (Real.pi / 2) ^ 2 ≠ 0 := by
    rw [Real.sin_pi_div_two]
    nlinarith
  have hcont' : Continuous (ellipticPiIntegrand (imagC c) (imagN c n)) :=
    continuous_ellipticPiIntegrand (imagC_lt_one hc) hn'
  have hPi0 := hasDerivAt_ellipticPiInc_of_ne (c := imagC c) (n := imagN c n)
    (θ := Real.pi / 2) (imagC_lt_one hc) (hcont'.intervalIntegrable 0 _) hne_pi'
  have hPi : Tendsto (ellipticPiInc (imagC c) (imagN c n))
      (𝓝 (Real.pi / 2)) (𝓝 (ellipticPi (imagC c) (imagN c n))) := by
    simpa [ellipticPi, ellipticPiInc] using hPi0.continuousAt.tendsto
  have hF0 := hasDerivAt_ellipticF (imagC_lt_one hc) (Real.pi / 2)
  have hF : Tendsto (fun ψ : ℝ => ellipticF (imagC c) ψ) (𝓝 (Real.pi / 2))
      (𝓝 (ellipticF (imagC c) (Real.pi / 2))) := hF0.continuousAt.tendsto
  have hpsi : Tendsto (imagPsi c) (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) := by
    have htan : Tendsto (fun θ : ℝ => imagLam c * Real.tan θ)
        (𝓝[<] (Real.pi / 2)) atTop :=
      Real.tendsto_tan_pi_div_two.const_mul_atTop (imagLam_pos hc)
    have := (Real.tendsto_arctan_atTop.comp htan).mono_right nhdsWithin_le_nhds
    unfold imagPsi
    exact this
  have hcomp : Tendsto (fun θ : ℝ => (1 / imagLam c) * ((n / (n - c))
        * ellipticPiInc (imagC c) (imagN c n) (imagPsi c θ)
        - (c / (n - c)) * ellipticF (imagC c) (imagPsi c θ)))
      (𝓝[<] (Real.pi / 2))
      (𝓝 ((1 / imagLam c) * ((n / (n - c)) * ellipticPi (imagC c) (imagN c n)
        - (c / (n - c)) * ellipticF (imagC c) (Real.pi / 2)))) :=
    (((hPi.comp hpsi).const_mul _).sub ((hF.comp hpsi).const_mul _)).const_mul _
  have heq : (fun θ : ℝ => ellipticPiInc c n θ) =ᶠ[𝓝[<] (Real.pi / 2)]
      (fun θ : ℝ => (1 / imagLam c) * ((n / (n - c))
        * ellipticPiInc (imagC c) (imagN c n) (imagPsi c θ)
        - (c / (n - c)) * ellipticF (imagC c) (imagPsi c θ))) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by positivity)] with θ hθ
    have habs : |θ| < Real.pi / 2 := by
      rw [abs_of_pos hθ.1]
      exact hθ.2
    exact ellipticPiInc_imag_of_abs_lt hc hnc habs (fun _ _ =>
      one_sub_mul_sin_sq_ne_zero_of_lt_one hn)
  exact tendsto_nhds_unique hL (hcomp.congr' heq.symm)

/-- **The imaginary-modulus case of the headline theorem.** -/
theorem ellipticPiInc_Pconstructible_imag {c n Φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hc : c < 0)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc c n Φ) := by
  by_cases hnc : n = c
  · subst hnc
    exact ellipticPiInc_self_Pconstructible hcP hΦP (by linarith)
  · have hcP' : PConstructible (imagC c) := by
      rw [imagC]
      pconstructible
    have hlamP : PConstructible (imagLam c) := by
      rw [imagLam]
      pconstructible
    have hcoef : PConstructible (n / (n - c)) := by pconstructible
    have hcoef2 : PConstructible (c / (n - c)) := by pconstructible
    rcases lt_or_ge n 1 with hn | hn
    · have hK : PConstructible (ellipticPi c n) := by
        rw [ellipticPi_imag hc hn hnc]
        have hnP' : PConstructible (imagN c n) := by
          rw [imagN]
          pconstructible
        have hPiP := ellipticPi_Pconstructible hcP' hnP' (imagC_pos hc) (imagC_lt_one hc)
          (imagN_lt_one hc hn)
        have hFP := ellipticF_Pconstructible hcP' pi_div_two_Pconstructible (imagC_lt_one hc)
        exact PConstructible.mul (by simpa [one_div] using inv_Pconstructible hlamP)
          (PConstructible.sub (PConstructible.mul hcoef hPiP)
            (PConstructible.mul hcoef2 hFP))
      refine ellipticPiInc_Pconstructible_of_base' hcP hnP hΦP (by linarith) hn hK ?_
      intro θ hθP h0 hlt
      have hθ : |θ| < Real.pi / 2 := by
        rw [abs_of_nonneg h0]
        exact hlt
      have hneθ : ∀ ψ ∈ Set.uIcc (0 : ℝ) θ, 1 - n * Real.sin ψ ^ 2 ≠ 0 :=
        fun _ _ => one_sub_mul_sin_sq_ne_zero_of_lt_one hn
      rw [ellipticPiInc_imag_of_abs_lt hc hnc hθ hneθ]
      have hnP' : PConstructible (imagN c n) := by
        rw [imagN]
        pconstructible
      have hψP : PConstructible (imagPsi c θ) := by
        rw [imagPsi, imagLam]
        pconstructible
      have hne' : ∀ σ ∈ Set.uIcc (0 : ℝ) (imagPsi c θ),
          1 - imagN c n * Real.sin σ ^ 2 ≠ 0 :=
        fun _ _ => one_sub_mul_sin_sq_ne_zero_of_lt_one (imagN_lt_one hc hn)
      have hPiP := ellipticPiInc_Pconstructible_standard hcP' hnP' hψP
        (imagC_pos hc) (imagC_lt_one hc) hne'
      have hFP := ellipticF_Pconstructible hcP' hψP (imagC_lt_one hc)
      exact PConstructible.mul (by simpa [one_div] using inv_Pconstructible hlamP)
        (PConstructible.sub (PConstructible.mul hcoef hPiP)
          (PConstructible.mul hcoef2 hFP))
    · have habs := abs_lt_pi_div_two_of_one_le hn hne
      rw [ellipticPiInc_imag_of_abs_lt hc hnc habs hne]
      have hnP' : PConstructible (imagN c n) := by
        rw [imagN]
        pconstructible
      have hψP : PConstructible (imagPsi c Φ) := by
        rw [imagPsi, imagLam]
        pconstructible
      have hne' : ∀ σ ∈ Set.uIcc (0 : ℝ) (imagPsi c Φ),
          1 - imagN c n * Real.sin σ ^ 2 ≠ 0 := by
        intro σ hσ
        rw [← imagPsi_image_uIcc hc habs] at hσ
        obtain ⟨θ, hθ, rfl⟩ := hσ
        rw [one_sub_imagN_mul_sin_sq hc (cos_pos_of_mem_uIcc habs hθ)]
        exact div_ne_zero (hne θ hθ) (one_sub_mul_sin_sq_pos_of_neg hc).ne'
      have hPiP := ellipticPiInc_Pconstructible_standard hcP' hnP' hψP
        (imagC_pos hc) (imagC_lt_one hc) hne'
      have hFP := ellipticF_Pconstructible hcP' hψP (imagC_lt_one hc)
      exact PConstructible.mul (by simpa [one_div] using inv_Pconstructible hlamP)
        (PConstructible.sub (PConstructible.mul hcoef hPiP)
          (PConstructible.mul hcoef2 hFP))

end Pconstructible
