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

import Pptc.ThirdKindAll.Period
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Pptc.ThirdKindAll.Pseudo

The pseudo-elliptic characteristics `n = 1 ± k'`, `k' = √(1 - c)`.

These are the fixed points of `n ↦ (c - n)/(1 - n)`, and they are exactly the locus where the
coefficient `thirdKindPiCoeff` of the Bézier construction vanishes. There the incomplete
third-kind integral has a closed form in `F` and `artanh`. -/

namespace Pconstructible

/-- The derivative of `Real.artanh`, which is not in Mathlib. -/
theorem hasDerivAt_artanh {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have hden : 1 - x ≠ 0 := by linarith
  have hg : HasDerivAt (fun y : ℝ => (1 + y) / (1 - y)) (2 / (1 - x) ^ 2) x := by
    have hnum : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have hden' : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    exact (hnum.div hden' hden).congr_deriv (by ring)
  have hgpos : 0 < (1 + x) / (1 - x) := div_pos (by linarith) (by linarith)
  have hsqrt := hg.sqrt hgpos.ne'
  have hlog := HasDerivAt.log hsqrt (Real.sqrt_pos.mpr hgpos).ne'
  have hfun : Real.artanh = fun y : ℝ => Real.log (Real.sqrt ((1 + y) / (1 - y))) := by
    funext y; rw [Real.artanh]
  rw [hfun]
  refine hlog.congr_deriv ?_
  field_simp [hgpos.ne']
  rw [Real.sq_sqrt hgpos.le]
  have hx2 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx0, hx1]
  field_simp [hx2]
  ring

/-- The generic pseudo-elliptic antiderivative, at characteristic `n = 1 + m`. -/
noncomputable def pseudoAnti (c m φ : ℝ) : ℝ :=
  (-(1 - m) * ellipticF c φ
    + Real.artanh ((1 + m) * Real.sin φ * Real.cos φ / ellipticEIntegrand c φ)) / (2 * m)

theorem pseudoAnti_zero (c m : ℝ) : pseudoAnti c m 0 = 0 := by
  simp [pseudoAnti, ellipticF]

/-- The core derivative computation, for arbitrary `m` with `m² = 1 - c`. -/
theorem hasDerivAt_pseudoAnti {c m φ : ℝ} (hm2 : m ^ 2 = 1 - c) (hm0 : m ≠ 0)
    (hpole : (1 + m) * Real.sin φ ^ 2 < 1) :
    HasDerivAt (pseudoAnti c m) (ellipticPiIntegrand c (1 + m) φ) φ := by
  have hc : c < 1 := by nlinarith [sq_pos_of_ne_zero hm0]
  have hE := ellipticEIntegrand_pos hc φ
  have hE2 := ellipticEIntegrand_sq hc φ
  have hF := hasDerivAt_ellipticF hc φ
  have hΔ' : HasDerivAt (ellipticEIntegrand c) (-(2 * c * Real.sin φ * Real.cos φ)
      / (2 * ellipticEIntegrand c φ)) φ :=
    hasDerivAt_ellipticEIntegrand c φ (one_sub_mul_sin_sq_pos hc φ).ne'
  let A : ℝ := (1 + m) * Real.sin φ * Real.cos φ / ellipticEIntegrand c φ
  have hA := ((Real.hasDerivAt_sin φ).mul (Real.hasDerivAt_cos φ)).const_mul (1 + m)
    |>.div hΔ' hE.ne'
  have hcs : 1 - Real.sin φ ^ 2 * c ≠ 0 := by
    have h := (one_sub_mul_sin_sq_pos hc φ).ne'
    rwa [mul_comm] at h
  have hA2 : 1 - A ^ 2
      = (1 - (1 + m) * Real.sin φ ^ 2) ^ 2 / ellipticEIntegrand c φ ^ 2 := by
    dsimp [A]
    rw [div_pow, hE2]
    field_simp [hE.ne', hcs]
    have hc_eq : c = 1 - m ^ 2 := by linarith
    rw [show Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 by
      linarith [Real.sin_sq_add_cos_sq φ], hc_eq]
    ring
  have hAabs : A ^ 2 < 1 := by
    have hpos : 0 < 1 - (1 + m) * Real.sin φ ^ 2 := by linarith
    rw [show A ^ 2 < 1 ↔ 0 < 1 - A ^ 2 by constructor <;> intro h <;> linarith, hA2]
    positivity
  have hA1 : -1 < A := by nlinarith [hAabs]
  have hA2' : A < 1 := by nlinarith [hAabs]
  have hA' := hA
  simp only [Pi.mul_apply, Pi.div_apply] at hA'
  have hval : ((fun y : ℝ => (1 + m) * (Real.sin y * Real.cos y))
      / ellipticEIntegrand c) φ = A := by
    simp [A, Pi.div_apply]
    ring
  have harctan := hasDerivAt_artanh hA1 hA2'
  rw [show A = ((fun y : ℝ => (1 + m) * (Real.sin y * Real.cos y))
      / ellipticEIntegrand c) φ from hval.symm] at harctan
  have harctan' : HasDerivAt (fun y : ℝ => Real.artanh
        ((1 + m) * Real.sin y * Real.cos y / ellipticEIntegrand c y))
      ((1 + m) * (1 - (1 - m) * Real.sin φ ^ 2)
        / (ellipticEIntegrand c φ * (1 - (1 + m) * Real.sin φ ^ 2))) φ := by
    have hcomp := harctan.comp φ hA'
    refine (hcomp.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.EventuallyEq.of_eq (by
        funext y
        simp only [Function.comp_apply, Pi.div_apply]
        ring)
    · rw [hval, hA2]
      have hne : 1 - (1 + m) * Real.sin φ ^ 2 ≠ 0 := by linarith
      field_simp [hE.ne', hne, hcs]
      rw [hE2]
      have hc_eq : c = 1 - m ^ 2 := by linarith
      rw [show Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 by
        linarith [Real.sin_sq_add_cos_sq φ], hc_eq]
      ring
  have htotal := (hF.const_mul (-(1 - m))).add harctan'
  have hdiv := htotal.div_const (2 * m)
  refine hdiv.congr_deriv ?_
  rw [ellipticPiIntegrand]
  have hne : 1 - (1 + m) * Real.sin φ ^ 2 ≠ 0 := by linarith
  simp only [ellipticFIntegrand]
  field_simp [hE.ne', hne, hcs, hm0]
  ring

theorem hasDerivAt_pseudoAntiPlus {c φ : ℝ} (hc : c < 1)
    (hpole : (1 + Real.sqrt (1 - c)) * Real.sin φ ^ 2 < 1) :
    HasDerivAt (pseudoAnti c (Real.sqrt (1 - c)))
      (ellipticPiIntegrand c (1 + Real.sqrt (1 - c)) φ) φ := by
  have hm2 : Real.sqrt (1 - c) ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  have hm0 : Real.sqrt (1 - c) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  exact hasDerivAt_pseudoAnti hm2 hm0 hpole

theorem hasDerivAt_pseudoAntiMinus {c φ : ℝ} (hc : c < 1) :
    HasDerivAt (pseudoAnti c (-(Real.sqrt (1 - c))))
      (ellipticPiIntegrand c (1 - Real.sqrt (1 - c)) φ) φ := by
  have hm2 : (-(Real.sqrt (1 - c))) ^ 2 = 1 - c := by
    rw [neg_sq]; exact Real.sq_sqrt (by linarith)
  have hm0 : (-(Real.sqrt (1 - c))) ≠ 0 :=
    neg_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith)).ne'
  have hlt : (1 - Real.sqrt (1 - c)) * Real.sin φ ^ 2 < 1 := by
    have hmpos : 0 < Real.sqrt (1 - c) := Real.sqrt_pos.mpr (by linarith)
    have hs := Real.sin_sq_le_one φ
    have hs0 : 0 ≤ Real.sin φ ^ 2 := sq_nonneg _
    nlinarith
  simpa [sub_eq_add_neg] using hasDerivAt_pseudoAnti hm2 hm0 hlt

/-- The `n = 1 + k'` closed form. -/
theorem ellipticPiInc_pseudo_plus {c φ : ℝ} (hc : c < 1)
    (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2)
    (hpole : (1 + Real.sqrt (1 - c)) * Real.sin φ ^ 2 < 1) :
    ellipticPiInc c (1 + Real.sqrt (1 - c)) φ
      = pseudoAnti c (Real.sqrt (1 - c)) φ := by
  set m := Real.sqrt (1 - c) with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact Real.sqrt_pos.mpr (by linarith)
  have hm2 : m ^ 2 = 1 - c := by rw [hmdef]; exact Real.sq_sqrt (by linarith)
  have hpole' : (1 + m) * Real.sin φ ^ 2 < 1 := by rw [hmdef]; exact hpole
  have hpole_all : ∀ ψ ∈ Set.uIcc (0 : ℝ) φ,
      (1 + m) * Real.sin ψ ^ 2 < 1 := by
    intro ψ hψ
    rw [Set.uIcc_of_le h0] at hψ
    have hsinle : Real.sin ψ ≤ Real.sin φ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hψ.1, Real.pi_pos])
        (by linarith [hπ]) hψ.2
    have hsin0 : 0 ≤ Real.sin ψ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 (by linarith [hψ.2, hπ, Real.pi_pos])
    have hsq : Real.sin ψ ^ 2 ≤ Real.sin φ ^ 2 := by nlinarith
    nlinarith
  have hcont : ContinuousOn (ellipticPiIntegrand c (1 + m)) (Set.uIcc (0 : ℝ) φ) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (Continuous.continuousOn (by fun_prop)).mul
        (continuous_ellipticEIntegrand c).continuousOn
    · intro ψ hψ
      exact mul_ne_zero (by linarith [hpole_all ψ hψ])
        (ellipticEIntegrand_pos hc ψ).ne'
  have hint : IntervalIntegrable (ellipticPiIntegrand c (1 + m)) MeasureTheory.volume 0 φ :=
    hcont.intervalIntegrable
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ψ hψ => hasDerivAt_pseudoAnti hm2 hmpos.ne' (hpole_all ψ hψ)) hint
  rw [ellipticPiInc, hkey, pseudoAnti_zero, sub_zero]

/-- The `n = 1 - k'` closed form (there is no pole on this branch). -/
theorem ellipticPiInc_pseudo_minus {c φ : ℝ} (hc : c < 1) :
    ellipticPiInc c (1 - Real.sqrt (1 - c)) φ
      = pseudoAnti c (-(Real.sqrt (1 - c))) φ := by
  set m := Real.sqrt (1 - c) with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact Real.sqrt_pos.mpr (by linarith)
  have hm2 : (-m) ^ 2 = 1 - c := by
    rw [neg_sq]; exact Real.sq_sqrt (by linarith)
  have hn : 1 + (-m) < 1 := by linarith
  have hcont := continuous_ellipticPiIntegrand hc hn
  have hpole : ∀ ψ : ℝ, (1 + (-m)) * Real.sin ψ ^ 2 < 1 := by
    intro ψ
    have hs := Real.sin_sq_le_one ψ
    have hs0 : 0 ≤ Real.sin ψ ^ 2 := sq_nonneg _
    nlinarith
  have hint : IntervalIntegrable (ellipticPiIntegrand c (1 + (-m)))
      MeasureTheory.volume 0 φ := hcont.intervalIntegrable 0 φ
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ψ _ => hasDerivAt_pseudoAnti hm2 (neg_ne_zero.mpr hmpos.ne') (hpole ψ)) hint
  change ellipticPiInc c (1 + (-m)) φ = pseudoAnti c (-m) φ
  rw [ellipticPiInc, hkey, pseudoAnti_zero, sub_zero]

/-- `artanh` of a P-constructible number in `(-1,1)`. -/
theorem artanh_Pconstructible {x : ℝ} (hxP : PConstructible x)
    (hx0 : -1 < x) (hx1 : x < 1) : PConstructible (Real.artanh x) := by
  rw [Real.artanh]
  refine log_Pconstructible ?_ ?_
  · pconstructible
  · exact Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))

/-- On the pseudo-elliptic locus `(n-1)² = 1-c`, the `artanh` argument is in `(-1,1)`. -/
theorem pseudo_arg_bounds {c n φ : ℝ} (hc : c < 1) (hn1 : (n - 1) ^ 2 = 1 - c)
    (hlt : n * Real.sin φ ^ 2 < 1) :
    -1 < n * Real.sin φ * Real.cos φ / ellipticEIntegrand c φ
      ∧ n * Real.sin φ * Real.cos φ / ellipticEIntegrand c φ < 1 := by
  have hE := ellipticEIntegrand_pos hc φ
  have hE2 := ellipticEIntegrand_sq hc φ
  have hkey : ellipticEIntegrand c φ ^ 2
      - (n * Real.sin φ * Real.cos φ) ^ 2
      = (1 - n * Real.sin φ ^ 2) ^ 2 := by
    rw [hE2]
    have hc_eq : c = 2 * n - n ^ 2 := by nlinarith [hn1]
    rw [hc_eq]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hpos : 0 < (1 - n * Real.sin φ ^ 2) ^ 2 := by
    have : 0 < 1 - n * Real.sin φ ^ 2 := by linarith
    positivity
  have hsq : (n * Real.sin φ * Real.cos φ / ellipticEIntegrand c φ) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    nlinarith [hkey, hpos]
  have hsq' : (n * Real.sin φ * Real.cos φ / ellipticEIntegrand c φ) ^ 2
      < (1 : ℝ) ^ 2 := by simpa using hsq
  exact abs_lt_of_sq_lt_sq' hsq' zero_le_one

/-- The `n = 1 + k'` closed form is P-constructible below the pole. -/
theorem ellipticPiInc_pseudo_plus_Pconstructible {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc0 : 0 < c) (hc : c < 1)
    (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2)
    (hpole : (1 + Real.sqrt (1 - c)) * Real.sin φ ^ 2 < 1) :
    PConstructible (ellipticPiInc c (1 + Real.sqrt (1 - c)) φ) := by
  rw [ellipticPiInc_pseudo_plus hc h0 hπ hpole]
  unfold pseudoAnti
  have hm2 : Real.sqrt (1 - c) ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  have hn1 : (1 + Real.sqrt (1 - c) - 1) ^ 2 = 1 - c := by
    rw [show 1 + Real.sqrt (1 - c) - 1 = Real.sqrt (1 - c) by ring, hm2]
  have hb := pseudo_arg_bounds hc hn1 hpole
  have hF := ellipticF_Pconstructible hcP hφP hc
  have harg : PConstructible
      ((1 + Real.sqrt (1 - c)) * Real.sin φ * Real.cos φ / ellipticEIntegrand c φ) := by
    pconstructible
  have harctan := artanh_Pconstructible harg hb.1 hb.2
  pconstructible

/-- The `n = 1 - k'` closed form is P-constructible. -/
theorem ellipticPiInc_pseudo_minus_Pconstructible {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc0 : 0 < c) (hc : c < 1) :
    PConstructible (ellipticPiInc c (1 - Real.sqrt (1 - c)) φ) := by
  rw [ellipticPiInc_pseudo_minus hc]
  unfold pseudoAnti
  have hm2 : (-(Real.sqrt (1 - c))) ^ 2 = 1 - c := by
    rw [neg_sq]; exact Real.sq_sqrt (by linarith)
  have hn1 : (1 - Real.sqrt (1 - c) - 1) ^ 2 = 1 - c := by
    rw [show 1 - Real.sqrt (1 - c) - 1 = -(Real.sqrt (1 - c)) by ring, hm2]
  have hlt : (1 - Real.sqrt (1 - c)) * Real.sin φ ^ 2 < 1 := by
    have hmpos : 0 < Real.sqrt (1 - c) := Real.sqrt_pos.mpr (by linarith)
    have hs := Real.sin_sq_le_one φ
    have hs0 : 0 ≤ Real.sin φ ^ 2 := sq_nonneg _
    nlinarith
  have hb := pseudo_arg_bounds hc hn1 hlt
  have hF := ellipticF_Pconstructible hcP hφP hc
  have harg : PConstructible
      ((1 - Real.sqrt (1 - c)) * Real.sin φ * Real.cos φ / ellipticEIntegrand c φ) := by
    pconstructible
  have harctan := artanh_Pconstructible harg hb.1 hb.2
  pconstructible

/-- **The `n > 1` theorem without the exceptional locus.** The omitted locus
`(n-1)² = 1-c` is exactly the pseudo-elliptic branch `n = 1 + k'`. -/
theorem ellipticPiInc_Pconstructible_gt_one' {c n Φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hc0 : 0 < c) (hc : c < 1) (hn : 1 < n) (h0 : 0 < Φ) (hlt : Φ < Real.pi / 2)
    (hp : n * Real.sin Φ ^ 2 < 1) :
    PConstructible (ellipticPiInc c n Φ) := by
  by_cases hgen : (n - 1) ^ 2 = 1 - c
  · set m := Real.sqrt (1 - c) with hmdef
    have hm2 : m ^ 2 = 1 - c := by rw [hmdef]; exact Real.sq_sqrt (by linarith)
    have hmpos : 0 < m := by rw [hmdef]; exact Real.sqrt_pos.mpr (by linarith)
    have hsq : (n - 1) ^ 2 = m ^ 2 := by rw [hm2]; exact hgen
    have hnm1 : n - 1 = m := by
      have h1 : 0 ≤ n - 1 := by linarith
      have h2 : 0 ≤ m := hmpos.le
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · exact h
      · linarith
    have hnm : n = 1 + m := by linarith
    have hp' : (1 + m) * Real.sin Φ ^ 2 < 1 := by rw [← hnm]; exact hp
    rw [hnm]
    exact ellipticPiInc_pseudo_plus_Pconstructible hcP hΦP hc0 hc h0.le hlt hp'
  · exact ellipticPiInc_Pconstructible_gt_one hcP hnP hΦP hc0 hc hn h0 hlt hp hgen

end Pconstructible
