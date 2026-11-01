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
import Pptc.ThirdKindAll.CircularUpper
import Pptc.ThirdKindAll.Pseudo
import Pptc.ThirdKindAll.HyperbolicLower
import Pptc.ThirdKindAll.Period

/-! # Pptc.ThirdKindAll.Main

The incomplete third-kind integral is P-constructible for every real characteristic,
modulus and upper limit. -/

namespace Pconstructible

/-- The pole angle of `1 - n sin²θ` for `n > 1`. -/
noncomputable def gtOneBeta (n : ℝ) : ℝ :=
  Real.arcsin (1 / Real.sqrt n)

theorem gtOneBeta_nonneg {n : ℝ} (_hn : 1 < n) : 0 ≤ gtOneBeta n := by
  unfold gtOneBeta
  exact Real.arcsin_nonneg.mpr (div_nonneg zero_le_one (Real.sqrt_nonneg n))

theorem gtOneBeta_lt_pi_div_two {n : ℝ} (hn : 1 < n) :
    gtOneBeta n < Real.pi / 2 := by
  unfold gtOneBeta
  rw [Real.arcsin_lt_pi_div_two]
  have hnpos : 0 < n := by linarith
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsqrtgt : 1 < Real.sqrt n := by
    nlinarith [Real.sq_sqrt hnpos.le, Real.sqrt_nonneg n]
  rw [div_lt_one hsqrtpos]
  exact hsqrtgt

theorem gtOneBeta_sin {n : ℝ} (hn : 1 < n) :
    Real.sin (gtOneBeta n) = 1 / Real.sqrt n := by
  unfold gtOneBeta
  have hnpos : 0 < n := by linarith
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsqrtgt : 1 < Real.sqrt n := by
    nlinarith [Real.sq_sqrt hnpos.le, Real.sqrt_nonneg n]
  refine Real.sin_arcsin ?_ ?_
  · have : 0 ≤ 1 / Real.sqrt n := div_nonneg zero_le_one (Real.sqrt_nonneg n)
    linarith
  · rw [div_le_one hsqrtpos]
    exact hsqrtgt.le

theorem gtOneBeta_pole {n : ℝ} (hn : 1 < n) :
    n * Real.sin (gtOneBeta n) ^ 2 = 1 := by
  have hnpos : 0 < n := by linarith
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  rw [gtOneBeta_sin hn]
  field_simp [hsqrtpos.ne']
  rw [Real.sq_sqrt hnpos.le]

theorem gtOne_phi_lt_pi_div_two {n Φ : ℝ} (hn : 1 < n) (hΦ0 : 0 ≤ Φ)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    Φ < Real.pi / 2 := by
  by_contra h
  have hβ0 := gtOneBeta_nonneg hn
  have hβlt := gtOneBeta_lt_pi_div_two hn
  have hmem : gtOneBeta n ∈ Set.uIcc (0 : ℝ) Φ := by
    rw [Set.uIcc_of_le hΦ0]
    exact ⟨hβ0, le_trans hβlt.le (le_of_not_gt h)⟩
  have hzero := hne (gtOneBeta n) hmem
  rw [gtOneBeta_pole hn] at hzero
  norm_num at hzero

theorem gtOne_sin_sq_lt_one {n Φ : ℝ} (hn : 1 < n) (hΦ0 : 0 ≤ Φ)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    n * Real.sin Φ ^ 2 < 1 := by
  have hΦlt := gtOne_phi_lt_pi_div_two hn hΦ0 hne
  have hnpos : 0 < n := by linarith
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsqrtgt : 1 < Real.sqrt n := by
    nlinarith [Real.sq_sqrt hnpos.le, Real.sqrt_nonneg n]
  have hβ0 := gtOneBeta_nonneg hn
  have hβlt := gtOneBeta_lt_pi_div_two hn
  have hβsin := gtOneBeta_sin hn
  by_contra h
  have hle : 1 ≤ n * Real.sin Φ ^ 2 := le_of_not_gt h
  have hsinΦ0 : 0 ≤ Real.sin Φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hΦ0 (by linarith [hΦlt, Real.pi_pos])
  have hsinΦ_ge : 1 / Real.sqrt n ≤ Real.sin Φ := by
    have hdiv : 1 / n ≤ Real.sin Φ ^ 2 := by
      rw [div_le_iff₀ hnpos]
      nlinarith
    have hsq : (1 / Real.sqrt n) ^ 2 ≤ Real.sin Φ ^ 2 := by
      rw [div_pow, one_pow, Real.sq_sqrt hnpos.le]
      exact hdiv
    nlinarith [hsinΦ0, hsqrtpos]
  have hβle : gtOneBeta n ≤ Φ := by
    calc gtOneBeta n = Real.arcsin (Real.sin (gtOneBeta n)) := by
          rw [Real.arcsin_sin]
          · linarith [hβ0]
          · exact hβlt.le
      _ ≤ Real.arcsin (Real.sin Φ) := by
          apply Real.arcsin_le_arcsin
          simpa [hβsin] using hsinΦ_ge
      _ = Φ := Real.arcsin_sin (by linarith [hΦlt]) hΦlt.le
  have hmem : gtOneBeta n ∈ Set.uIcc (0 : ℝ) Φ := by
    rw [Set.uIcc_of_le hΦ0]
    exact ⟨hβ0, hβle⟩
  have hzero := hne (gtOneBeta n) hmem
  rw [gtOneBeta_pole hn] at hzero
  norm_num at hzero

theorem ellipticPiInc_Pconstructible_gt_one_all {c n Φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hc0 : 0 < c) (hc : c < 1) (hn : 1 < n)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc c n Φ) := by
  rcases lt_trichotomy Φ 0 with hneg | hzero | hpos
  · have hpos' : 0 < -Φ := by linarith
    have hne' : ∀ θ ∈ Set.uIcc (0 : ℝ) (-Φ), 1 - n * Real.sin θ ^ 2 ≠ 0 := by
      intro θ hθ
      have hmem : -θ ∈ Set.uIcc (0 : ℝ) Φ := by
        rw [Set.uIcc_of_ge (le_of_lt hneg)]
        rw [Set.uIcc_of_le hpos'.le] at hθ
        constructor <;> linarith [hθ.1, hθ.2]
      have := hne (-θ) hmem
      simpa [Real.sin_neg] using this
    have hp : n * Real.sin (-Φ) ^ 2 < 1 :=
      gtOne_sin_sq_lt_one hn hpos'.le hne'
    have hlt : -Φ < Real.pi / 2 :=
      gtOne_phi_lt_pi_div_two hn hpos'.le hne'
    have hnegP : PConstructible (ellipticPiInc c n (-Φ)) :=
      ellipticPiInc_Pconstructible_gt_one' hcP hnP (neg_Pconstructible hΦP)
        hc0 hc hn hpos' hlt hp
    rw [show Φ = -(-Φ) by ring, ellipticPiInc_neg]
    exact neg_Pconstructible hnegP
  · subst Φ
    simpa [ellipticPiInc] using zero_Pconstructible
  · exact ellipticPiInc_Pconstructible_gt_one' hcP hnP hΦP hc0 hc hn hpos
      (gtOne_phi_lt_pi_div_two hn hpos.le hne)
      (gtOne_sin_sq_lt_one hn hpos.le hne)

theorem ellipticPiInc_Pconstructible_one_all {c Φ : ℝ}
    (hcP : PConstructible c) (hΦP : PConstructible Φ) (hc : c < 1)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - 1 * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc c 1 Φ) := by
  have hlt : |Φ| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · by_contra h
      have hle : Φ ≤ -(Real.pi / 2) := le_of_not_gt h
      have hmem : -(Real.pi / 2) ∈ Set.uIcc (0 : ℝ) Φ := by
        rw [Set.mem_uIcc]
        right
        constructor <;> linarith [Real.pi_pos]
      have hzero := hne (-(Real.pi / 2)) hmem
      norm_num at hzero
    · by_contra h
      have hle : Real.pi / 2 ≤ Φ := le_of_not_gt h
      have hmem : Real.pi / 2 ∈ Set.uIcc (0 : ℝ) Φ := by
        rw [Set.mem_uIcc]
        left
        constructor <;> linarith [Real.pi_pos]
      have hzero := hne (Real.pi / 2) hmem
      norm_num at hzero
  exact ellipticPiInc_one_Pconstructible hcP hΦP hc hlt

/-- **The incomplete third-kind integral is P-constructible for every real characteristic.** -/
theorem ellipticPiInc_Pconstructible {c n Φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hc0 : 0 < c) (hc : c < 1)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc c n Φ) := by
  rcases lt_trichotomy n 0 with hnneg | hnzero | hnpos
  · exact ellipticPiInc_Pconstructible_neg hcP hnP hΦP hc0 hc hnneg
  · subst n
    exact ellipticPiInc_zero_Pconstructible hcP hΦP hc
  · rcases lt_trichotomy n c with hnc | hncn | hcn
    · exact ellipticPiInc_Pconstructible_hyp_lower_all hcP hnP hΦP hc0 hc hnpos hnc
    · subst n
      exact ellipticPiInc_self_Pconstructible hcP hΦP hc
    · rcases lt_trichotomy n 1 with hn1 | hn1eq | hn1gt
      · exact ellipticPiInc_Pconstructible_circ_upper hcP hnP hΦP hc0 hc hcn hn1
      · subst n
        exact ellipticPiInc_Pconstructible_one_all hcP hΦP hc hne
      · exact ellipticPiInc_Pconstructible_gt_one_all hcP hnP hΦP hc0 hc hn1gt hne

end Pconstructible
