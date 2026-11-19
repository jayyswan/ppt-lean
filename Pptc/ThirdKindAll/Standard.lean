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

/-! # Pptc.ThirdKindAll.Standard

The incomplete third-kind integral is P-constructible for every real characteristic and
upper limit, when the modulus lies in `(0, 1)`.

This is the case where `ellipticEIntegrand c` is everywhere positive and smooth, so the
integrand `1 / ((1 - n sin²θ) Δ(θ))` is continuous except at the characteristic poles.
The remaining moduli are reduced to this one in `Pptc.ThirdKindAll.ModulusImag`,
`Pptc.ThirdKindAll.ModulusRecip`, `Pptc.ThirdKindAll.ModulusZero` and
`Pptc.ThirdKindAll.ModulusOne`. -/

namespace Pconstructible

/-- No pole on `[0, Φ]` forces `n sin²Φ < 1`: otherwise the intermediate value theorem
produces a root of `1 - n sin²` in `[0, Φ]`. -/
theorem gtOne_sin_sq_lt_one {n Φ : ℝ} (hΦ0 : 0 ≤ Φ)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    n * Real.sin Φ ^ 2 < 1 := by
  by_contra h
  have hcont : ContinuousOn (fun θ : ℝ => n * Real.sin θ ^ 2) (Set.Icc 0 Φ) := by fun_prop
  obtain ⟨θ, hθ, hθeq⟩ := intermediate_value_Icc hΦ0 hcont ⟨by simp, not_lt.mp h⟩
  exact hne θ (by rw [Set.uIcc_of_le hΦ0]; exact hθ) (by simp only at hθeq; rw [hθeq]; norm_num)

theorem gtOne_phi_lt_pi_div_two {n Φ : ℝ} (hn : 1 < n) (hΦ0 : 0 ≤ Φ)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    Φ < Real.pi / 2 := by
  by_contra h
  have hle : Real.pi / 2 ≤ Φ := not_lt.mp h
  have := gtOne_sin_sq_lt_one (n := n) (Φ := Real.pi / 2) (by positivity) fun θ hθ => by
    rw [Set.uIcc_of_le (by positivity)] at hθ
    exact hne θ (by rw [Set.uIcc_of_le hΦ0]; exact ⟨hθ.1, hθ.2.trans hle⟩)
  simp at this
  linarith

/-- The same bound at `n = 1`, where the numerator is `cos²`. -/
theorem one_le_phi_lt_pi_div_two {n Φ : ℝ} (hn : 1 ≤ n) (hΦ0 : 0 ≤ Φ)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    Φ < Real.pi / 2 := by
  rcases lt_or_eq_of_le hn with h1 | h1
  · exact gtOne_phi_lt_pi_div_two h1 hΦ0 hne
  · subst h1
    by_contra h
    have hle : Real.pi / 2 ≤ Φ := le_of_not_gt h
    have hmem : Real.pi / 2 ∈ Set.uIcc (0 : ℝ) Φ := by
      rw [Set.uIcc_of_le hΦ0]
      exact ⟨by positivity, hle⟩
    have hzero := hne (Real.pi / 2) hmem
    norm_num at hzero

/-- A no-pole hypothesis with `1 ≤ n` forces `|Φ| < π/2`. -/
theorem abs_lt_pi_div_two_of_one_le {n Φ : ℝ} (hn : 1 ≤ n)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    |Φ| < Real.pi / 2 := by
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
    have hlt := one_le_phi_lt_pi_div_two hn hpos'.le hne'
    rw [abs_of_neg hneg]
    linarith
  · subst hzero
    simpa using Real.pi_pos
  · rw [abs_of_pos hpos]
    exact one_le_phi_lt_pi_div_two hn hpos.le hne

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
      gtOne_sin_sq_lt_one hpos'.le hne'
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
      (gtOne_sin_sq_lt_one hpos.le hne)

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

/-- **The incomplete third-kind integral is P-constructible for every real characteristic,
for moduli in `(0, 1)`.** -/
theorem ellipticPiInc_Pconstructible_standard {c n Φ : ℝ}
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
