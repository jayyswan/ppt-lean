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

/-! # Pptc.ThirdKindAll.ModulusOne

The modulus-one reduction: when `c = 1` the third-kind integral is elementary,
`∫ dθ / ((1 - n sin²θ) cos θ)`, and the substitution `s = sin θ` makes the integrand
rational in `s`. -/

namespace Pconstructible

/-! ### The integrand at modulus one

At `c = 1` the second-kind integrand collapses to `√(1 - sin²θ) = cos θ` on the principal
branch, so the third-kind integrand is `1/((1 - n sin²θ) cos θ)` — no elliptic square root
survives. -/

/-- Points of the segment `[0, Φ]` stay on the principal branch when `Φ` does. -/
theorem abs_lt_pi_div_two_of_mem_uIcc {Φ θ : ℝ} (hΦ : |Φ| < Real.pi / 2)
    (hθ : θ ∈ Set.uIcc (0 : ℝ) Φ) : |θ| < Real.pi / 2 := by
  rw [abs_lt] at hΦ ⊢
  rcases Set.mem_uIcc.mp hθ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

/-- A modulus-one no-pole hypothesis forces `|Φ| < π/2`: the points `±π/2` would make the
integrand vanish in the denominator. -/
theorem abs_lt_pi_div_two_of_one_sub_sin_sq {Φ : ℝ}
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - 1 * Real.sin θ ^ 2 ≠ 0) :
    |Φ| < Real.pi / 2 := by
  rw [abs_lt]
  constructor
  · by_contra h
    have hle : Φ ≤ -(Real.pi / 2) := le_of_not_gt h
    have hmem : -(Real.pi / 2) ∈ Set.uIcc (0 : ℝ) Φ := by
      rw [Set.mem_uIcc]
      right
      constructor <;> linarith [Real.pi_pos]
    have hzero := hmod (-(Real.pi / 2)) hmem
    norm_num at hzero
  · by_contra h
    have hle : Real.pi / 2 ≤ Φ := le_of_not_gt h
    have hmem : Real.pi / 2 ∈ Set.uIcc (0 : ℝ) Φ := by
      rw [Set.mem_uIcc]
      left
      constructor <;> linarith [Real.pi_pos]
    have hzero := hmod (Real.pi / 2) hmem
    norm_num at hzero

/-- On the principal branch `sin` stays inside `(-1, 1)`. -/
theorem abs_sin_lt_one {θ : ℝ} (hθ : |θ| < Real.pi / 2) : |Real.sin θ| < 1 := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hsq : Real.sin θ ^ 2 < 1 := by
    have h := Real.sin_sq_add_cos_sq θ
    nlinarith
  exact abs_lt_of_sq_lt_sq (by simpa using hsq) zero_le_one

/-- At modulus one the second-kind integrand is `cos θ` on the principal branch. -/
theorem ellipticEIntegrand_one {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    ellipticEIntegrand 1 θ = Real.cos θ := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  rw [ellipticEIntegrand,
    show (1 : ℝ) - 1 * Real.sin θ ^ 2 = Real.cos θ ^ 2 by
      linear_combination -Real.sin_sq_add_cos_sq θ,
    Real.sqrt_sq hcos.le]

/-- The modulus-one third-kind integrand is `1/((1 - n sin²θ) cos θ)`. -/
theorem ellipticPiIntegrand_one {n θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    ellipticPiIntegrand 1 n θ = 1 / ((1 - n * Real.sin θ ^ 2) * Real.cos θ) := by
  rw [ellipticPiIntegrand, ellipticEIntegrand_one hθ]

/-- A pole-free segment carries no point with `n sin²θ ≥ 1`: the intermediate value
theorem would produce a zero of `1 - n sin²` inside it. -/
theorem mul_sin_sq_lt_one_of_ne {n Φ : ℝ} (_hn : 0 < n)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, n * Real.sin θ ^ 2 < 1 := by
  intro θ hθ
  rcases Set.mem_uIcc.mp hθ with ⟨h0, hΦ⟩ | ⟨hΦ, h0⟩
  · by_contra hcon
    have hcon' : 1 ≤ n * Real.sin θ ^ 2 := not_lt.mp hcon
    have hcont : ContinuousOn (fun t : ℝ => n * Real.sin t ^ 2) (Set.Icc 0 θ) := by fun_prop
    have hf0 : (fun t : ℝ => n * Real.sin t ^ 2) 0 = 0 := by simp
    obtain ⟨c, hc, hce⟩ := intermediate_value_Icc h0 hcont
      (show (1 : ℝ) ∈ Set.Icc ((fun t : ℝ => n * Real.sin t ^ 2) 0)
          ((fun t : ℝ => n * Real.sin t ^ 2) θ) from ⟨by rw [hf0]; exact zero_le_one, by
        simpa using hcon'⟩)
    have hmem : c ∈ Set.uIcc (0 : ℝ) Φ := Set.mem_uIcc.mpr (Or.inl ⟨hc.1, hc.2.trans hΦ⟩)
    have hzero := hne c hmem
    have hce' : n * Real.sin c ^ 2 = 1 := hce
    rw [hce'] at hzero
    norm_num at hzero
  · by_contra hcon
    have hcon' : 1 ≤ n * Real.sin θ ^ 2 := not_lt.mp hcon
    have hcont : ContinuousOn (fun t : ℝ => n * Real.sin t ^ 2) (Set.Icc θ 0) := by fun_prop
    have hf0 : (fun t : ℝ => n * Real.sin t ^ 2) 0 = 0 := by simp
    obtain ⟨c, hc, hce⟩ := intermediate_value_Icc' h0 hcont
      (show (1 : ℝ) ∈ Set.Icc ((fun t : ℝ => n * Real.sin t ^ 2) 0)
          ((fun t : ℝ => n * Real.sin t ^ 2) θ) from ⟨by rw [hf0]; exact zero_le_one, by
        simpa using hcon'⟩)
    have hmem : c ∈ Set.uIcc (0 : ℝ) Φ := Set.mem_uIcc.mpr (Or.inr ⟨hΦ.trans hc.1, hc.2⟩)
    have hzero := hne c hmem
    have hce' : n * Real.sin c ^ 2 = 1 := hce
    rw [hce'] at hzero
    norm_num at hzero

/-! ### The antiderivatives in `s = sin θ`

With `s = sin θ` the integral becomes `∫ ds / ((1 - n s²)(1 - s²))`, whose partial
fractions give an elementary antiderivative in each of the three regimes of `n`. -/

/-- Antiderivative of `1/((1 - s²)²)`, the case `n = 1`. -/
noncomputable def modulusOneAntiOne (s : ℝ) : ℝ :=
  s / (2 * (1 - s ^ 2)) + Real.artanh s / 2

/-- Antiderivative of `1/((1 - n s²)(1 - s²))` for `n > 0`,
from `1/(1-s²) - n/(1-n s²)` scaled by `1/(1-n)`. -/
noncomputable def modulusOneAntiPos (n s : ℝ) : ℝ :=
  (Real.artanh s - Real.sqrt n * Real.artanh (Real.sqrt n * s)) / (1 - n)

/-- Antiderivative of `1/((1 - n s²)(1 - s²))` for `n ≤ 0`,
where `-n/(1-n s²)` integrates to `√(-n) arctan(√(-n) s)`. -/
noncomputable def modulusOneAntiNeg (n s : ℝ) : ℝ :=
  (Real.artanh s + Real.sqrt (-n) * Real.arctan (Real.sqrt (-n) * s)) / (1 - n)

/-- The `n = 1` antiderivative differentiates to `1/(1 - s²)²`. -/
theorem hasDerivAt_modulusOneAntiOne {s : ℝ} (hs : |s| < 1) :
    HasDerivAt modulusOneAntiOne (1 / ((1 - 1 * s ^ 2) * (1 - s ^ 2))) s := by
  have hs' := abs_lt.mp hs
  have hs2 : s ^ 2 < 1 := by nlinarith
  have hden : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hden2 : 2 * (1 - s ^ 2) ≠ 0 := mul_ne_zero two_ne_zero hden
  have hsq : (1 : ℝ) - 1 * s ^ 2 = 1 - s ^ 2 := by ring
  have hd : HasDerivAt (fun t : ℝ => t / (2 * (1 - t ^ 2)))
      ((1 + s ^ 2) / (2 * (1 - s ^ 2) ^ 2)) s := by
    have hden' : HasDerivAt (fun t : ℝ => 2 * (1 - t ^ 2)) (-4 * s) s := by
      have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      have h' := (hp.const_sub 1).const_mul 2
      refine h'.congr_deriv ?_
      ring
    have h := (hasDerivAt_id s).div hden' hden2
    refine h.congr_deriv ?_
    simp only [id_eq]
    field_simp
    ring_nf
  have ha : HasDerivAt (fun t : ℝ => Real.artanh t / 2) (1 / (2 * (1 - s ^ 2))) s := by
    have h := (hasDerivAt_artanh hs'.1 hs'.2).div_const 2
    refine h.congr_deriv ?_
    field_simp
  refine (hd.add ha).congr_deriv ?_
  rw [hsq]
  field_simp
  ring_nf

/-- For `n > 0` the antiderivative `(artanh s - √n artanh(√n s))/(1 - n)` differentiates to
`1/((1 - n s²)(1 - s²))`. -/
theorem hasDerivAt_modulusOneAntiPos {n s : ℝ} (hn : 0 < n) (hn1 : n ≠ 1)
    (hs : |s| < 1) (hb : n * s ^ 2 < 1) :
    HasDerivAt (modulusOneAntiPos n) (1 / ((1 - n * s ^ 2) * (1 - s ^ 2))) s := by
  have hm2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hs' := abs_lt.mp hs
  have hden : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hns : 1 - n * s ^ 2 ≠ 0 := by nlinarith
  have hn1' : 1 - n ≠ 0 := by
    intro h
    exact hn1 (by linarith)
  have hms : |Real.sqrt n * s| < 1 := by
    have hsq : (Real.sqrt n * s) ^ 2 < 1 ^ 2 := by
      rw [mul_pow, hm2]
      simpa using hb
    exact abs_lt_of_sq_lt_sq hsq zero_le_one
  have hms' := abs_lt.mp hms
  have h2 : HasDerivAt (fun t : ℝ => Real.sqrt n * Real.artanh (Real.sqrt n * t))
      (n * (1 / (1 - n * s ^ 2))) s := by
    have hinner : HasDerivAt (fun t : ℝ => Real.sqrt n * t) (Real.sqrt n) s := by
      simpa using (hasDerivAt_id s).const_mul (Real.sqrt n)
    have hcomp := ((hasDerivAt_artanh hms'.1 hms'.2).comp s hinner).const_mul (Real.sqrt n)
    refine hcomp.congr_deriv ?_
    have hsq : (Real.sqrt n * s) ^ 2 = n * s ^ 2 := by rw [mul_pow, hm2]
    have hsqq : Real.sqrt n * Real.sqrt n = n := by rw [← sq, hm2]
    rw [hsq]
    rw [show Real.sqrt n * (1 / (1 - n * s ^ 2) * Real.sqrt n)
        = (Real.sqrt n * Real.sqrt n) * (1 / (1 - n * s ^ 2)) by ring, hsqq]
  have h := ((hasDerivAt_artanh hs'.1 hs'.2).sub h2).div_const (1 - n)
  refine h.congr_deriv ?_
  field_simp [show (1 : ℝ) - s ^ 2 * n ≠ 0 by nlinarith]
  ring

/-- For `n ≤ 0` the antiderivative `(artanh s + √(-n) arctan(√(-n) s))/(1 - n)` differentiates
to `1/((1 - n s²)(1 - s²))`. -/
theorem hasDerivAt_modulusOneAntiNeg {n s : ℝ} (hn : n ≤ 0) (hs : |s| < 1) :
    HasDerivAt (modulusOneAntiNeg n) (1 / ((1 - n * s ^ 2) * (1 - s ^ 2))) s := by
  have hm2 : Real.sqrt (-n) ^ 2 = -n := Real.sq_sqrt (by linarith)
  have hs' := abs_lt.mp hs
  have hden : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hns : 1 - n * s ^ 2 ≠ 0 := by nlinarith
  have hn1' : 1 - n ≠ 0 := by linarith
  have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (-n) * Real.arctan (Real.sqrt (-n) * t))
      ((-n) * (1 / (1 - n * s ^ 2))) s := by
    have hinner : HasDerivAt (fun t : ℝ => Real.sqrt (-n) * t) (Real.sqrt (-n)) s := by
      simpa using (hasDerivAt_id s).const_mul (Real.sqrt (-n))
    have hcomp := ((Real.hasDerivAt_arctan (Real.sqrt (-n) * s)).comp s hinner).const_mul
      (Real.sqrt (-n))
    refine hcomp.congr_deriv ?_
    have hsq : (Real.sqrt (-n) * s) ^ 2 = -n * s ^ 2 := by rw [mul_pow, hm2]
    have hsqq : Real.sqrt (-n) * Real.sqrt (-n) = -n := by rw [← sq, hm2]
    rw [hsq]
    rw [show Real.sqrt (-n) * (1 / (1 + -n * s ^ 2) * Real.sqrt (-n))
        = (Real.sqrt (-n) * Real.sqrt (-n)) * (1 / (1 + -n * s ^ 2)) by ring, hsqq]
    ring
  have h := ((hasDerivAt_artanh hs'.1 hs'.2).add h2).div_const (1 - n)
  refine h.congr_deriv ?_
  field_simp [show (1 : ℝ) - s ^ 2 * n ≠ 0 by nlinarith]
  ring

/-! ### The reduction to the rational integral -/

/-- From `n s² < 1` and `n > 0`, the rescaled argument `√n s` is in `(-1, 1)`. -/
theorem abs_sqrt_mul_lt_one {n s : ℝ} (hn : 0 < n) (hb : n * s ^ 2 < 1) :
    |Real.sqrt n * s| < 1 := by
  have hm2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hsq : (Real.sqrt n * s) ^ 2 < 1 ^ 2 := by
    rw [mul_pow, hm2]
    simpa using hb
  exact abs_lt_of_sq_lt_sq hsq zero_le_one

/-- `(artanh s - √n artanh(√n s))/(1 - n)` is P-constructible for `n > 0`, `n ≠ 1` and
`n s² < 1`. -/
theorem modulusOneAntiPos_Pconstructible {n s : ℝ} (hnP : PConstructible n)
    (hsP : PConstructible s) (hs : |s| < 1) (hn : 0 < n) (_hn1 : n ≠ 1)
    (hb : n * s ^ 2 < 1) : PConstructible (modulusOneAntiPos n s) := by
  unfold modulusOneAntiPos
  have hargP : PConstructible (Real.sqrt n * s) := by pconstructible
  have hb' := abs_lt.mp (abs_sqrt_mul_lt_one hn hb)
  have h1 := artanh_Pconstructible hsP (abs_lt.mp hs).1 (abs_lt.mp hs).2
  have h2 := artanh_Pconstructible hargP hb'.1 hb'.2
  pconstructible

/-- **The modulus-one substitution `s = sin θ`.** If `F` is an antiderivative of
`s ↦ 1/((1 - n s²)(1 - s²))` along the segment and `F 0 = 0`, then `Π(1, n, Φ) = F (sin Φ)`. -/
theorem ellipticPiInc_one_modulus_eq {n Φ : ℝ} {F : ℝ → ℝ}
    (hΦ : |Φ| < Real.pi / 2)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0)
    (hF : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ,
      HasDerivAt F (1 / ((1 - n * Real.sin θ ^ 2) * (1 - Real.sin θ ^ 2))) (Real.sin θ))
    (hF0 : F 0 = 0) :
    ellipticPiInc 1 n Φ = F (Real.sin Φ) := by
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ,
      HasDerivAt (fun θ : ℝ => F (Real.sin θ)) (ellipticPiIntegrand 1 n θ) θ := by
    intro θ hθ
    have hθ' := abs_lt_pi_div_two_of_mem_uIcc hΦ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ')
    have hcs : (1 : ℝ) - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
      linear_combination -Real.sin_sq_add_cos_sq θ
    have hcomp := (hF θ hθ).comp θ (Real.hasDerivAt_sin θ)
    rw [ellipticPiIntegrand_one hθ']
    refine hcomp.congr_deriv ?_
    rw [hcs]
    field_simp [hcos.ne']
  have hint : IntervalIntegrable (ellipticPiIntegrand 1 n) MeasureTheory.volume 0 Φ := by
    refine ContinuousOn.intervalIntegrable fun θ hθ => ?_
    have hθ' := abs_lt_pi_div_two_of_mem_uIcc hΦ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ')
    refine ContinuousAt.continuousWithinAt (ContinuousAt.div continuousAt_const ?_ ?_)
    · exact (((by fun_prop : Continuous fun s : ℝ => 1 - n * Real.sin s ^ 2)).mul
        (continuous_ellipticEIntegrand 1)).continuousAt
    · refine mul_ne_zero (hne θ hθ) ?_
      rw [ellipticEIntegrand_one hθ']
      exact hcos.ne'
  rw [ellipticPiInc, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [hF0]

/-! ### The theorem -/

/-- **The modulus-one case of the headline theorem.** At `c = 1` the third-kind integrand is
elementary, and the substitution `s = sin θ` makes it rational, so `Π(1, n, Φ)` is
P-constructible for every P-constructible characteristic with no pole on the segment. -/
theorem ellipticPiInc_one_modulus_Pconstructible {n Φ : ℝ}
    (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - 1 * Real.sin θ ^ 2 ≠ 0)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc 1 n Φ) := by
  have hΦ : |Φ| < Real.pi / 2 := abs_lt_pi_div_two_of_one_sub_sin_sq hmod
  have hsinΦ : |Real.sin Φ| < 1 := abs_sin_lt_one hΦ
  have hsinΦ' := abs_lt.mp hsinΦ
  have hsinP : PConstructible (Real.sin Φ) := sin_Pconstructible hΦP
  rcases lt_trichotomy n 1 with hn1 | hn1 | hn1
  · by_cases hn0 : n ≤ 0
    · -- `n ≤ 0`: the `arctan` branch
      have hF : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ,
          HasDerivAt (modulusOneAntiNeg n)
            (1 / ((1 - n * Real.sin θ ^ 2) * (1 - Real.sin θ ^ 2))) (Real.sin θ) :=
        fun θ hθ => hasDerivAt_modulusOneAntiNeg hn0
          (abs_sin_lt_one (abs_lt_pi_div_two_of_mem_uIcc hΦ hθ))
      rw [ellipticPiInc_one_modulus_eq hΦ hne hF (by simp [modulusOneAntiNeg])]
      unfold modulusOneAntiNeg
      have hartanh : PConstructible (Real.artanh (Real.sin Φ)) :=
        artanh_Pconstructible hsinP hsinΦ'.1 hsinΦ'.2
      have harctan : PConstructible (Real.arctan (Real.sqrt (-n) * Real.sin Φ)) :=
        arctan_Pconstructible (by pconstructible)
      pconstructible
    · -- `0 < n < 1`: the `artanh` branch, no extra bound needed
      have hnpos : 0 < n := lt_of_not_ge hn0
      have hb : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, n * Real.sin θ ^ 2 < 1 := by
        intro θ _
        have hs := Real.sin_sq_le_one θ
        nlinarith
      have hF : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ,
          HasDerivAt (modulusOneAntiPos n)
            (1 / ((1 - n * Real.sin θ ^ 2) * (1 - Real.sin θ ^ 2))) (Real.sin θ) :=
        fun θ hθ => hasDerivAt_modulusOneAntiPos hnpos hn1.ne
          (abs_sin_lt_one (abs_lt_pi_div_two_of_mem_uIcc hΦ hθ)) (hb θ hθ)
      rw [ellipticPiInc_one_modulus_eq hΦ hne hF (by simp [modulusOneAntiPos])]
      have hbΦ : n * Real.sin Φ ^ 2 < 1 := by
        have hs := Real.sin_sq_le_one Φ
        nlinarith
      exact modulusOneAntiPos_Pconstructible hnP hsinP hsinΦ hnpos hn1.ne hbΦ
  · -- `n = 1`
    subst hn1
    have hF : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ,
        HasDerivAt modulusOneAntiOne
          (1 / ((1 - 1 * Real.sin θ ^ 2) * (1 - Real.sin θ ^ 2))) (Real.sin θ) :=
      fun θ hθ => hasDerivAt_modulusOneAntiOne
        (abs_sin_lt_one (abs_lt_pi_div_two_of_mem_uIcc hΦ hθ))
    rw [ellipticPiInc_one_modulus_eq hΦ hne hF (by simp [modulusOneAntiOne])]
    unfold modulusOneAntiOne
    have hartanh : PConstructible (Real.artanh (Real.sin Φ)) :=
      artanh_Pconstructible hsinP hsinΦ'.1 hsinΦ'.2
    pconstructible
  · -- `1 < n`: the `artanh` branch, with the pole bound from `hne`
    have hbound := mul_sin_sq_lt_one_of_ne (n := n) (Φ := Φ) (by linarith) hne
    have hbΦ : n * Real.sin Φ ^ 2 < 1 := hbound Φ Set.right_mem_uIcc
    have hF : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ,
        HasDerivAt (modulusOneAntiPos n)
          (1 / ((1 - n * Real.sin θ ^ 2) * (1 - Real.sin θ ^ 2))) (Real.sin θ) :=
      fun θ hθ => hasDerivAt_modulusOneAntiPos (by linarith) hn1.ne'
        (abs_sin_lt_one (abs_lt_pi_div_two_of_mem_uIcc hΦ hθ)) (hbound θ hθ)
    rw [ellipticPiInc_one_modulus_eq hΦ hne hF (by simp [modulusOneAntiPos])]
    exact modulusOneAntiPos_Pconstructible hnP hsinP hsinΦ (by linarith) hn1.ne' hbΦ

end Pconstructible
