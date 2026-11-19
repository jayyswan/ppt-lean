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

import Pptc.ThirdKind

/-! # Pptc.ThirdKindAll.Period

The symmetries of the incomplete third-kind integrand, and the reduction of an arbitrary
upper limit to one half-turn.

For `n < 1` the integrand `1 / ((1 - n sin²θ) Δ(θ))` is defined and continuous on all of
`ℝ`, is `π`-periodic (`sin²` is), and is even. Hence

  `Π(n, φ + mπ) = Π(n, φ) + 2m · Π(n)` and `Π(n, -φ) = -Π(n, φ)`,

and every upper limit reduces to `[0, π)`. This is exactly the reduction used for `F` and
`E`, with the complete third-kind integral in place of `F(π)`.

The no-pole hypothesis of the general theorem is not needed here: these lemmas are used
only in the cases `n < 1`, where there is no pole. -/

namespace Pconstructible

/-- The third-kind integrand has period `π`. -/
theorem periodic_ellipticPiIntegrand (c n : ℝ) :
    Function.Periodic (ellipticPiIntegrand c n) Real.pi := fun θ => by
  simp [ellipticPiIntegrand, ellipticEIntegrand, Real.sin_add_pi]

/-- The third-kind integrand is even. -/
theorem ellipticPiIntegrand_neg (c n θ : ℝ) :
    ellipticPiIntegrand c n (-θ) = ellipticPiIntegrand c n θ := by
  simp [ellipticPiIntegrand, ellipticEIntegrand]

/-- For `n < 1` the third-kind integrand is continuous everywhere: `1 - n sin²θ ≥ 1 - n > 0`. -/
theorem continuous_ellipticPiIntegrand {c n : ℝ} (hc : c < 1) (hn : n < 1) :
    Continuous (ellipticPiIntegrand c n) := by
  unfold ellipticPiIntegrand
  refine Continuous.div continuous_const ?_ fun θ => ?_
  · exact (by fun_prop : Continuous fun θ : ℝ => 1 - n * Real.sin θ ^ 2).mul
      (continuous_ellipticEIntegrand c)
  · have hs : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
    have h3 : 0 < 1 - n * Real.sin θ ^ 2 := by
      rcases le_total n 0 with hn0 | hn0
      · have : n * Real.sin θ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn0 hs0
        linarith
      · have hle : n * Real.sin θ ^ 2 ≤ n * 1 := mul_le_mul_of_nonneg_left hs hn0
        nlinarith
    exact mul_ne_zero h3.ne' (ellipticEIntegrand_pos hc θ).ne'

/-- The integral over one full half-turn is twice the complete integral. -/
theorem integral_ellipticPiIntegrand_pi {c n : ℝ} (hc : c < 1) (hn : n < 1) :
    (∫ θ in (0 : ℝ)..Real.pi, ellipticPiIntegrand c n θ) = 2 * ellipticPi c n := by
  have hcont := continuous_ellipticPiIntegrand hc hn
  have hsym : ∀ θ : ℝ, ellipticPiIntegrand c n (Real.pi - θ)
      = ellipticPiIntegrand c n θ := by
    intro θ
    simp [ellipticPiIntegrand, ellipticEIntegrand]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (f := ellipticPiIntegrand c n)
    (a := (0 : ℝ)) (b := Real.pi / 2) (c := Real.pi)
    (hcont.intervalIntegrable 0 (Real.pi / 2))
    (hcont.intervalIntegrable (Real.pi / 2) Real.pi)
  rw [← hsplit]
  have hsecond : (∫ θ in Real.pi / 2..Real.pi, ellipticPiIntegrand c n θ)
      = ∫ θ in (0 : ℝ)..Real.pi / 2, ellipticPiIntegrand c n θ := by
    calc (∫ θ in Real.pi / 2..Real.pi, ellipticPiIntegrand c n θ)
        = ∫ θ in Real.pi / 2..Real.pi, ellipticPiIntegrand c n (Real.pi - θ) := by
          exact intervalIntegral.integral_congr fun θ _ => (hsym θ).symm
      _ = ∫ θ in Real.pi - Real.pi..Real.pi - Real.pi / 2, ellipticPiIntegrand c n θ :=
          intervalIntegral.integral_comp_sub_left
            (a := Real.pi / 2) (b := Real.pi) (f := ellipticPiIntegrand c n) Real.pi
      _ = ∫ θ in (0 : ℝ)..Real.pi / 2, ellipticPiIntegrand c n θ := by
          rw [show Real.pi - Real.pi = 0 by ring,
            show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
  rw [hsecond, ellipticPi]
  ring

/-- The incomplete third-kind integral is odd in the upper limit. -/
theorem ellipticPiInc_neg (c n φ : ℝ) :
    ellipticPiInc c n (-φ) = -ellipticPiInc c n φ := by
  have heven : ∀ x : ℝ, ellipticPiIntegrand c n (-x) = ellipticPiIntegrand c n x :=
    fun x => ellipticPiIntegrand_neg c n x
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -φ)
    (ellipticPiIntegrand c n)
  simp only [heven, neg_neg, neg_zero] at h
  rw [ellipticPiInc, h, intervalIntegral.integral_symm, ellipticPiInc]

/-- `Π(n, φ + mπ) = Π(n, φ) + 2mΠ(n)` for `n < 1`. -/
theorem ellipticPiInc_add_int_mul_pi {c n : ℝ} (hc : c < 1) (hn : n < 1) (φ : ℝ) (m : ℤ) :
    ellipticPiInc c n (φ + m * Real.pi) = ellipticPiInc c n φ + m * (2 * ellipticPi c n) := by
  have hper := periodic_ellipticPiIntegrand c n
  have hint : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (ellipticPiIntegrand c n) MeasureTheory.volume t₁ t₂ :=
    fun t₁ t₂ => (continuous_ellipticPiIntegrand hc hn).intervalIntegrable t₁ t₂
  have hA : (∫ θ in (0 : ℝ)..(m : ℝ) * Real.pi, ellipticPiIntegrand c n θ)
      = m * (2 * ellipticPi c n) := by
    have h := hper.intervalIntegral_add_zsmul_eq m 0 hint
    simp only [zero_add, zsmul_eq_mul] at h
    rw [integral_ellipticPiIntegrand_pi hc hn] at h
    simpa using h
  have hB : (∫ θ in ((m : ℝ) * Real.pi)..(φ + (m : ℝ) * Real.pi),
      ellipticPiIntegrand c n θ) = ellipticPiInc c n φ := by
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := φ)
      (ellipticPiIntegrand c n) ((m : ℝ) * Real.pi)
    have hshift : ∀ x : ℝ,
        ellipticPiIntegrand c n (x + (m : ℝ) * Real.pi) = ellipticPiIntegrand c n x :=
      fun x => hper.int_mul m x
    simp only [hshift, zero_add] at h
    rw [ellipticPiInc, h]
  rw [ellipticPiInc, ← intervalIntegral.integral_add_adjacent_intervals
    (b := (m : ℝ) * Real.pi) (hint 0 _) (hint _ _), hA, hB]
  ring

theorem ellipticPiIntegrand_pi_sub (c n x : ℝ) :
    ellipticPiIntegrand c n (Real.pi - x) = ellipticPiIntegrand c n x := by
  simp [ellipticPiIntegrand, ellipticEIntegrand]

/-- Reflection about the quarter turn. -/
theorem ellipticPiInc_eq_two_complete_sub {c n θ : ℝ} (hc : c < 1) (hn : n < 1)
    (h1 : Real.pi / 2 ≤ θ) (_h2 : θ ≤ Real.pi) :
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

/-- **Reduction to the first quarter turn, with the complete integral supplied separately.**
For `n < 1`, if `Π(n, ·)` is P-constructible at every P-constructible `θ ∈ [0, π/2)` and the
complete integral `Π(n)` is P-constructible, then `Π(n, ·)` is P-constructible at every
P-constructible upper limit: shift by whole half-turns (`Π(θ + mπ) = Π(θ) + 2mΠ(n)`), then
reflect about `π/2`.

This variant is what the modulus transformations use: they reach `c < 1` moduli for which
`ellipticPi_Pconstructible` does not apply directly. -/
theorem ellipticPiInc_Pconstructible_of_base' {c n Φ : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) (hΦP : PConstructible Φ) (hc : c < 1) (hn : n < 1)
    (hK : PConstructible (ellipticPi c n))
    (base : ∀ θ : ℝ, PConstructible θ → 0 ≤ θ → θ < Real.pi / 2 →
      PConstructible (ellipticPiInc c n θ)) :
    PConstructible (ellipticPiInc c n Φ) := by
  obtain ⟨m, h0, hpi⟩ := exists_int_half_turns Φ
  have hθP : PConstructible (Φ - m * Real.pi) :=
    PConstructible.sub hΦP (PConstructible.mul (int_Pconstructible m) pi_Pconstructible)
  have hkey := ellipticPiInc_add_int_mul_pi hc hn (Φ - m * Real.pi) m
  rw [sub_add_cancel] at hkey
  have hterm : PConstructible (m * (2 * ellipticPi c n)) :=
    PConstructible.mul (int_Pconstructible m) (PConstructible.mul two_Pconstructible hK)
  rw [hkey]
  set θ := Φ - m * Real.pi
  rcases lt_trichotomy θ (Real.pi / 2) with hlt | heq | hgt
  · exact PConstructible.add (base θ hθP h0 hlt) hterm
  · rw [heq, ← ellipticPi_eq_inc]
    exact PConstructible.add hK hterm
  · rw [ellipticPiInc_eq_two_complete_sub hc hn hgt.le hpi]
    have hpart := base (Real.pi - θ) (PConstructible.sub pi_Pconstructible hθP)
      (by linarith) (by linarith)
    exact PConstructible.add
      (PConstructible.sub (PConstructible.mul two_Pconstructible hK) hpart) hterm

/-- **Reduction to the first quarter turn.** For `n < 1`, if `Π(n, ·)` is P-constructible at
every P-constructible `θ ∈ [0, π/2)`, then it is P-constructible at every P-constructible
upper limit: shift by whole half-turns (`Π(θ + mπ) = Π(θ) + 2mΠ(n)`), then reflect about
`π/2`; the complete integral `Π(n)` handles the endpoint. -/
theorem ellipticPiInc_Pconstructible_of_base {c n Φ : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) (hΦP : PConstructible Φ) (hc0 : 0 < c) (hc : c < 1)
    (hn : n < 1)
    (base : ∀ θ : ℝ, PConstructible θ → 0 ≤ θ → θ < Real.pi / 2 →
      PConstructible (ellipticPiInc c n θ)) :
    PConstructible (ellipticPiInc c n Φ) :=
  ellipticPiInc_Pconstructible_of_base' hcP hnP hΦP hc hn
    (ellipticPi_Pconstructible hcP hnP hc0 hc hn) base

end Pconstructible
