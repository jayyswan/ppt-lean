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
import Pptc.GammaRational.HalfBeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Splitting the Beta integral in half

Mathlib's Beta integral is the full `B(α, β) = ∫₀¹ t ^ (α - 1) (1 - t) ^ (β - 1) dt`. Cut at
`t = 1/2` and reflect the right half by `t ↦ 1 - t`: that half is `halfBeta β α`, so

    B(α, β) = halfBeta α β + halfBeta β α.

Combined with `Complex.Gamma_mul_Gamma_eq_betaIntegral` and `Γ(1/2) = √π` this gives the
product identity the whole development is built on:

    Γ(ρ) Γ(1/2 - ρ) = √π · (halfBeta ρ (1/2 - ρ) + halfBeta (1/2 - ρ) ρ)   (0 < ρ < 1/2).

Only this half-split is needed; the improper `∫₀^∞` and the Beta integral of the second kind
that the paper uses are avoided entirely. -/

namespace Pconstructible

open MeasureTheory

-- Theorem: the complex Beta integral of nonnegative real arguments is the sum of the two
-- real half-Beta integrals.
theorem betaIntegral_ofReal_eq_halfBeta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Complex.betaIntegral α β = ((halfBeta α β + halfBeta β α : ℝ) : ℂ) := by
  have hreal : Complex.betaIntegral α β
      = ((∫ x in (0 : ℝ)..1, x ^ (α - 1) * (1 - x) ^ (β - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hx1 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
    push_cast
    rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow hx1]
    push_cast
    rfl
  have hf1 : IntervalIntegrable
      (fun x : ℝ => x ^ (α - 1) * (1 - x) ^ (β - 1)) volume (0 : ℝ) (1 / 2) := by
    have hin : IntervalIntegrable (fun x : ℝ => x ^ (α - 1)) volume (0 : ℝ) (1 / 2) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)
    have hcont : ContinuousOn (fun x : ℝ => (1 - x) ^ (β - 1))
        (Set.uIcc (0 : ℝ) (1 / 2)) := by
      refine (continuousOn_const.sub continuousOn_id).rpow_const fun x hx => Or.inl ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
      change (1 : ℝ) - x ≠ 0
      have : (0 : ℝ) < 1 - x := by linarith [hx.2]
      exact this.ne'
    exact hin.mul_continuousOn hcont
  have hf2 : IntervalIntegrable
      (fun x : ℝ => x ^ (α - 1) * (1 - x) ^ (β - 1)) volume (1 / 2 : ℝ) 1 := by
    have hg : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (β - 1)) volume (1 / 2 : ℝ) 1 := by
      have h0 : IntervalIntegrable (fun x : ℝ => x ^ (β - 1)) volume (0 : ℝ) (1 / 2) :=
        intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β - 1)
      have h1 := (h0.comp_sub_left (1 : ℝ)).symm
      rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
        show (1 : ℝ) - 0 = 1 by norm_num] at h1
    have hcont : ContinuousOn (fun x : ℝ => x ^ (α - 1)) (Set.uIcc (1 / 2 : ℝ) 1) := by
      refine continuousOn_id.rpow_const fun x hx => Or.inl ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 1)] at hx
      exact (by linarith [hx.1] : (0 : ℝ) < x).ne'
    exact hg.continuousOn_mul hcont
  have hmain : (∫ x in (0 : ℝ)..1, x ^ (α - 1) * (1 - x) ^ (β - 1))
      = halfBeta α β + halfBeta β α := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hf1 hf2
    have hleft : (∫ x in (0 : ℝ)..(1 / 2), x ^ (α - 1) * (1 - x) ^ (β - 1))
        = halfBeta α β := by
      rw [halfBeta, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
        integral_Ioc_eq_integral_Ioo]
    have hright : (∫ x in (1 / 2 : ℝ)..1, x ^ (α - 1) * (1 - x) ^ (β - 1))
        = halfBeta β α := by
      rw [halfBeta]
      have hreflect : (∫ x in (1 / 2 : ℝ)..1, x ^ (α - 1) * (1 - x) ^ (β - 1))
          = ∫ x in (0 : ℝ)..(1 / 2),
              (1 - x) ^ (α - 1) * (1 - (1 - x)) ^ (β - 1) := by
        have := intervalIntegral.integral_comp_sub_left
          (fun x : ℝ => x ^ (α - 1) * (1 - x) ^ (β - 1)) (1 : ℝ)
            (a := (0 : ℝ)) (b := (1 / 2))
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
          show (1 : ℝ) - 0 = 1 by norm_num] at this
        exact this.symm
      rw [hreflect, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
        integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
      rw [show (1 : ℝ) - (1 - x) = x by ring, mul_comm]
    rw [← hsplit, hleft, hright]
  rw [hreal, hmain]

-- Theorem: Euler's Beta identity for the symmetric arguments `ρ`, `1/2 - ρ`.
theorem Gamma_mul_Gamma_half_sub {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1 / 2) :
    Real.Gamma ρ * Real.Gamma (1 / 2 - ρ)
      = Real.sqrt Real.pi * (halfBeta ρ (1 / 2 - ρ) + halfBeta (1 / 2 - ρ) ρ) := by
  have hpos : 0 < 1 / 2 - ρ := by linarith
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (ρ : ℂ))
    (t := ((1 / 2 - ρ : ℝ) : ℂ)) (by simpa using h0) (by simpa using hpos)
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    show (ρ : ℂ) + ((1 / 2 - ρ : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Real.Gamma_one_half_eq,
    betaIntegral_ofReal_eq_halfBeta h0 hpos] at h
  exact_mod_cast h

end Pconstructible
