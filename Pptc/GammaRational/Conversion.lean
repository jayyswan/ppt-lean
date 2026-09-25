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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # From the arc length `ℓ(σ)` to the integral `A(σ)`

The arc length `ℓ(σ) = ∫₀¹ √(1 + x ^ σ) dx` is what `arc_length` hands back, but the
substitution of `Pptc.GammaRational.Substitution` lands on the *inverse* square root:

    A(σ) = ∫₀¹ dx / √(1 + x ^ σ).

The two are related by an exact antiderivative. Differentiating `F x = x √(1 + x ^ σ)` on
`(0, 1)` gives

    F' x = (1 + σ/2) √(1 + x ^ σ) - (σ/2) / √(1 + x ^ σ),

so integrating over `[0, 1]` and using `F 1 = √2`, `F 0 = 0` yields

    A(σ) = (1 + 2/σ) ℓ(σ) - 2 √2 / σ.

The fundamental theorem is applied on the *open* interval `(0, 1)` only: `x ^ σ` need not be
differentiable at `0` when `σ < 1`, so the derivative identity is not available on the closed
interval. The integrand is nevertheless continuous on `[0, 1]`, which supplies the
integrability the theorem asks for. -/

namespace Pconstructible

-- Theorem: the inverse-square-root integral is an explicit affine function of the arc
-- length integral.
theorem integral_inv_sqrt_one_add_rpow {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ σ))⁻¹
      = (1 + 2 / σ) * (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x ^ σ)) - 2 * Real.sqrt 2 / σ := by
  let F : ℝ → ℝ := fun x => x * Real.sqrt (1 + x ^ σ)
  let G : ℝ → ℝ := fun x => (1 + σ / 2) * Real.sqrt (1 + x ^ σ)
      - (σ / 2) * (Real.sqrt (1 + x ^ σ))⁻¹
  have hbase : Continuous fun x : ℝ => 1 + x ^ σ :=
    continuous_const.add (Real.continuous_rpow_const hσ.le)
  have hsqrt : Continuous fun x : ℝ => Real.sqrt (1 + x ^ σ) :=
    Real.continuous_sqrt.comp hbase
  -- `1 + x ^ σ > 0` on `[0, 1]`, so the square root never vanishes there.
  have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + x ^ σ := by
    intro x hx
    have hxn : 0 ≤ x ^ σ := Real.rpow_nonneg hx.1 σ
    linarith
  have hsne : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (1 + x ^ σ) ≠ 0 :=
    fun x hx => ne_of_gt (Real.sqrt_pos.2 (hpos x hx))
  have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt (1 + x ^ σ))⁻¹) (Set.Icc (0 : ℝ) 1) :=
    hsqrt.continuousOn.inv₀ hsne
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun x : ℝ => x * Real.sqrt (1 + x ^ σ)) (Set.Icc (0 : ℝ) 1)
    exact (continuous_id.mul hsqrt).continuousOn
  have hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun x : ℝ => (1 + σ / 2) * Real.sqrt (1 + x ^ σ)
      - (σ / 2) * (Real.sqrt (1 + x ^ σ))⁻¹) (Set.Icc (0 : ℝ) 1)
    exact ((continuous_const.mul hsqrt).continuousOn).sub
      (continuous_const.continuousOn.mul hinv)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt F (G x) (Set.Ioi x) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hs : Real.sqrt (1 + x ^ σ) ≠ 0 := hsne x hxIcc
    have harg : (1 + x ^ σ) ≠ 0 := ne_of_gt (hpos x hxIcc)
    have hb : HasDerivAt (fun y : ℝ => (1 : ℝ) + y ^ σ) (σ * x ^ (σ - 1)) x :=
      (Real.hasDerivAt_rpow_const (x := x) (p := σ) (Or.inl hx0.ne')).const_add 1
    have hcomp : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ σ))
        ((1 / (2 * Real.sqrt (1 + x ^ σ))) * (σ * x ^ (σ - 1))) x :=
      (Real.hasDerivAt_sqrt harg).comp x hb
    have hF' : HasDerivAt F (Real.sqrt (1 + x ^ σ)
        + x * ((1 / (2 * Real.sqrt (1 + x ^ σ))) * (σ * x ^ (σ - 1)))) x := by
      have h0 : HasDerivAt (fun y : ℝ => y * Real.sqrt (1 + y ^ σ))
          (1 * Real.sqrt (1 + x ^ σ)
            + x * ((1 / (2 * Real.sqrt (1 + x ^ σ))) * (σ * x ^ (σ - 1)))) x :=
        (hasDerivAt_id x).mul hcomp
      have h1 : (1 * Real.sqrt (1 + x ^ σ)
            + x * ((1 / (2 * Real.sqrt (1 + x ^ σ))) * (σ * x ^ (σ - 1))))
          = Real.sqrt (1 + x ^ σ)
            + x * ((1 / (2 * Real.sqrt (1 + x ^ σ))) * (σ * x ^ (σ - 1))) := by ring
      rw [h1] at h0
      exact h0
    have hsq : (Real.sqrt (1 + x ^ σ)) ^ 2 = 1 + x ^ σ :=
      Real.sq_sqrt (le_of_lt (hpos x hxIcc))
    have hxpow : x * x ^ (σ - 1) = x ^ σ := by
      have h := Real.rpow_add hx0 (σ - 1) 1
      rw [Real.rpow_one] at h
      rw [mul_comm, ← h]
      congr 1
      ring
    have hD : Real.sqrt (1 + x ^ σ)
        + x * ((1 / (2 * Real.sqrt (1 + x ^ σ))) * (σ * x ^ (σ - 1)))
        = G x := by
      have e1 : x * ((1 / (2 * Real.sqrt (1 + x ^ σ))) * (σ * x ^ (σ - 1)))
          = (σ / (2 * Real.sqrt (1 + x ^ σ))) * (x * x ^ (σ - 1)) := by ring
      rw [e1, hxpow]
      change Real.sqrt (1 + x ^ σ) + (σ / (2 * Real.sqrt (1 + x ^ σ))) * x ^ σ
        = (1 + σ / 2) * Real.sqrt (1 + x ^ σ)
          - (σ / 2) * (Real.sqrt (1 + x ^ σ))⁻¹
      field_simp [hs]
      rw [hsq]
      ring
    rw [hD] at hF'
    exact hF'.hasDerivWithinAt
  have hFTC : ∫ x in (0 : ℝ)..1, G x = Real.sqrt 2 := by
    have hmain := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      (by norm_num : (0 : ℝ) ≤ 1) hFcont hderiv
      (hGcont.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1))
    have hF1 : F 1 = Real.sqrt 2 := by
      change (1 : ℝ) * Real.sqrt (1 + (1 : ℝ) ^ σ) = Real.sqrt 2
      rw [Real.one_rpow]
      norm_num
    have hF0 : F 0 = 0 := by
      change (0 : ℝ) * Real.sqrt (1 + (0 : ℝ) ^ σ) = 0
      ring
    rw [hF1, hF0] at hmain
    simpa using hmain
  have hLint : IntervalIntegrable (fun x : ℝ => (1 + σ / 2) * Real.sqrt (1 + x ^ σ))
      MeasureTheory.volume (0 : ℝ) 1 :=
    (continuous_const.mul hsqrt).intervalIntegrable 0 1
  have hAint : IntervalIntegrable (fun x : ℝ => (σ / 2) * (Real.sqrt (1 + x ^ σ))⁻¹)
      MeasureTheory.volume (0 : ℝ) 1 :=
    (continuous_const.continuousOn.mul hinv).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hlin : ∫ x in (0 : ℝ)..1, G x
      = (1 + σ / 2) * (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x ^ σ))
        - (σ / 2) * (∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ σ))⁻¹) := by
    rw [show G = (fun x : ℝ => (1 + σ / 2) * Real.sqrt (1 + x ^ σ))
        - (fun x : ℝ => (σ / 2) * (Real.sqrt (1 + x ^ σ))⁻¹) from rfl]
    simp only [Pi.sub_apply]
    rw [intervalIntegral.integral_sub hLint hAint,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hkey : (1 + σ / 2) * (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x ^ σ))
      - (σ / 2) * (∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ σ))⁻¹)
      = Real.sqrt 2 := hlin.symm.trans hFTC
  field_simp [hσ.ne']
  simp only [one_div]
  linear_combination (-2) * hkey

end Pconstructible
