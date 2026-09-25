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
import Pptc.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The power-law arc length `ℓ(σ)`

The paper's Lemma 2, as a curve and a tracing. The curve `y = b⁻¹ x ^ b` with `b = 1 + σ/2`
is (semantically) a `power_law` curve, and the tracing

    powerLawParam σ t = (t, (1 + σ/2)⁻¹ * t ^ (1 + σ/2))

runs along it for `t ∈ [0, 1]`. The arc starts at the origin, so its two plane endpoints
`(0, 0)` and `(1, (1 + σ/2)⁻¹)` are rational.

**This is where the development is conditional.** The real `power_law` constructor draws only
the half-line `x > 0`; it does *not* include the origin. The family is therefore correctly
stated as `PowerLawWithOrigin`: "there is a constructible power-law curve that does contain
the origin". Under that hypothesis the arc is a genuine closed interval, and `arc_length`
applied to this tracing returns

    ℓ(σ) = ∫₀¹ √(1 + x ^ σ) dx.

This file proves every analytic side condition (`speed_powerLawParam`,
`arcLengthOf_powerLawParam`, `powerLawParam_injOn`, `powerLawParam_differentiableAt`,
`powerLawParam_intervalIntegrable`) *unconditionally* — none of them touches a constructor.
The origin-inclusive *set* is also written down and membership in it is checked pointwise;
what is missing, and what `PowerLawWithOrigin` supplies, is that this set is a constructible
curve. The analytic conversion from `ℓ(σ)` to the *inverse*-square-root integral `A(σ)` is the
subject of `Pptc.GammaRational.Conversion`. -/

namespace Pconstructible

/-- **The one missing primitive, named as a hypothesis.** In this project the `power_law`
constructor draws only `x > 0`. If it were extended to include the origin whenever the
exponent is positive — that is, if the set `{(x, a x ^ b) : 0 < x ∨ (x = 0 ∧ 0 < b)}` were
a constructible curve — then `Γ` would be P-constructible at every rational. This `Prop`
packages that extension as a hypothesis so the rest of `Pptc.GammaRational` can be stated and
proved now, and becomes trivial (supplied by a single application of the constructor) the
moment the definitions are widened. The *only* use of `hPL` anywhere is the image side
condition `powerLawParam_image_subset` below; everything after it is unconditional. -/
def PowerLawWithOrigin : Prop :=
  ∀ a b : ℚ, 0 < b →
    PConstructibleCurve
      {pt : ℝ × ℝ | (0 < pt.1 ∨ (pt.1 = 0 ∧ 0 < b)) ∧ pt.2 = (a : ℝ) * pt.1 ^ (b : ℝ)}

/-- The tracing `t ↦ (t, (1 + σ/2)⁻¹ t ^ (1 + σ/2))` of the power-law curve with exponent
`1 + σ/2`, the arc whose length is `ℓ(σ)`. -/
noncomputable def powerLawParam (σ : ℝ) (t : ℝ) : ℝ × ℝ :=
  (t, (1 + σ / 2)⁻¹ * t ^ (1 + σ / 2))

-- Theorem: the speed of the power-law tracing is `√(1 + t ^ σ)`.
theorem speed_powerLawParam {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    speed (powerLawParam σ) t = Real.sqrt (1 + t ^ σ) := by
  have hb : 1 ≤ 1 + σ / 2 := by linarith
  have hb0 : (1 + σ / 2) ≠ 0 := by linarith
  have hderiv1 : deriv (fun s : ℝ => (powerLawParam σ s).1) t = 1 := by
    change deriv (fun s : ℝ => s) t = 1
    simp
  have hderiv2 : deriv (fun s : ℝ => (powerLawParam σ s).2) t = t ^ (σ / 2) := by
    change deriv (fun s : ℝ => (1 + σ / 2)⁻¹ * s ^ (1 + σ / 2)) t = t ^ (σ / 2)
    have h : HasDerivAt (fun s : ℝ => (1 + σ / 2)⁻¹ * s ^ (1 + σ / 2))
        ((1 + σ / 2)⁻¹ * ((1 + σ / 2) * t ^ ((1 + σ / 2) - 1))) t :=
      (Real.hasDerivAt_rpow_const (Or.inr hb)).const_mul _
    rw [h.deriv]
    rw [show (1 + σ / 2)⁻¹ * ((1 + σ / 2) * t ^ ((1 + σ / 2) - 1)) = t ^ (σ / 2) from by
      rw [← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
      congr 1
      ring]
  rw [speed, hderiv1, hderiv2, one_pow]
  have hsq : (t ^ (σ / 2)) ^ 2 = t ^ σ := by
    rw [← Real.rpow_natCast (t ^ (σ / 2)) 2,
      ← Real.rpow_mul ht (σ / 2) ((2 : ℕ) : ℝ)]
    congr 1
    push_cast
    ring
  rw [hsq]

-- Theorem: the length of the tracing is the integral of `√(1 + x ^ σ)` over `[0, 1]`.
theorem arcLengthOf_powerLawParam {σ : ℝ} (hσ : 0 < σ) :
    arcLengthOf (powerLawParam σ) 0 1 = ∫ x in (0 : ℝ)..1, Real.sqrt (1 + x ^ σ) := by
  rw [arcLengthOf]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le zero_le_one] at hx
  exact speed_powerLawParam hσ hx.1

-- Theorem: for rational `σ > 0` the tracing lands on the origin-inclusive `power_law` curve
-- with the matching rational data. The *set* is the one `PowerLawWithOrigin` asserts is a
-- curve; membership itself is checked pointwise and is unconditional. Stated so that
-- `exact PConstructibleCurve.power_law _ _` closes the constructor side goal after
-- `push_cast`.
theorem powerLawParam_image_subset {σ : ℚ} (hσ : 0 < σ) :
    powerLawParam σ '' Set.Icc 0 1 ⊆
      {pt : ℝ × ℝ | (0 < pt.1 ∨ (pt.1 = 0 ∧ 0 < (1 + σ / 2 : ℚ))) ∧
        pt.2 = (((1 + σ / 2)⁻¹ : ℚ) : ℝ) * pt.1 ^ (((1 + σ / 2 : ℚ)) : ℝ)} := by
  rintro pt ⟨t, ht, rfl⟩
  constructor
  · rcases eq_or_lt_of_le ht.1 with h | h
    · exact Or.inr ⟨h.symm, by linarith⟩
    · exact Or.inl h
  · simp only [powerLawParam]
    push_cast
    ring

-- Theorem: the tracing is injective on `[0, 1]`.
theorem powerLawParam_injOn (σ : ℝ) : Set.InjOn (powerLawParam σ) (Set.Icc 0 1) := by
  intro a _ b _ h
  simpa [powerLawParam] using congrArg Prod.fst h

-- Theorem: the tracing is differentiable at every parameter in `[0, 1]`.
theorem powerLawParam_differentiableAt {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    DifferentiableAt ℝ (fun s => (powerLawParam σ s).1) t ∧
      DifferentiableAt ℝ (fun s => (powerLawParam σ s).2) t := by
  have hb : 1 ≤ 1 + σ / 2 := by
    have ht0 : 0 ≤ t := ht.1
    linarith
  constructor
  · change DifferentiableAt ℝ (fun s : ℝ => s) t
    exact differentiableAt_id
  · change DifferentiableAt ℝ (fun s : ℝ => (1 + σ / 2)⁻¹ * s ^ (1 + σ / 2)) t
    exact (DifferentiableAt.rpow_const differentiableAt_id (Or.inr hb)).const_mul _

-- Theorem: the speed is interval-integrable on `[0, 1]`.
theorem powerLawParam_intervalIntegrable {σ : ℝ} (hσ : 0 < σ) :
    IntervalIntegrable (speed (powerLawParam σ)) MeasureTheory.volume 0 1 := by
  have hcont : Continuous fun t : ℝ => Real.sqrt (1 + t ^ σ) :=
    Continuous.sqrt (continuous_const.add
      (continuous_id.rpow_const fun _ => Or.inr hσ.le))
  have hf : IntervalIntegrable (fun t : ℝ => Real.sqrt (1 + t ^ σ))
      MeasureTheory.volume 0 1 := hcont.intervalIntegrable 0 1
  refine IntervalIntegrable.congr ?_ hf
  intro x hx
  rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hx
  exact (speed_powerLawParam hσ hx.1.le).symm

end Pconstructible
