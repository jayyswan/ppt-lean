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
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # The substitution `t = x ^ σ / (1 + x ^ σ)`

The analytic heart of the reduction. The map

    φ x = x ^ σ / (1 + x ^ σ)

carries `(0, 1)` strictly increasingly onto `(0, 1/2)`, and pulling the half-Beta integrand
back along it collapses to a constant times the inverse square root:

    t ^ (σ⁻¹ - 1) (1 - t) ^ (1/2 - σ⁻¹ - 1) · φ' x = σ / √(1 + x ^ σ).

Indeed `t = x^σ (1+x^σ)⁻¹` gives `t ^ (σ⁻¹ - 1) = x ^ (1 - σ) (1 + x^σ) ^ (1 - σ⁻¹)` and
`(1 - t) ^ (-1/2 - σ⁻¹) = (1 + x^σ) ^ (1/2 + σ⁻¹)`, while
`φ' x = σ x ^ (σ - 1) (1 + x^σ)⁻²`; the powers of `x` cancel and the powers of `1 + x^σ`
collapse to `(1 + x^σ) ^ (-1/2)`.

Because the integrand is unbounded at `0`, the substitution is performed with the
measure-theoretic `integral_image_eq_integral_abs_deriv_smul` on the *open* interval, which
needs a derivative and injectivity and asks for no integrability hypothesis at all — the
same device the Beta-integral changes of variables in `Pptc.Gamma` use. -/

namespace Pconstructible

open MeasureTheory Set

/-- The substitution `φ x = x ^ σ / (1 + x ^ σ)`. -/
private noncomputable def phi (σ : ℝ) (x : ℝ) : ℝ := x ^ σ / (1 + x ^ σ)

/-- The derivative of `phi`. -/
private noncomputable def phiDeriv (σ : ℝ) (x : ℝ) : ℝ := σ * x ^ (σ - 1) / (1 + x ^ σ) ^ 2

private theorem phi_hasDerivAt {σ : ℝ} (_hσ : 0 < σ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (phi σ) (phiDeriv σ x) x := by
  have hx0 : 0 < x := hx.1
  have hd : HasDerivAt (fun y : ℝ => y ^ σ) (σ * x ^ (σ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ σ) (σ * x ^ (σ - 1)) x := by
    simpa using hd.const_add 1
  have hq : (1 + x ^ σ) ≠ 0 := by
    have : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    positivity
  have h := hd.div h1 hq
  have hval : phiDeriv σ x
      = (σ * x ^ (σ - 1) * (1 + x ^ σ) - x ^ σ * (σ * x ^ (σ - 1))) / (1 + x ^ σ) ^ 2 := by
    rw [phiDeriv]
    ring
  rw [hval]
  have h' : HasDerivAt (fun y : ℝ => y ^ σ / (1 + y ^ σ))
      ((σ * x ^ (σ - 1) * (1 + x ^ σ) - x ^ σ * (σ * x ^ (σ - 1))) / (1 + x ^ σ) ^ 2) x :=
    h
  exact h'

private theorem phi_pos {σ : ℝ} (_hσ : 0 < σ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < phi σ x := by
  have hx0 : 0 < x := hx.1
  have hp : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
  rw [phi]
  positivity

private theorem phi_lt_half {σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    phi σ x < 1 / 2 := by
  have hx0 : 0 < x := hx.1
  have hp : x ^ σ < 1 := (Real.rpow_lt_one_iff_of_pos hx0).2 (Or.inr ⟨hx.2, hσ⟩)
  have hq : 0 < 1 + x ^ σ := by
    have : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    linarith
  rw [phi, div_lt_iff₀ hq]
  linarith

private theorem phi_image_Ioo {σ : ℝ} (hσ : 0 < σ) :
    phi σ '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) (1 / 2) := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨phi_pos hσ hx, phi_lt_half hσ hx⟩
  · intro ht
    have ht0 : 0 < t := ht.1
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have hb0 : 0 < t / (1 - t) := div_pos ht0 h1t
    have hb1 : t / (1 - t) < 1 := (div_lt_one h1t).2 (by linarith [ht.2])
    refine ⟨(t / (1 - t)) ^ (1 / σ), ⟨Real.rpow_pos_of_pos hb0 _, ?_⟩, ?_⟩
    · exact (Real.rpow_lt_one_iff_of_pos hb0).2 (Or.inr ⟨hb1, one_div_pos.mpr hσ⟩)
    · have hpow : ((t / (1 - t)) ^ (1 / σ)) ^ σ = t / (1 - t) := by
        rw [← Real.rpow_mul hb0.le]
        have h1 : (1 / σ) * σ = 1 := by field_simp
        rw [h1, Real.rpow_one]
      rw [phi, hpow]
      field_simp
      ring

private theorem phi_injOn {σ : ℝ} (hσ : 0 < σ) : InjOn (phi σ) (Ioo (0 : ℝ) 1) := by
  refine (strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1) ?_ ?_).injOn
  · intro x hx
    exact (phi_hasDerivAt hσ hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    have hx0 : 0 < x := hx.1
    have hp : 0 < x ^ (σ - 1) := Real.rpow_pos_of_pos hx0 _
    have hq : 0 < (1 + x ^ σ) ^ 2 := by
      have : 0 < 1 + x ^ σ := by
        have := Real.rpow_pos_of_pos hx0 σ
        linarith
      positivity
    rw [(phi_hasDerivAt hσ hx).deriv, phiDeriv]
    positivity

/-- Combining `(u / v) ^ a` with `(v⁻¹) ^ b` for positive `u`, `v`. -/
private theorem div_rpow_mul_inv_rpow {u v a b : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (u / v) ^ a * v⁻¹ ^ b = u ^ a * v ^ (-(a + b)) := by
  rw [Real.div_rpow hu.le hv.le, Real.inv_rpow hv.le]
  have h1 : u ^ a / v ^ a * (v ^ b)⁻¹ = u ^ a * ((v ^ a)⁻¹ * (v ^ b)⁻¹) := by ring
  rw [h1, ← mul_inv, ← Real.rpow_add hv, Real.rpow_neg hv.le]

-- Theorem: pointwise collapse of the pulled-back half-Beta integrand. On `(0, 1)` the
-- Jacobian `φ'` and the two `rpow` factors multiply to `σ / √(1 + x ^ σ)`.
private theorem phi_integrand_eq {σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |phiDeriv σ x| • (phi σ x ^ (σ⁻¹ - 1) * (1 - phi σ x) ^ (1 / 2 - σ⁻¹ - 1))
      = σ * (Real.sqrt (1 + x ^ σ))⁻¹ := by
  have hx0 : 0 < x := hx.1
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hp : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
  have hq : 0 < 1 + x ^ σ := by linarith
  have hdpos : 0 < phiDeriv σ x := by
    rw [phiDeriv]
    positivity
  have h1phi : 1 - phi σ x = (1 + x ^ σ)⁻¹ := by
    rw [phi]
    field_simp
    ring
  have hxp : (x ^ σ) ^ (σ⁻¹ - 1) = x ^ (1 - σ) := by
    rw [← Real.rpow_mul hx0.le, mul_sub, mul_inv_cancel₀ hσne, mul_one]
  have hR : phi σ x ^ (σ⁻¹ - 1) * (1 - phi σ x) ^ (1 / 2 - σ⁻¹ - 1)
      = x ^ (1 - σ) * (1 + x ^ σ) ^ ((3 : ℝ) / 2) := by
    rw [h1phi, phi, div_rpow_mul_inv_rpow hp hq, hxp]
    congr 1
    ring_nf
  have hxcomb : x ^ (σ - 1) * x ^ (1 - σ) = 1 := by
    rw [← Real.rpow_add hx0, show σ - 1 + (1 - σ) = 0 by ring, Real.rpow_zero]
  have hqcomb : (1 + x ^ σ) ^ ((3 : ℝ) / 2) / (1 + x ^ σ) ^ 2
      = (Real.sqrt (1 + x ^ σ))⁻¹ := by
    rw [← Real.rpow_natCast (1 + x ^ σ) 2, ← Real.rpow_sub hq]
    rw [show (3 : ℝ) / 2 - ((2 : ℕ) : ℝ) = -(1 / 2) by norm_num, Real.sqrt_eq_rpow,
      Real.rpow_neg hq.le]
  rw [hR, smul_eq_mul, abs_of_pos hdpos, phiDeriv]
  rw [show σ * x ^ (σ - 1) / (1 + x ^ σ) ^ 2 * (x ^ (1 - σ) * (1 + x ^ σ) ^ ((3 : ℝ) / 2))
        = σ * (x ^ (σ - 1) * x ^ (1 - σ)) * ((1 + x ^ σ) ^ ((3 : ℝ) / 2)
            / (1 + x ^ σ) ^ 2) by ring,
    hxcomb, hqcomb, mul_one]

-- Theorem: `halfBeta` at the reciprocal arguments is `σ` times the inverse-square-root
-- integral.
theorem halfBeta_inv_eq {σ : ℝ} (hσ : 0 < σ) :
    halfBeta σ⁻¹ (1 / 2 - σ⁻¹) = σ * ∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ σ))⁻¹ := by
  rw [halfBeta, ← phi_image_Ioo hσ]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun x hx => (phi_hasDerivAt hσ hx).hasDerivWithinAt) (phi_injOn hσ)]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => phi_integrand_eq hσ hx),
    integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

end Pconstructible
