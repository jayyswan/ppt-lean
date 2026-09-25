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
import Pptc.GammaRational.ArcLength
import Pptc.GammaRational.Conversion
import Pptc.GammaRational.Substitution
import Pptc.GammaRational.BetaSplit
import Pptc.GammaRational.HalfShift
import Pptc.GammaRational.Doubling

/-! # `Γ(q)` is P-constructible for every rational `q`, conditional on the origin

**Status: conditional and currently unrealizable.** This development proves the *implication*
"if a constructible power-law curve can include the origin, then `Γ(q)` is P-constructible at
every rational `q`". The antedecent is the hypothesis `PowerLawWithOrigin` created in
`Pptc.GammaRational.ArcLength`. The real `power_law` constructor in `Pptc.Defs` draws only
the half-line `x > 0` and does **not** include the origin, so `PowerLawWithOrigin` is *not*
currently provable and the final result here is *not* unconditional. This is deliberate: the
`Defs` change that widened `power_law` was reverted because it made several existing proofs
false, and this file preserves the machinery that would immediately give
`∀ q : ℚ, PConstructible (Real.Gamma q)` if the constructor were ever widened.

The paper `gamma-power-laws.pdf` ("Γ at every rational from power-law arc lengths") assumes
the origin is on the curve; Mathlib's `Real.rpow` would additionally place a spurious origin
on `y = a / x` (a negative `b`), whence the `0 < b` guard in `PowerLawWithOrigin`.

Each piece is a single step of one chain:

* `powerLawArc_Pconstructible hPL` — the origin-inclusive `power_law` curve with exponent
  `1 + σ/2`, traced by `powerLawParam`, has arc length `ℓ(σ) = ∫₀¹ √(1 + x ^ σ)`, so
  `arc_length` makes `ℓ(σ)` P-constructible (`ArcLength`).
* `inv_sqrt_integral_Pconstructible hPL` — `A(σ) = ∫₀¹ dx / √(1 + x ^ σ)` is the affine
  function `(1 + 2/σ) ℓ(σ) - 2√2/σ` of it (`Conversion`).
* `halfProducts hPL` — the substitution `t = x ^ σ / (1 + x ^ σ)` identifies
  `halfBeta σ⁻¹ (1/2 - σ⁻¹)` with `σ A(σ)` (`Substitution`), and the half-split Beta integral
  turns `Γ(ρ) Γ(1/2 - ρ)` into `√π (halfBeta ρ (1/2 - ρ) + halfBeta (1/2 - ρ) ρ)`
  (`BetaSplit`), which is therefore P-constructible for every rational `ρ ∈ (0, 1/2)`.
* `Gamma_rat_Pconstructible hPL` — the half-products give the half-shift and doubling ratios
  (`HalfShift`), and the doubling ratio reaches every rational (`Doubling`).

Together these settle *every* rational argument, with no new transcendental input beyond the
origin-inclusive `power_law`. The paper's Example 9, curves with exponents
`7/2, 8/3, 9/4, 6`, is the `σ = 5/2, 3/2, 1/2, 4` cases of the same arc. -/

namespace Pconstructible

-- Lemma: the power-law tracing starts at the origin.
private theorem powerLawParam_zero {σ : ℝ} (hσ : 0 < σ) :
    powerLawParam σ 0 = (0, 0) := by
  have hb : (1 + σ / 2) ≠ 0 := ne_of_gt (by linarith)
  simp [powerLawParam, Real.zero_rpow hb]

-- Lemma: the power-law tracing ends at `(1, (1 + σ/2)⁻¹)`.
private theorem powerLawParam_one (σ : ℝ) :
    powerLawParam σ 1 = (1, (1 + σ / 2)⁻¹) := by
  simp [powerLawParam]

-- Theorem: the power-law arc length `ℓ(σ)` is P-constructible for every rational `σ > 0`,
-- conditional on the origin-inclusive power law.
theorem powerLawArc_Pconstructible (hPL : PowerLawWithOrigin) (σ : ℚ) (hσ : 0 < σ) :
    PConstructible (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x ^ (σ : ℝ))) := by
  have hσR : (0 : ℝ) < (σ : ℝ) := by exact_mod_cast hσ
  rw [← arcLengthOf_powerLawParam (σ := (σ : ℝ)) hσR]
  refine PConstructible.arc_length
    (hPL ((1 + σ / 2)⁻¹) (1 + σ / 2) (by linarith))
    (powerLawParam (σ : ℝ)) zero_le_one ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact powerLawParam_image_subset hσ
  · exact powerLawParam_injOn (σ : ℝ)
  · intro t ht
    exact powerLawParam_differentiableAt hσR ht
  · exact powerLawParam_intervalIntegrable hσR
  · rw [powerLawParam_zero hσR]
    exact zero_Pconstructible
  · rw [powerLawParam_zero hσR]
    exact zero_Pconstructible
  · rw [powerLawParam_one]
    exact PConstructible.base_one
  · rw [powerLawParam_one]
    exact inv_Pconstructible (ratval_Pconstructible (1 + σ / 2) (by push_cast; ring))

-- Theorem: the inverse-square-root integral `A(σ)` is P-constructible for rational `σ > 0`,
-- conditional on the origin-inclusive power law.
theorem inv_sqrt_integral_Pconstructible (hPL : PowerLawWithOrigin) (σ : ℚ) (hσ : 0 < σ) :
    PConstructible (∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ (σ : ℝ)))⁻¹) := by
  have hσR : (0 : ℝ) < (σ : ℝ) := by exact_mod_cast hσ
  have hσP : PConstructible (σ : ℝ) := ratval_Pconstructible σ rfl
  rw [integral_inv_sqrt_one_add_rpow hσR]
  refine PConstructible.sub
    (PConstructible.mul (by pconstructible) (powerLawArc_Pconstructible hPL σ hσ))
    (by pconstructible)

-- Theorem: the analytic half delivers its promise — the products `Γ(ρ) Γ(1/2 - ρ)` —
-- conditional on the origin-inclusive power law.
theorem halfProducts (hPL : PowerLawWithOrigin) : HalfProducts := by
  intro ρ h0 h1
  have h0R : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast h0
  have h1R : (ρ : ℝ) < 1 / 2 := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr h1
  have hpos : (0 : ℝ) < 1 / 2 - (ρ : ℝ) := by linarith
  rw [Gamma_mul_Gamma_half_sub h0R h1R]
  have hb1 : halfBeta (ρ : ℝ) (1 / 2 - (ρ : ℝ))
      = (ρ : ℝ)⁻¹ * ∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ ((ρ : ℝ)⁻¹)))⁻¹ := by
    have h := halfBeta_inv_eq (σ := (ρ : ℝ)⁻¹) (inv_pos.mpr h0R)
    simpa only [inv_inv] using h
  have hb2 : halfBeta (1 / 2 - (ρ : ℝ)) (ρ : ℝ)
      = (1 / 2 - (ρ : ℝ))⁻¹
          * ∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ ((1 / 2 - (ρ : ℝ))⁻¹)))⁻¹ := by
    have h := halfBeta_inv_eq (σ := (1 / 2 - (ρ : ℝ))⁻¹) (inv_pos.mpr hpos)
    rw [inv_inv] at h
    rw [show (1 / 2 : ℝ) - (1 / 2 - (ρ : ℝ)) = (ρ : ℝ) by ring] at h
    exact h
  rw [hb1, hb2]
  refine PConstructible.mul sqrt_pi_Pconstructible (PConstructible.add ?_ ?_)
  · have hA : PConstructible (∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ ((ρ : ℝ)⁻¹)))⁻¹) := by
      simpa using inv_sqrt_integral_Pconstructible hPL (ρ⁻¹) (inv_pos.mpr h0)
    exact PConstructible.mul (ratval_Pconstructible (ρ⁻¹) (by push_cast; rfl)) hA
  · have hq : (0 : ℚ) < 1 / 2 - ρ := by linarith
    have hA : PConstructible
        (∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ ((1 / 2 - (ρ : ℝ))⁻¹)))⁻¹) := by
      simpa using inv_sqrt_integral_Pconstructible hPL ((1 / 2 - ρ)⁻¹) (inv_pos.mpr hq)
    exact PConstructible.mul (ratval_Pconstructible ((1 / 2 - ρ)⁻¹) (by push_cast; rfl)) hA

-- Theorem: `Γ(q)` is P-constructible for every rational `q`, conditional on the
-- origin-inclusive power law. This is the paper's theorem; without `PowerLawWithOrigin` the
-- hypothesis is not currently satisfiable.
theorem Gamma_rat_Pconstructible (hPL : PowerLawWithOrigin) (q : ℚ) :
    PConstructible (Real.Gamma q) :=
  Gamma_rat_Pconstructible_of_dup
    (Gamma_sq_div_Gamma_two_mul_Pconstructible (halfProducts hPL)) q

-- Theorem: the paper's worked example, `Γ(1/5)`, as a one-liner.
theorem Gamma_one_fifth_Pconstructible (hPL : PowerLawWithOrigin) :
    PConstructible (Real.Gamma (1 / 5)) := by
  convert Gamma_rat_Pconstructible hPL (1 / 5 : ℚ) using 1
  norm_num

end Pconstructible
