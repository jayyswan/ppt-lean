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

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
-- `GoursatGeneral` supplies the quadratic transformation `hyp_goursat`, `GaussRational` the
-- lifted Gauss summation theorem at `z = 1` together with its rational P-constructibility,
-- and `GammaFunctional` the P-constructibility of `√π`.
import Pptc.Hypergeometric.GoursatGeneral
import Pptc.Hypergeometric.GaussRational
import Pptc.GammaFunctional

/-! # Gauss's second theorem

Gauss's second summation theorem for the hypergeometric function,

`₂F₁(a, b; (a + b + 1)/2; 1/2) = √π Γ((a + b + 1)/2) / (Γ((a + 1)/2) Γ((b + 1)/2))`,

together with the P-constructibility of the left-hand side at rational `a`, `b`.

The proof is the `z → 1/2⁻` limit of Goursat's quadratic transformation. With
`α = a/2`, `β = b/2` and `c = (a + b + 1)/2 = α + β + 1/2`, the transformation reads

`₂F₁(a, b; c; z) = ₂F₁(α, β; c; 4z(1-z))` for `0 ≤ z < 1/2`.

As `z → 1/2⁻` the argument `4z(1-z) = 1 - (2z-1)²` increases to `1`, and because
`c - α - β = 1/2 > 0` Abel's theorem (`tendsto_hyp_nhdsWithin_one`) gives

`₂F₁(α, β; c; 4z(1-z)) → ₂F₁(α, β; c; 1)`.

The left-hand side `₂F₁(a, b; c; ·)` is analytic at `1/2` (it is the sum of its power
series on the unit disc), so it also has a limit there; uniqueness of limits identifies
`₂F₁(a, b; c; 1/2)` with `₂F₁(α, β; c; 1)`. Gauss's summation theorem at `1` then gives
`Γ(c) Γ(1/2) / (Γ(c - α) Γ(c - β))`, and `Γ(1/2) = √π` finishes the identity.

For the constructibility statement, every `Γ` argument occurring is rational once `a` and
`b` are, and `√π` is P-constructible, so `PConstructible.div` finishes.
-/

open scoped Topology ENNReal

namespace Pconstructible

noncomputable section

-- Theorem: Gauss's second summation theorem,
-- `₂F₁(A,B;(A+B+1)/2;1/2) = √π Γ((A+B+1)/2) / (Γ((A+1)/2) Γ((B+1)/2))`.
theorem hyp_second {A B : ℝ}
    (hAB : ∀ n : ℕ, (A + B + 1) / 2 ≠ -(n : ℝ))
    (hA : ∀ n : ℕ, (A + 1) / 2 ≠ -(n : ℝ))
    (hB : ∀ n : ℕ, (B + 1) / 2 ≠ -(n : ℝ)) :
    hyp A B ((A + B + 1) / 2) (1 / 2) =
      Real.sqrt Real.pi * Real.Gamma ((A + B + 1) / 2) /
        (Real.Gamma ((A + 1) / 2) * Real.Gamma ((B + 1) / 2)) := by
  set c : ℝ := (A + B + 1) / 2 with hc_def
  have hc_eq : c = A / 2 + B / 2 + 1 / 2 := by rw [hc_def]; ring
  have hABc : ∀ n : ℕ, c ≠ -(n : ℝ) := by intro n; rw [hc_def]; exact hAB n
  have hca' : ∀ n : ℕ, c - A / 2 ≠ -(n : ℝ) := by
    intro n
    rw [show c - A / 2 = (B + 1) / 2 by rw [hc_def]; ring]
    exact hB n
  have hcb' : ∀ n : ℕ, c - B / 2 ≠ -(n : ℝ) := by
    intro n
    rw [show c - B / 2 = (A + 1) / 2 by rw [hc_def]; ring]
    exact hA n
  have hcab : 0 < c - A / 2 - B / 2 := by rw [hc_def]; linarith
  -- The pole hypothesis of Goursat's transformation.
  have hcG : ∀ n : ℕ, A / 2 + B / 2 + 1 / 2 ≠ -(n : ℝ) := by
    intro n
    rw [← hc_eq]
    exact hABc n
  -- The right-hand side tends to `₂F₁(A/2, B/2; c; 1)` as `z → 1/2⁻`.
  have h_limR : Filter.Tendsto (fun z : ℝ => hyp (A / 2) (B / 2) c (4 * z * (1 - z)))
      (𝓝[<] (1 / 2)) (𝓝 (hyp (A / 2) (B / 2) c 1)) := by
    refine (tendsto_hyp_nhdsWithin_one hcab).comp ?_
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hct : ContinuousAt (fun z : ℝ => 4 * z * (1 - z)) (1 / 2) :=
        ((continuous_const.mul continuous_id).mul
          (continuous_const.sub continuous_id)).continuousAt
      have h1 : Filter.Tendsto (fun z : ℝ => 4 * z * (1 - z)) (𝓝 (1 / 2)) (𝓝 1) := by
        convert hct.tendsto using 2
        norm_num
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z < 1 / 2 := hz
      have hne : 2 * z - 1 ≠ 0 := by intro h; linarith
      have hsq : 0 < (2 * z - 1) ^ 2 := sq_pos_of_ne_zero hne
      have hid : 4 * z * (1 - z) = 1 - (2 * z - 1) ^ 2 := by ring
      change 4 * z * (1 - z) < 1
      rw [hid]
      linarith
  -- The left-hand side is continuous at `1/2`, which is inside the unit disc.
  have h_limL : Filter.Tendsto (fun z : ℝ => hyp A B c z) (𝓝[<] (1 / 2))
      (𝓝 (hyp A B c (1 / 2))) := by
    let S : FormalMultilinearSeries ℝ ℝ ℝ := ordinaryHypergeometricSeries ℝ A B c
    have hrad : (1 : ℝ≥0∞) ≤ S.radius :=
      one_le_hypergeometric_radius (a := A) (b := B) (c := c) hABc
    have hpos : 0 < S.radius := lt_of_lt_of_le (by norm_num) hrad
    have hball : AnalyticOnNhd ℝ (fun z : ℝ => hyp A B c z) (Metric.eball 0 (1 : ℝ≥0∞)) :=
      ((S.hasFPowerSeriesOnBall hpos).analyticOnNhd).mono (Metric.eball_subset_eball hrad)
    have hmem : (1 / 2 : ℝ) ∈ Metric.eball 0 (1 : ℝ≥0∞) := by
      rw [mem_eball_zero_iff, enorm_eq_nnnorm]
      simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
      norm_num
    exact ((hball (1 / 2) hmem).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  -- Goursat identifies the two functions eventually below `1/2`.
  have h_eq_ev : (fun z : ℝ => hyp A B c z) =ᶠ[𝓝[<] (1 / 2)]
      fun z : ℝ => hyp (A / 2) (B / 2) c (4 * z * (1 - z)) := by
    have hz0 : ∀ᶠ z : ℝ in 𝓝[<] (1 / 2), 0 < z :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hz0] with z hz hz0
    have h := hyp_goursat (a := A / 2) (b := B / 2) hcG (le_of_lt hz0) hz
    rw [show 2 * (A / 2) = A by ring, show 2 * (B / 2) = B by ring, ← hc_eq] at h
    exact h
  have hmain : hyp A B c (1 / 2) = hyp (A / 2) (B / 2) c 1 :=
    tendsto_nhds_unique h_limL (h_limR.congr' h_eq_ev.symm)
  rw [hmain]
  rw [hyp_one_eq_Gamma' (a := A / 2) (b := B / 2) (c := c) hcab hca' hcb' hABc]
  rw [show c - A / 2 - B / 2 = 1 / 2 by rw [hc_def]; ring,
    show c - A / 2 = (B + 1) / 2 by rw [hc_def]; ring,
    show c - B / 2 = (A + 1) / 2 by rw [hc_def]; ring]
  rw [Real.Gamma_one_half_eq]
  ring

-- Theorem: `₂F₁(A,B;(A+B+1)/2;1/2)` is P-constructible for rational `A`, `B` whose
-- three Gamma arguments `(A+B+1)/2`, `(A+1)/2`, `(B+1)/2` are not nonpositive integers.
theorem hyp_second_rat_Pconstructible {A B : ℚ}
    (hAB : ∀ n : ℕ, ((A + B + 1) / 2 : ℚ) ≠ -(n : ℚ))
    (hA : ∀ n : ℕ, ((A + 1) / 2 : ℚ) ≠ -(n : ℚ))
    (hB : ∀ n : ℕ, ((B + 1) / 2 : ℚ) ≠ -(n : ℚ)) :
    PConstructible (hyp (A : ℝ) (B : ℝ) (((A + B + 1) / 2 : ℚ) : ℝ) (1 / 2)) := by
  have hABr : ∀ n : ℕ, ((A : ℝ) + (B : ℝ) + 1) / 2 ≠ -(n : ℝ) := by
    intro n hcon
    exact hAB n (by exact_mod_cast hcon)
  have hAr : ∀ n : ℕ, ((A : ℝ) + 1) / 2 ≠ -(n : ℝ) := by
    intro n hcon
    exact hA n (by exact_mod_cast hcon)
  have hBr : ∀ n : ℕ, ((B : ℝ) + 1) / 2 ≠ -(n : ℝ) := by
    intro n hcon
    exact hB n (by exact_mod_cast hcon)
  rw [show (((A + B + 1) / 2 : ℚ) : ℝ) = ((A : ℝ) + (B : ℝ) + 1) / 2 by push_cast; ring]
  rw [hyp_second hABr hAr hBr]
  rw [show ((A : ℝ) + (B : ℝ) + 1) / 2 = (((A + B + 1) / 2 : ℚ) : ℝ) by push_cast; ring,
    show ((A : ℝ) + 1) / 2 = (((A + 1) / 2 : ℚ) : ℝ) by push_cast; ring,
    show ((B : ℝ) + 1) / 2 = (((B + 1) / 2 : ℚ) : ℝ) by push_cast; ring]
  exact PConstructible.div
    (PConstructible.mul sqrt_pi_Pconstructible (Gamma_rat_Pconstructible ((A + B + 1) / 2)))
    (PConstructible.mul (Gamma_rat_Pconstructible ((A + 1) / 2))
      (Gamma_rat_Pconstructible ((B + 1) / 2)))

end

end Pconstructible
