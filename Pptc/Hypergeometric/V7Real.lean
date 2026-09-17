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
-- `V7Eval`/`V7MobiusEval` supply the evaluations of the two series on the small disc,
-- `Mathlib.Analysis.Normed.Ring.InfiniteSum` the Cauchy product of two `HasSum`s, and the
-- analytic files the uniqueness principle used to continue the identity.
import Pptc.Hypergeometric.V7Eval
import Pptc.Hypergeometric.V7MobiusEval
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness

open scoped PowerSeries ENNReal Topology

namespace Pconstructible

noncomputable section

/-! # Pptc.Hypergeometric.V7Real

The real form of Goursat's quartic transformation (V7),

`₂F₁(1/4, 3/4; 1; z) = (1 + √z)^(-1/2) · ₂F₁(1/2, 1/2; 1; 2√z/(1 + √z))`
for `0 ≤ z < 1`.

`Pptc.Hypergeometric.V7` proves the formal identity `phiSeries = rSeries` in `ℝ⟦X⟧`. This
file transfers that coefficient identity to the real variable `w = √z`:

* `hasSum_rSeries` evaluates the right-hand side `rSeries` as the real function
  `(1+w)^(-1/2) · ₂F₁(1/2,1/2;1;2w/(1+w))` on `|w| < 1/3`. The two factor evaluations are
  `HasSum`s of absolutely summable sequences, so their Cauchy product converges
  (`hasSum_sum_range_mul_of_summable_norm`) and `PowerSeries.coeff_mul` identifies the
  convolution coefficients with those of `rSeries`.
* `goursat_small` is the identity on `|w| < 1/3`: `HasSum.unique` compares the evaluation of
  `phiSeries` with that of `rSeries`, and `phiSeries_eq_rSeries` makes the two families equal.
* `goursat_unit` extends it to `0 ≤ w < 1`. Both sides are analytic on `(0, 1)` — `hyp` is the
  sum of its power series on the unit disc, the prefactor `(1+w)^(-1/2)` is analytic there
  through its binomial series, and the Möbius map `w ↦ 2w/(1+w)` sends `(0,1)` into the unit
  disc — so `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` propagates the identity from
  the neighbourhood of `1/6` where `goursat_small` applies.
* `hyp_quarter_three_quarter` is V7 itself, obtained by substituting `w = √z` (with the
  degenerate case `z = 0` handled separately).
-/

/-- The Cauchy product of the two series on the disc `|w| < 1/3`: the coefficients of
`rSeries = sqrtInvSeries * mSeries` are the convolution of `sqrtInvCoeff` with the
coefficients of `mSeries`. -/
-- Theorem: for `|w| < 1/3`, the `rSeries` coefficients sum to
-- `(1+w)^(-1/2) · hyp (1/2)(1/2)1 (2w/(1+w))`.
theorem hasSum_rSeries {w : ℝ} (hw : |w| < 1 / 3) :
    HasSum (fun k : ℕ => PowerSeries.coeff k rSeries * w ^ k)
      ((1 + w) ^ (-(1 / 2 : ℝ)) * hyp (1 / 2) (1 / 2) 1 (2 * w / (1 + w))) := by
  have hw1 : |w| < 1 := by linarith [abs_nonneg w, hw]
  have hInv := hasSum_sqrtInvSeries (w := w) hw1
  have hM := hasSum_mSeries hw
  have hmain := hasSum_sum_range_mul_of_summable_norm
    (f := fun i : ℕ => sqrtInvCoeff i * w ^ i)
    (g := fun j : ℕ => PowerSeries.coeff j mSeries * w ^ j)
    hInv.summable.norm hM.summable.norm
  rw [hInv.tsum_eq, hM.tsum_eq] at hmain
  refine hmain.congr_fun fun n => ?_
  have hcoeff : ∀ k : ℕ, PowerSeries.coeff k sqrtInvSeries = sqrtInvCoeff k := by
    intro k
    rw [sqrtInvSeries, PowerSeries.coeff_mk]
  have hconv : PowerSeries.coeff n rSeries
      = ∑ k ∈ Finset.range (n + 1),
          sqrtInvCoeff k * PowerSeries.coeff (n - k) mSeries := by
    rw [rSeries, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i sqrtInvSeries
          * PowerSeries.coeff j mSeries),
      Nat.succ_eq_add_one]
    exact Finset.sum_congr rfl fun k _ => by rw [hcoeff k]
  rw [hconv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hk' : k ≤ n := Nat.le_of_lt_succ hk
  symm
  calc (sqrtInvCoeff k * w ^ k) * (PowerSeries.coeff (n - k) mSeries * w ^ (n - k))
      = (sqrtInvCoeff k * PowerSeries.coeff (n - k) mSeries)
          * (w ^ k * w ^ (n - k)) := by ring
    _ = (sqrtInvCoeff k * PowerSeries.coeff (n - k) mSeries) * w ^ n := by
        rw [← pow_add, Nat.add_sub_cancel' hk']

/-- Goursat's V7 in the variable `w = √z` on the small disc `|w| < 1/3`: uniqueness of the
sum of a convergent series, together with the formal identity `phiSeries = rSeries`. -/
-- Theorem: for `|w| < 1/3`, `hyp (1/4)(3/4)1 (w²) = (1+w)^(-1/2) · hyp (1/2)(1/2)1 (2w/(1+w))`.
theorem goursat_small {w : ℝ} (hw : |w| < 1 / 3) :
    hyp (1 / 4) (3 / 4) 1 (w ^ 2) =
      (1 + w) ^ (-(1 / 2 : ℝ)) * hyp (1 / 2) (1 / 2) 1 (2 * w / (1 + w)) := by
  have hw1 : |w| < 1 := by linarith [abs_nonneg w, hw]
  have h1 : HasSum (fun k : ℕ => PowerSeries.coeff k rSeries * w ^ k)
      (hyp (1 / 4) (3 / 4) 1 (w ^ 2)) :=
    (hasSum_phiSeries hw1).congr_fun fun k => by rw [phiSeries_eq_rSeries]
  exact h1.unique (hasSum_rSeries hw)

/-- V7 on `0 ≤ w < 1`, by analytic continuation. The logarithmic singularity at `w = 0` is
harmless: both sides equal `1` there, and on `(0, 1)` the two sides are analytic and agree near
`1/6` by `goursat_small`. -/
-- Theorem: for `0 ≤ w < 1`,
-- `hyp (1/4)(3/4)1 (w²) = (1+w)^(-1/2) · hyp (1/2)(1/2)1 (2w/(1+w))`.
theorem goursat_unit {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    hyp (1 / 4) (3 / 4) 1 (w ^ 2) =
      (1 + w) ^ (-(1 / 2 : ℝ)) * hyp (1 / 2) (1 / 2) 1 (2 * w / (1 + w)) := by
  rcases hw0.eq_or_lt with h | h
  · subst h
    simp [hyp, ordinaryHypergeometric_zero]
  · have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
      intro n hn
      have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hball : ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∈ Metric.eball (0 : ℝ) 1 := by
      intro x hx
      rw [Set.mem_Ioo] at hx
      obtain ⟨hx0, hx1⟩ := hx
      have hxabs : |x| < 1 := by rw [abs_of_nonneg (le_of_lt hx0)]; exact hx1
      rw [mem_eball_zero_iff, enorm_eq_nnnorm]
      simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
      exact hxabs
    have hF : AnalyticOnNhd ℝ (fun x : ℝ => hyp (1 / 4) (3 / 4) 1 (x ^ 2))
        (Set.Ioo (0 : ℝ) 1) := by
      let S : FormalMultilinearSeries ℝ ℝ ℝ :=
        ordinaryHypergeometricSeries ℝ (1 / 4) (3 / 4) 1
      have hrad : (1 : ℝ≥0∞) ≤ S.radius :=
        one_le_hypergeometric_radius (a := (1 : ℝ) / 4) (b := (3 : ℝ) / 4) (c := 1) hc
      have hpos : 0 < S.radius := lt_of_lt_of_le (by norm_num) hrad
      have houter : AnalyticOnNhd ℝ (fun x : ℝ => hyp (1 / 4) (3 / 4) 1 x)
          (Metric.eball 0 1) :=
        ((S.hasFPowerSeriesOnBall hpos).analyticOnNhd).mono (Metric.eball_subset_eball hrad)
      have hinner : AnalyticOnNhd ℝ (fun x : ℝ => x ^ 2) (Set.Ioo (0 : ℝ) 1) :=
        analyticOnNhd_id.pow 2
      have hmaps : Set.MapsTo (fun x : ℝ => x ^ 2)
          (Set.Ioo (0 : ℝ) 1) (Metric.eball 0 1) := by
        intro x hx
        rw [Set.mem_Ioo] at hx
        obtain ⟨hx0, hx1⟩ := hx
        have hxabs : |x ^ 2| < 1 := by
          have hx2 : x ^ 2 < 1 := by
            have h : x * x < x := by simpa using mul_lt_mul_of_pos_left hx1 hx0
            calc x ^ 2 = x * x := pow_two x
              _ < x := h
              _ < 1 := hx1
          rwa [abs_of_nonneg (sq_nonneg x)]
        have hnorm : (‖x ^ 2‖ₑ : ℝ≥0∞) < 1 := by
          rw [enorm_eq_nnnorm]
          simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
          exact hxabs
        rwa [mem_eball_zero_iff]
      exact houter.comp hinner hmaps
    have hG : AnalyticOnNhd ℝ
        (fun x : ℝ => (1 + x) ^ (-(1 / 2 : ℝ)) * hyp (1 / 2) (1 / 2) 1 (2 * x / (1 + x)))
        (Set.Ioo (0 : ℝ) 1) := by
      have hA : AnalyticOnNhd ℝ (fun x : ℝ => (1 + x) ^ (-(1 / 2 : ℝ)))
          (Set.Ioo (0 : ℝ) 1) :=
        ((Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -(1 / 2 : ℝ))).analyticOnNhd).mono
          fun x hx => hball x hx
      have hB : AnalyticOnNhd ℝ (fun x : ℝ => hyp (1 / 2) (1 / 2) 1 (2 * x / (1 + x)))
          (Set.Ioo (0 : ℝ) 1) := by
        let S2 : FormalMultilinearSeries ℝ ℝ ℝ :=
          ordinaryHypergeometricSeries ℝ (1 / 2) (1 / 2) 1
        have hrad : (1 : ℝ≥0∞) ≤ S2.radius :=
          one_le_hypergeometric_radius (a := (1 : ℝ) / 2) (b := (1 : ℝ) / 2) (c := 1) hc
        have hpos : 0 < S2.radius := lt_of_lt_of_le (by norm_num) hrad
        have houter : AnalyticOnNhd ℝ (fun x : ℝ => hyp (1 / 2) (1 / 2) 1 x)
            (Metric.eball 0 1) :=
          ((S2.hasFPowerSeriesOnBall hpos).analyticOnNhd).mono (Metric.eball_subset_eball hrad)
        have hinner : AnalyticOnNhd ℝ (fun x : ℝ => 2 * x / (1 + x))
            (Set.Ioo (0 : ℝ) 1) := by
          refine AnalyticOnNhd.div
            ((analyticOnNhd_const (v := (2 : ℝ))).mul analyticOnNhd_id)
            ((analyticOnNhd_const (v := (1 : ℝ))).add analyticOnNhd_id) ?_
          intro x hx
          rw [Set.mem_Ioo] at hx
          exact ne_of_gt (by linarith [hx.1])
        have hmaps : Set.MapsTo (fun x : ℝ => 2 * x / (1 + x))
            (Set.Ioo (0 : ℝ) 1) (Metric.eball 0 1) := by
          intro x hx
          rw [Set.mem_Ioo] at hx
          obtain ⟨hx0, hx1⟩ := hx
          have hx1pos : 0 < 1 + x := by linarith
          have h2x : 0 ≤ 2 * x := by linarith
          have hxabs : |2 * x / (1 + x)| < 1 := by
            rw [abs_of_nonneg (div_nonneg h2x (le_of_lt hx1pos)), div_lt_one hx1pos]
            linarith
          have hnorm : (‖2 * x / (1 + x)‖ₑ : ℝ≥0∞) < 1 := by
            rw [enorm_eq_nnnorm]
            simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
            exact hxabs
          rwa [mem_eball_zero_iff]
        exact houter.comp hinner hmaps
      exact hA.mul hB
    have hev : (fun x : ℝ => hyp (1 / 4) (3 / 4) 1 (x ^ 2)) =ᶠ[𝓝 (1 / 6 : ℝ)]
        fun x : ℝ => (1 + x) ^ (-(1 / 2 : ℝ)) * hyp (1 / 2) (1 / 2) 1 (2 * x / (1 + x)) := by
      refine Filter.eventually_of_mem
        (Metric.ball_mem_nhds (1 / 6 : ℝ) (by norm_num : (0 : ℝ) < 1 / 6)) fun x hx => ?_
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hx
      refine goursat_small ?_
      have hxa := abs_lt.mp hx
      rw [abs_lt]
      constructor <;> linarith [hxa.1, hxa.2]
    have h0 : (1 / 6 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [Set.mem_Ioo]
      exact ⟨by norm_num, by norm_num⟩
    have hwmem : w ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [Set.mem_Ioo]
      exact ⟨h, hw1⟩
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hG isPreconnected_Ioo h0 hev
      hwmem

/-- **V7**: Goursat's quartic transformation, `₂F₁(1/4,3/4;1;z)` in terms of
`₂F₁(1/2,1/2;1;·)` at the Möbius image of `√z`, for `0 ≤ z < 1`. -/
-- Theorem (V7): for `0 ≤ z < 1`,
-- `hyp (1/4)(3/4)1 z = (1+√z)^(-1/2) · hyp (1/2)(1/2)1 (2√z/(1+√z))`.
theorem hyp_quarter_three_quarter {z : ℝ} (hz0 : 0 ≤ z) (hz : z < 1) :
    hyp (1 / 4) (3 / 4) 1 z =
      (1 + Real.sqrt z) ^ (-(1 / 2 : ℝ))
        * hyp (1 / 2) (1 / 2) 1 (2 * Real.sqrt z / (1 + Real.sqrt z)) := by
  rcases hz0.eq_or_lt with h | h
  · subst h
    simp [hyp, ordinaryHypergeometric_zero]
  · have hw0 : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z
    have hw1 : Real.sqrt z < 1 :=
      (Real.sqrt_lt hz0 (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hz)
    have hsq : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz0
    have hmain := goursat_unit (w := Real.sqrt z) hw0 hw1
    rwa [hsq] at hmain

end

end Pconstructible
