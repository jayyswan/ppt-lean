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
-- `V7` supplies the formal identity `phiSeries = rSeries` together with the two series
-- themselves; `Mathlib.Analysis.Analytic.Binomial` supplies the real binomial series whose
-- `(1+X)^(-1/2)` case is the analytic value of `sqrtInvSeries`.
import Pptc.Hypergeometric.V7
import Mathlib.Analysis.Analytic.Binomial

open scoped PowerSeries ENNReal

namespace Pconstructible

noncomputable section

/-! # Pptc.Hypergeometric.V7Eval

Analytic evaluation of the two formal power series occurring in V7.

The formal identity `phiSeries = rSeries` (in `Pptc.Hypergeometric.V7`) lives entirely in the
ring `ℝ⟦X⟧`. This file connects the two formal series to the real functions from which they
were built, which is what the geometric application of V7 needs:

* `hasSum_phiSeries` evaluates the squaring-substituted hypergeometric series
  `phiSeries = ₂F₁(1/4,3/4;1;X²)` as the real hypergeometric function `hyp (1/4)(3/4)1 (w²)`
  on the open unit disc. The squaring substitution keeps only the even coefficients, so the
  series over all of `ℕ` is the positive-even reindexing of the hypergeometric series; the
  odd coefficients vanish, which is exactly what `Function.Injective.hasSum_iff` needs.
* `hasSum_sqrtInvSeries` evaluates `sqrtInvSeries = (1+X)^(-1/2)` as the real power
  `(1+w)^(-1/2)`, via Mathlib's binomial series and the coefficient identity
  `Ring.choose (-(1/2)) n = sqrtInvCoeff n`.
-/

/-! ### The coefficient identity for `(1 + X)^(-1/2)` -/

/-- The generalized binomial coefficient `(-1/2 choose n)` is the coefficient `sqrtInvCoeff n`
of `(1 + X)^(-1/2)`.

Both families satisfy the same first-order recurrence with the same initial value: the
binomial coefficients satisfy `(n+1) · (-1/2 choose n+1) = (-1/2 - n) · (-1/2 choose n)` (the
`k = n` case of `Ring.choose_smul_choose`), while `sqrtInvCoeff_succ` is precisely
`h_{n+1} = -((n + 1/2)/(n + 1)) h_n`. -/
-- Theorem: `Ring.choose (-(1/2)) n = sqrtInvCoeff n`.
theorem ring_choose_neg_half (n : ℕ) :
    Ring.choose (-(1 / 2 : ℝ)) n = sqrtInvCoeff n := by
  induction n with
  | zero =>
    rw [Ring.choose_zero_right, sqrtInvCoeff_zero]
  | succ n ih =>
    have hrec : ((n : ℝ) + 1) * Ring.choose (-(1 / 2 : ℝ)) (n + 1)
        = Ring.choose (-(1 / 2 : ℝ)) n * (-(1 / 2 : ℝ) - n) := by
      have h := Ring.choose_smul_choose (-(1 / 2 : ℝ)) (n := n + 1) (k := n) (Nat.le_succ n)
      rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right] at h
      rw [nsmul_eq_mul, Nat.cast_succ] at h
      exact h
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hdiv : Ring.choose (-(1 / 2 : ℝ)) (n + 1)
        = Ring.choose (-(1 / 2 : ℝ)) n * (-(1 / 2 : ℝ) - n) / ((n : ℝ) + 1) := by
      rw [eq_div_iff hn1]
      simpa [mul_comm] using hrec
    rw [hdiv, ih, sqrtInvCoeff_succ]
    ring

/-- Evaluation of `sqrtInvSeries` on the open unit disc: it is the real function
`w ↦ (1 + w)^(-1/2)`.

Mathlib's binomial series gives `HasFPowerSeriesOnBall (fun x => (1 + x) ^ a)
(binomialSeries ℝ a) 0 1`; evaluating the `n`-th term at `w` produces `(-1/2 choose n) wⁿ`,
and `ring_choose_neg_half` identifies the coefficients with `sqrtInvCoeff`. -/
-- Theorem: for `|w| < 1`, `∑ₙ sqrtInvCoeff n * wⁿ = (1 + w)^(-1/2)`.
theorem hasSum_sqrtInvSeries {w : ℝ} (hw : |w| < 1) :
    HasSum (fun n : ℕ => sqrtInvCoeff n * w ^ n) ((1 + w) ^ (-(1 / 2 : ℝ))) := by
  have hball : w ∈ Metric.eball (0 : ℝ) 1 := by
    rw [mem_eball_zero_iff]
    have hlt : (‖w‖ₑ : ℝ≥0∞) < 1 := by
      rw [enorm_eq_nnnorm]
      simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
      exact hw
    exact hlt
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -(1 / 2 : ℝ))).hasSum hball
  have hterm : ∀ n : ℕ, binomialSeries ℝ (-(1 / 2 : ℝ)) n (fun _ : Fin n => w)
      = Ring.choose (-(1 / 2 : ℝ)) n * w ^ n := by
    intro n
    rw [binomialSeries_apply]
    simp [smul_eq_mul]
  have h' : HasSum (fun n : ℕ => Ring.choose (-(1 / 2 : ℝ)) n * w ^ n)
      ((1 + w) ^ (-(1 / 2 : ℝ))) := by
    have hc := h.congr_fun (fun n => (hterm n).symm)
    simpa using hc
  have h'' : HasSum (fun n : ℕ => sqrtInvCoeff n * w ^ n) ((1 + w) ^ (-(1 / 2 : ℝ))) :=
    h'.congr_fun (fun n => by rw [← ring_choose_neg_half n])
  exact h''

/-! ### Evaluation of the squaring-substituted hypergeometric series -/

/-- Coefficient extraction for `phiSeries`: the substitution `w = X²` retains only the even
coefficients, `[Xᵏ] phiSeries` being the `k/2`-th hypergeometric coefficient when `k` is even
and `0` otherwise.

This is the `k = 2` case of `PowerSeries.coeff_subst_X_pow`. -/
-- Theorem: `[Xᵏ] phiSeries = if 2 ∣ k then hypCoeff (1/4)(3/4)1 (k/2) else 0`.
theorem coeff_phiSeries (k : ℕ) :
    PowerSeries.coeff k phiSeries
      = if 2 ∣ k then hypCoeff (1 / 4) (3 / 4) 1 (k / 2) else 0 := by
  rw [phiSeries, PowerSeries.coeff_subst_X_pow (by norm_num : (2 : ℕ) ≠ 0)]
  by_cases h : 2 ∣ k
  · rw [if_pos h, if_pos h, coeff_hypSeries]
    simp
  · rw [if_neg h, if_neg h]

/-- Evaluation of `phiSeries` on the open unit disc: the squaring substitution really is the
`w = √z` pullback, `phiSeries(w) = ₂F₁(1/4,3/4;1;w²)`.

The hypergeometric series `∑ₙ hypCoeff (1/4)(3/4)1 n * (w²)ⁿ` converges for `|w²| < 1` by
`hasSum_hyp`, and it is the same sum as `∑ₖ [Xᵏ]phiSeries * wᵏ`: the two agree on the even
indices `k = 2n` by `coeff_phiSeries`; the odd coefficients all vanish, so the injective
reindexing `n ↦ 2n` loses nothing (`Function.Injective.hasSum_iff`). -/
-- Theorem: for `|w| < 1`, `∑ₖ [Xᵏ]phiSeries * wᵏ = hyp (1/4)(3/4)1 (w²)`.
theorem hasSum_phiSeries {w : ℝ} (hw : |w| < 1) :
    HasSum (fun k : ℕ => PowerSeries.coeff k phiSeries * w ^ k)
      (hyp (1 / 4) (3 / 4) 1 (w ^ 2)) := by
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n hn
    have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw2 : |w ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg w, hw]
  have hhyp := hasSum_hyp (a := 1 / 4) (b := 3 / 4) (c := 1) (z := w ^ 2) hw2 hc
  have hcomp : HasSum ((fun k : ℕ => PowerSeries.coeff k phiSeries * w ^ k) ∘
      fun n : ℕ => 2 * n) (hyp (1 / 4) (3 / 4) 1 (w ^ 2)) :=
    hhyp.congr_fun (by
      intro n
      have h2 : (2 * n) / 2 = n := Nat.mul_div_cancel_left n (by norm_num)
      rw [Function.comp_apply, coeff_phiSeries, if_pos (dvd_mul_right 2 n), h2, pow_mul])
  have hg : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b hab
    exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hab
  have hzero : ∀ x ∉ Set.range (fun n : ℕ => 2 * n),
      PowerSeries.coeff x phiSeries * w ^ x = 0 := by
    intro x hx
    have hx2 : ¬ (2 ∣ x) := by
      rintro ⟨m, hm⟩
      exact hx ⟨m, hm.symm⟩
    rw [coeff_phiSeries, if_neg hx2, zero_mul]
  exact (Function.Injective.hasSum_iff hg hzero).mp hcomp

end

end Pconstructible
