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
import Pptc.Basic
import Pptc.Hypergeometric.Basic
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Pptc.Hypergeometric.Elliptic

The complete elliptic integrals `K = ellipticF c (π/2)` and `E = ellipticE c (π/2)` as
Gauss hypergeometric functions (H2 of the hypergeometric plan):

  `ellipticF c (π/2) = (π/2) ₂F₁(1/2, 1/2; 1; c)`,  `ellipticE c (π/2) = (π/2) ₂F₁(-1/2, 1/2; 1; c)`

for `|c| < 1`. The two PConstructible corollaries are the point of the file: they turn the
existing `ellipticF_pi_div_two_Pconstructible` / `ellipticE_Pconstructible` into closure
results for the ₂F₁ family `(±1/2, 1/2; 1; ·)` that the rest of the hypergeometric programme
(L3b, L6b, L6c, L9) consumes.

## Why the proof is a power series in the integrand

Both integrals are `∫₀^{π/2} (1 - c sin²θ)^a dθ` for `a = -1/2` (F) and `a = 1/2` (E), and
`(1 - u)^a` has the binomial power series `∑ₙ Ring.choose (a+n-1) n uⁿ` on `|u| < 1`
(`Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`). For fixed `c` with `|c| < 1`, the
geometric factor `u = c sin²θ` lies in the disc for *every* `θ`, and the coefficients are
dominated by `C(2n,n)/4ⁿ · Rⁿ` for some `|c| < R < 1`, which is summable. So
`intervalIntegral.hasSum_integral_of_dominated_convergence` swaps the sum and the integral.
Each term integrates by the Wallis formula, and the resulting coefficients are exactly the
hypergeometric coefficients of `(±1/2, 1/2; 1; c)` — the coefficient identity that makes the
bridge work. -/

open scoped Topology ENNReal

namespace Pconstructible

noncomputable section

/-! ### Coefficients and the Wallis half-integral

The two coefficient facts behind the bridge. `(1/2)ₙ/n! = C(2n,n)/4ⁿ` is
`ascPochhammer_one_div_two` already in `Pptc.Hypergeometric.Basic`; here we record what it
gives for the hypergeometric coefficients of `(1/2,1/2;1;·)` and `(-1/2,1/2;1;·)`, and the
integral `∫₀^{π/2} sin^{2n} = (π/2) (1/2)ₙ/n!`, which is the `π/2`-restriction of
`integral_sin_pow_even`. -/

-- Theorem: `(1/2)ₙ > 0`.
private lemma ascPochhammer_one_div_two_pos (n : ℕ) :
    0 < (ascPochhammer ℝ n).eval (1 / 2) := by
  induction n with
  | zero => norm_num [ascPochhammer]
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    exact mul_pos ih (by positivity)

-- Theorem: `|(-1/2)ₙ| ≤ (1/2)ₙ`, factorwise since `|j - 1/2| ≤ j + 1/2`.
private lemma abs_ascPochhammer_neg_half_le (n : ℕ) :
    |(ascPochhammer ℝ n).eval (-1 / 2)| ≤ (ascPochhammer ℝ n).eval (1 / 2) := by
  induction n with
  | zero => norm_num [ascPochhammer]
  | succ n ih =>
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [ascPochhammer_succ_eval n (-1 / 2 : ℝ), ascPochhammer_succ_eval n (1 / 2 : ℝ),
      abs_mul]
    refine mul_le_mul ih ?_ (abs_nonneg _) (ascPochhammer_one_div_two_pos n).le
    rw [abs_le]
    constructor <;> linarith

-- Theorem: `Ring.choose (1/2 + n - 1) n = C(2n,n)/4ⁿ`.
private lemma ring_choose_half_eq (n : ℕ) :
    Ring.choose ((1 / 2 : ℝ) + n - 1) n = (Nat.choose (2 * n) n : ℝ) / 4 ^ n := by
  rw [ring_choose_eq_ascPochhammer, ascPochhammer_one_div_two]
  have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

-- Theorem: `|Ring.choose (-1/2 + n - 1) n| ≤ C(2n,n)/4ⁿ`, the domination behind the E case.
private lemma abs_ring_choose_neg_half_le (n : ℕ) :
    |Ring.choose ((-1 / 2 : ℝ) + n - 1) n| ≤ (Nat.choose (2 * n) n : ℝ) / 4 ^ n := by
  rw [ring_choose_eq_ascPochhammer, abs_mul]
  have hnf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [abs_of_pos (inv_pos.mpr hnf)]
  calc |(ascPochhammer ℝ n).eval (-1 / 2)| * (n.factorial : ℝ)⁻¹
      ≤ (ascPochhammer ℝ n).eval (1 / 2) * (n.factorial : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right (abs_ascPochhammer_neg_half_le n) (inv_pos.mpr hnf).le
    _ = (Nat.choose (2 * n) n : ℝ) / 4 ^ n := by
        rw [ascPochhammer_one_div_two]
        have hnf0 : (n.factorial : ℝ) ≠ 0 := hnf.ne'
        have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
        field_simp

-- Theorem: `∑ₙ hypCoeff (1/2)(1/2)1 n zⁿ` has `n`-th coefficient `((1/2)ₙ/n!)²`.
private lemma hypCoeff_half_half_one (n : ℕ) :
    hypCoeff (1 / 2) (1 / 2) 1 n =
      ((ascPochhammer ℝ n).eval (1 / 2) / (n.factorial : ℝ)) ^ 2 := by
  unfold hypCoeff ordinaryHypergeometricCoefficient
  rw [ascPochhammer_eval_one]
  have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

-- Theorem: `hypCoeff (-1/2)(1/2)1 n = ((-1/2)ₙ/n!) ((1/2)ₙ/n!)`.
private lemma hypCoeff_neg_half_half_one (n : ℕ) :
    hypCoeff (-1 / 2) (1 / 2) 1 n =
      ((ascPochhammer ℝ n).eval (-1 / 2) / (n.factorial : ℝ)) *
        ((ascPochhammer ℝ n).eval (1 / 2) / (n.factorial : ℝ)) := by
  unfold hypCoeff ordinaryHypergeometricCoefficient
  rw [ascPochhammer_eval_one]
  have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

-- Theorem: the Wallis product is `(1/2)ₙ/n!`.
private lemma prod_range_eq_ascPochhammer (n : ℕ) :
    ∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * (i : ℝ) + 2) =
      (ascPochhammer ℝ n).eval (1 / 2) / (n.factorial : ℝ) := by
  induction n with
  | zero => simp [ascPochhammer]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
    have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
    ring

-- Theorem: `∫₀^{π/2} sin^{2n} = (π/2) (1/2)ₙ/n!` (half of `integral_sin_pow_even` by symmetry).
private lemma integral_sin_pow_even_half (n : ℕ) :
    (∫ x in (0 : ℝ)..(Real.pi / 2), Real.sin x ^ (2 * n)) =
      (Real.pi / 2) * (ascPochhammer ℝ n).eval (1 / 2) / (n.factorial : ℝ) := by
  have hsym : (∫ x in (Real.pi / 2)..Real.pi, Real.sin x ^ (2 * n)) =
      ∫ x in (0 : ℝ)..(Real.pi / 2), Real.sin x ^ (2 * n) := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := fun x : ℝ => Real.sin x ^ (2 * n)) (a := (0 : ℝ))
      (b := Real.pi / 2) Real.pi
    simp only [sub_zero] at h
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at h
    have hcongr : (∫ x in (0 : ℝ)..(Real.pi / 2), Real.sin (Real.pi - x) ^ (2 * n)) =
        ∫ x in (0 : ℝ)..(Real.pi / 2), Real.sin x ^ (2 * n) :=
      intervalIntegral.integral_congr fun x _ => by rw [Real.sin_pi_sub]
    rw [hcongr] at h
    exact h.symm
  have hadd := intervalIntegral.integral_add_adjacent_intervals
      (f := fun x : ℝ => Real.sin x ^ (2 * n)) (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := Real.pi / 2) (c := Real.pi)
      ((Real.continuous_sin.pow _).intervalIntegrable _ _)
      ((Real.continuous_sin.pow _).intervalIntegrable _ _)
  rw [integral_sin_pow_even n, hsym, prod_range_eq_ascPochhammer n] at hadd
  have h2 : (∫ x in (0 : ℝ)..(Real.pi / 2), Real.sin x ^ (2 * n)) =
      Real.pi * ((ascPochhammer ℝ n).eval (1 / 2) / (n.factorial : ℝ)) / 2 := by
    linarith
  rw [h2]
  ring

/-! ### Swapping the binomial series with the integral

The single analytic ingredient, used twice (F with `a = 1/2`, E with `a = -1/2`). The
dominating series is the binomial series evaluated at some `|c| < R < 1`, which converges
absolutely; the termwise integral is a constant times the Wallis integral above. -/

-- Theorem: `∫₀^{π/2} (1 - c sin²θ)^(-a) dθ = ∑ₙ Ring.choose (a+n-1) n cⁿ ∫₀^{π/2} sin^{2n}`.
private lemma integral_rpow_hasSum {c a : ℝ} (hc : |c| < 1)
    (hcoef : ∀ n : ℕ, |Ring.choose (a + n - 1) n| ≤ (Nat.choose (2 * n) n : ℝ) / 4 ^ n) :
    HasSum (fun n : ℕ => Ring.choose (a + n - 1) n * c ^ n *
        (∫ x in (0 : ℝ)..(Real.pi / 2), Real.sin x ^ (2 * n)))
      (∫ x in (0 : ℝ)..(Real.pi / 2), 1 / (1 - c * Real.sin x ^ 2) ^ a) := by
  obtain ⟨R, hcR, hR1⟩ := exists_between hc
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg c) hcR
  have hRabs : |R| < 1 := by rw [abs_of_pos hRpos]; exact hR1
  have hbound_summ : Summable fun n : ℕ => (Nat.choose (2 * n) n : ℝ) / 4 ^ n * R ^ n := by
    have hmem : R ∈ Metric.eball (0 : ℝ) (1 : ℝ≥0∞) := by
      rw [mem_eball_zero_iff, enorm_eq_nnnorm]
      simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
      exact hRabs
    have hbase := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2)).hasSum hmem
    rw [zero_add] at hbase
    refine hbase.summable.congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, ring_choose_half_eq]
  have hmain : HasSum (fun n : ℕ => ∫ x in (0 : ℝ)..(Real.pi / 2),
        Ring.choose (a + n - 1) n * (c * Real.sin x ^ 2) ^ n)
      (∫ x in (0 : ℝ)..(Real.pi / 2), 1 / (1 - c * Real.sin x ^ 2) ^ a) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun n (_ : ℝ) => (Nat.choose (2 * n) n : ℝ) / 4 ^ n * R ^ n)
    · intro n
      exact (continuous_const.mul
        ((continuous_const.mul (Real.continuous_sin.pow 2)).pow n)).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall (fun t _ => ?_)
      have hsin : |Real.sin t ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact Real.sin_sq_le_one t
      have hu : |c * Real.sin t ^ 2| ≤ R := by
        rw [abs_mul]
        calc |c| * |Real.sin t ^ 2| ≤ |c| * 1 :=
              mul_le_mul_of_nonneg_left hsin (abs_nonneg c)
          _ = |c| := mul_one _
          _ ≤ R := hcR.le
      have hb : 0 ≤ (Nat.choose (2 * n) n : ℝ) / 4 ^ n := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul (hcoef n) (pow_le_pow_left₀ (abs_nonneg _) hu n)
        (pow_nonneg (abs_nonneg _) n) hb
    · refine Filter.Eventually.of_forall (fun _ _ => hbound_summ)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun t _ => ?_)
      have hu : |c * Real.sin t ^ 2| < 1 := by
        rw [abs_mul]
        have hsin : |Real.sin t ^ 2| ≤ 1 := by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact Real.sin_sq_le_one t
        calc |c| * |Real.sin t ^ 2| ≤ |c| * 1 :=
              mul_le_mul_of_nonneg_left hsin (abs_nonneg c)
          _ = |c| := mul_one _
          _ < 1 := hc
      have hmem : c * Real.sin t ^ 2 ∈ Metric.eball (0 : ℝ) (1 : ℝ≥0∞) := by
        rw [mem_eball_zero_iff, enorm_eq_nnnorm]
        simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
        exact hu
      have hbase := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum hmem
      rw [zero_add] at hbase
      simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hbase
  refine hmain.congr_fun fun n => ?_
  have hcongr : (∫ x in (0 : ℝ)..(Real.pi / 2),
        Ring.choose (a + n - 1) n * (c * Real.sin x ^ 2) ^ n) =
      ∫ x in (0 : ℝ)..(Real.pi / 2),
        Ring.choose (a + n - 1) n * c ^ n * Real.sin x ^ (2 * n) :=
    intervalIntegral.integral_congr fun x _ => by rw [mul_pow, ← pow_mul]; ring
  rw [hcongr, intervalIntegral.integral_const_mul]

/-! ### The integrands as powers of `1 - c sin²θ` -/

-- Theorem: the first-kind integrand is `(1 - c sin²θ)^(-1/2)`.
private lemma ellipticFIntegrand_eq_rpow (c θ : ℝ) (hc : c < 1) :
    ellipticFIntegrand c θ = (1 - c * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) := by
  rw [ellipticFIntegrand, ellipticEIntegrand, Real.sqrt_eq_rpow,
    ← Real.rpow_neg (one_sub_mul_sin_sq_pos hc θ).le (1 / 2 : ℝ)]

-- Theorem: the second-kind integrand is `(1 - c sin²θ)^(1/2)`.
private lemma ellipticEIntegrand_eq_rpow (c θ : ℝ) :
    ellipticEIntegrand c θ = (1 - c * Real.sin θ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [ellipticEIntegrand, Real.sqrt_eq_rpow]

/-! ### The bridges -/

-- Theorem (H2, first kind): `ellipticF c (π/2) = (π/2) ₂F₁(1/2,1/2;1;c)` for `|c| < 1`.
-- The binomial series for `(1-u)^(-1/2)` has coefficients `(1/2)ₙ/n! = C(2n,n)/4ⁿ`, and the
-- Wallis integral contributes the same factor again, so each term is
-- `(π/2) ((1/2)ₙ/n!)² cⁿ = (π/2) hypCoeff (1/2)(1/2)1 n cⁿ`.
theorem ellipticF_pi_div_two_eq_hyp {c : ℝ} (hc : |c| < 1) :
    ellipticF c (Real.pi / 2) = Real.pi / 2 * hyp (1 / 2) (1 / 2) 1 c := by
  have hc1 : c < 1 := (abs_lt.mp hc).2
  have hint : ellipticF c (Real.pi / 2) =
      ∫ x in (0 : ℝ)..(Real.pi / 2), 1 / (1 - c * Real.sin x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [ellipticF]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [ellipticFIntegrand_eq_rpow c x hc1,
      Real.rpow_neg (one_sub_mul_sin_sq_pos hc1 x).le (1 / 2 : ℝ), inv_eq_one_div]
  rw [hint]
  have hcoef : ∀ n : ℕ,
      |Ring.choose ((1 / 2 : ℝ) + n - 1) n| ≤ (Nat.choose (2 * n) n : ℝ) / 4 ^ n := by
    intro n
    have hb : (0 : ℝ) ≤ (Nat.choose (2 * n) n : ℝ) / 4 ^ n := by positivity
    rw [ring_choose_half_eq n, abs_of_nonneg hb]
  have hmain := integral_rpow_hasSum (a := 1 / 2) hc hcoef
  have hterms : ∀ n : ℕ, (Real.pi / 2) * hypCoeff (1 / 2) (1 / 2) 1 n * c ^ n =
      Ring.choose ((1 / 2 : ℝ) + n - 1) n * c ^ n *
        (∫ x in (0 : ℝ)..(Real.pi / 2), Real.sin x ^ (2 * n)) := by
    intro n
    rw [ring_choose_eq_ascPochhammer, integral_sin_pow_even_half n,
      hypCoeff_half_half_one n]
    ring
  refine (hmain.congr_fun hterms).unique ?_
  have hne : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2 := (hasSum_hyp (a := 1 / 2) (b := 1 / 2) (c := 1) (z := c) hc hne).mul_left
    (Real.pi / 2)
  refine h2.congr_fun fun n => ?_
  ring

-- Theorem (H2, second kind): `ellipticE c (π/2) = (π/2) ₂F₁(-1/2,1/2;1;c)` for `|c| < 1`.
-- The binomial series for `(1-u)^(1/2)` has coefficients `(-1/2)ₙ/n!`, and the Wallis
-- integral contributes `(1/2)ₙ/n!`, so each term is `(π/2) hypCoeff (-1/2)(1/2)1 n cⁿ`.
theorem ellipticE_pi_div_two_eq_hyp {c : ℝ} (hc : |c| < 1) :
    ellipticE c (Real.pi / 2) = Real.pi / 2 * hyp (-1 / 2) (1 / 2) 1 c := by
  have hc1 : c < 1 := (abs_lt.mp hc).2
  have hint : ellipticE c (Real.pi / 2) =
      ∫ x in (0 : ℝ)..(Real.pi / 2), 1 / (1 - c * Real.sin x ^ 2) ^ (-1 / 2 : ℝ) := by
    rw [ellipticE]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [ellipticEIntegrand_eq_rpow c x]
    rw [show ((-1) / 2 : ℝ) = -(1 / 2) by ring]
    rw [Real.rpow_neg (one_sub_mul_sin_sq_pos hc1 x).le (1 / 2 : ℝ)]
    simp only [one_div, inv_inv]
  rw [hint]
  have hcoef : ∀ n : ℕ,
      |Ring.choose ((-1 / 2 : ℝ) + n - 1) n| ≤ (Nat.choose (2 * n) n : ℝ) / 4 ^ n :=
    abs_ring_choose_neg_half_le
  have hmain := integral_rpow_hasSum (a := -1 / 2) hc hcoef
  have hterms : ∀ n : ℕ, (Real.pi / 2) * hypCoeff (-1 / 2) (1 / 2) 1 n * c ^ n =
      Ring.choose ((-1 / 2 : ℝ) + n - 1) n * c ^ n *
        (∫ x in (0 : ℝ)..(Real.pi / 2), Real.sin x ^ (2 * n)) := by
    intro n
    rw [ring_choose_eq_ascPochhammer, integral_sin_pow_even_half n,
      hypCoeff_neg_half_half_one n]
    ring
  refine (hmain.congr_fun hterms).unique ?_
  have hne : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2 := (hasSum_hyp (a := -1 / 2) (b := 1 / 2) (c := 1) (z := c) hc hne).mul_left
    (Real.pi / 2)
  refine h2.congr_fun fun n => ?_
  ring

/-! ### PConstructible corollaries

The real downstream need: the two ₂F₁ families at rational `c ∈ (-1,1)`. Each is a
`2/π` multiple of the corresponding complete elliptic integral, so
`ellipticF_pi_div_two_Pconstructible` and `ellipticE_Pconstructible` close them. -/

-- Theorem: `₂F₁(1/2,1/2;1;c)` is P-constructible for P-constructible `|c| < 1`.
@[pconstructible_cond]
theorem hyp_half_half_one_Pconstructible {c : ℝ} (hcP : PConstructible c) (hc : |c| < 1) :
    PConstructible (hyp (1 / 2) (1 / 2) 1 c) := by
  have hc1 : c < 1 := (abs_lt.mp hc).2
  have h2 : hyp (1 / 2) (1 / 2) 1 c = (2 / Real.pi) * ellipticF c (Real.pi / 2) := by
    rw [ellipticF_pi_div_two_eq_hyp hc]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [h2]
  exact PConstructible.mul (PConstructible.div two_Pconstructible pi_Pconstructible)
    (ellipticF_pi_div_two_Pconstructible hcP hc1)

-- Theorem: `₂F₁(-1/2,1/2;1;c)` is P-constructible for P-constructible `|c| < 1`.
@[pconstructible_cond]
theorem hyp_neg_half_half_one_Pconstructible {c : ℝ} (hcP : PConstructible c) (hc : |c| < 1) :
    PConstructible (hyp (-1 / 2) (1 / 2) 1 c) := by
  have hc1 : c < 1 := (abs_lt.mp hc).2
  have h2 : hyp (-1 / 2) (1 / 2) 1 c = (2 / Real.pi) * ellipticE c (Real.pi / 2) := by
    rw [ellipticE_pi_div_two_eq_hyp hc]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [h2]
  exact PConstructible.mul (PConstructible.div two_Pconstructible pi_Pconstructible)
    (ellipticE_Pconstructible hcP (PConstructible.div pi_Pconstructible two_Pconstructible)
      hc1)

end

end Pconstructible
