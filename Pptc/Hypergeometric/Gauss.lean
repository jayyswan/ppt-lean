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
-- `Pptc.Hypergeometric.Euler` supplies the Beta integral `integral_rpow_mul_one_sub_rpow`,
-- the term integral `integral_term` and the Beta weight's interval integrability
-- `intervalIntegrable_weight`; `Pptc.Gamma` the twenty-fourth-denominator family of
-- P-constructible `Γ` values.
import Pptc.Hypergeometric.Basic
import Pptc.Hypergeometric.Euler
import Pptc.Hypergeometric.Contiguous
import Pptc.Gamma
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Pptc.Hypergeometric.Gauss

Gauss's summation theorem for the Gauss hypergeometric function at the argument `z = 1`,

`₂F₁(a, b; c; 1) = Γ(c) Γ(c − a − b) / (Γ(c − a) Γ(c − b))` for `a, b > 0`, `c > b`,
`c − a − b > 0`,

and the resulting P-constructible family: whenever `24a`, `24b`, `24c` are integers in the
range where the theorem applies, `₂F₁(a, b; c; 1)` is P-constructible, because the three
`Γ` values on the right are P-constructible by `Gamma_intCast_div_twentyfour_Pconstructible`.

## Why the integral cannot be evaluated directly at `z = 1`

The Euler representation `hyp_eq_integral` of L7a carries the strict hypothesis `|z| < 1`,
which `z = 1` does not satisfy, so it cannot be specialised at the summation point. Instead
we expand the limiting integrand `(1 − t)^(−a)` in its *own* binomial series
`₂F₁(a, b; b; t) = ∑ₙ (a)ₙ/n! tⁿ` and integrate term by term against the Beta weight
`t^(b−1) (1 − t)^(c−b−1)` over `[0, 1]`.

For `a > 0` every term is non-negative, which is what makes the interchange painless: the
dominating function of `intervalIntegral.hasSum_integral_of_dominated_convergence` can be
taken to be the terms themselves, and the pointwise sum of the dominating series is the
single explicit function `t ↦ t^(b−1) (1 − t)^(c−a−b−1)`, which is interval integrable by
`intervalIntegrable_weight`. This is the same dominated-convergence skeleton as Euler.lean,
with the uniform geometric weight `ρⁿ` replaced by the exact limiting sum.

The `n`-th term integrates to `hypCoeff a b c n` divided by the Beta prefactor (this is
`integral_term` at `z = 1`), so the series on the integral side is *literally* the
hypergeometric series at `1`; `hyp_eq_tsum_coeff` at `z = 1` then identifies
`hyp a b c 1` with the prefactor times the integral, and the Beta integral
`integral_rpow_mul_one_sub_rpow` finishes the evaluation.
-/

open scoped Topology ENNReal BigOperators

namespace Pconstructible

noncomputable section

/-! ### Gauss's summation theorem

The proof is the term-by-term integration described in the module docstring. The only
delicate point is the pointwise identification of the dominating series with
`t^(b−1)(1−t)^(c−a−b−1)`: it is a binomial series evaluated at `t < 1`, so it holds on the
open interval and only there — the interval-integral lemmas `integral_congr_uIoo` and
`IntervalIntegrable.congr_uIoo` exist precisely so that the endpoint `t = 1` can be
discarded. -/

set_option linter.unusedVariables false in
/-- **Gauss's summation theorem.** For positive `a`, `b` with `b < c` and `c − a − b > 0`,

`₂F₁(a, b; c; 1) = Γ(c) Γ(c − a − b) / (Γ(c − a) Γ(c − b))`.

The hypotheses `a, b > 0` and `b < c` are what the term-by-term Beta-integral proof needs;
the `hc` hypothesis records that `c` is not a nonpositive integer, so that the Gamma values
in the prefactor are non-zero. General real parameters follow from this case by the
contiguous relations, but that extension is not formalized here. -/
-- Theorem: Gauss's summation theorem for `₂F₁` at `z = 1`.
theorem hyp_one_eq_Gamma {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hbc : b < c)
    (h : 0 < c - a - b) (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    hyp a b c 1 = Real.Gamma c * Real.Gamma (c - a - b) /
      (Real.Gamma (c - a) * Real.Gamma (c - b)) := by
  have hcpos : 0 < c := lt_trans hb hbc
  have hbne : ∀ n : ℕ, b ≠ -(n : ℝ) := ne_neg_nat_of_pos hb
  -- Positivity of the hypergeometric coefficients `(a)ₙ/n!` and of the Beta weight.
  have hcoeff_nonneg : ∀ n : ℕ, 0 ≤ hypCoeff a b b n := by
    intro n
    rw [hypCoeff_self a b hbne n]
    exact div_nonneg (le_of_lt (ascPochhammer_pos n a ha)) (by positivity)
  -- The binomial series `₂F₁(a, b; b; t) = (1 − t)^(−a)` as a `HasSum`.
  have hpoint : ∀ t : ℝ, |t| < 1 →
      HasSum (fun n : ℕ => hypCoeff a b b n * t ^ n) ((1 - t) ^ (-a)) := by
    intro t ht
    rw [← hyp_self_eq_rpow hbne ht]
    exact hasSum_hyp (a := a) (b := b) (c := b) (z := t) ht hbne
  -- The endpoint `t = 1` is the only point where the binomial series no longer converges;
  -- it is negligible, and the a.e. hypotheses below discard it.
  have hae1 : ∀ᵐ t : ℝ, t ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  -- Term-by-term integration of `(1 − t)^(−a)` against the Beta weight.
  have hmain : HasSum (fun n : ℕ => ∫ t in (0 : ℝ)..1,
        hypCoeff a b b n * t ^ n * (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))
      (∫ t in (0 : ℝ)..1, (1 - t) ^ (-a) * (t ^ (b - 1) * (1 - t) ^ (c - b - 1))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
      (bound := fun n t => hypCoeff a b b n * t ^ n * (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))
    · intro n
      exact (by fun_prop : Measurable (fun t : ℝ => hypCoeff a b b n * t ^ n *
        (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht0 : (0 : ℝ) ≤ t := ht.1.le
      have h1t : 0 ≤ 1 - t := by linarith [ht.2]
      have hf : 0 ≤ hypCoeff a b b n * t ^ n * (t ^ (b - 1) * (1 - t) ^ (c - b - 1)) :=
        mul_nonneg (mul_nonneg (hcoeff_nonneg n) (pow_nonneg ht0 n))
          (mul_nonneg (Real.rpow_nonneg ht0 _) (Real.rpow_nonneg h1t _))
      rw [Real.norm_eq_abs, abs_of_nonneg hf]
    · refine hae1.mono fun t htne htmem => ?_
      rw [Set.uIoc_of_le zero_le_one] at htmem
      have ht1 : t < 1 := lt_of_le_of_ne htmem.2 htne
      have hzt : |t| < 1 := by rw [abs_of_pos htmem.1]; exact ht1
      exact ((hpoint t hzt).mul_right _).summable
    · refine (intervalIntegrable_weight b (c - a) hb (by linarith)).congr_uIoo ?_
      intro t ht
      rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      dsimp only
      have h1t : 0 < 1 - t := by linarith [ht.2]
      symm
      rw [tsum_mul_right, (hpoint t (by rw [abs_of_pos ht.1]; exact ht.2)).tsum_eq,
        ← mul_assoc, mul_comm ((1 - t) ^ (-a)) (t ^ (b - 1)), mul_assoc, ← Real.rpow_add h1t,
        show (-a) + (c - b - 1) = (c - a) - b - 1 by ring]
    · refine hae1.mono fun t htne htmem => ?_
      rw [Set.uIoc_of_le zero_le_one] at htmem
      have ht1 : t < 1 := lt_of_le_of_ne htmem.2 htne
      have hzt : |t| < 1 := by rw [abs_of_pos htmem.1]; exact ht1
      exact (hpoint t hzt).mul_right _
  -- Each term integrates to `hypCoeff a b c n` divided by the prefactor.
  have hterm : ∀ n : ℕ, ∫ t in (0 : ℝ)..1,
        hypCoeff a b b n * t ^ n * (t ^ (b - 1) * (1 - t) ^ (c - b - 1)) =
      hypCoeff a b c n / (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) := by
    intro n
    simpa using integral_term a b c 1 hb hbc n
  have hmain' : HasSum (fun n : ℕ => hypCoeff a b c n /
        (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))))
      (∫ t in (0 : ℝ)..1, (1 - t) ^ (-a) * (t ^ (b - 1) * (1 - t) ^ (c - b - 1))) :=
    hmain.congr_fun fun n => (hterm n).symm
  -- The limiting integral is the Beta value `B(b, c − a − b)`.
  have hInt : (∫ t in (0 : ℝ)..1, (1 - t) ^ (-a) * (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))
      = Real.Gamma b * Real.Gamma (c - a - b) / Real.Gamma (c - a) := by
    have hcongr : (∫ t in (0 : ℝ)..1, (1 - t) ^ (-a) * (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))
        = ∫ t in (0 : ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - a - b - 1) := by
      refine intervalIntegral.integral_congr_uIoo ?_
      intro t ht
      rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      dsimp only
      have h1t : 0 < 1 - t := by linarith [ht.2]
      rw [← mul_assoc, mul_comm ((1 - t) ^ (-a)) (t ^ (b - 1)), mul_assoc, ← Real.rpow_add h1t,
        show (-a) + (c - b - 1) = c - a - b - 1 by ring]
    rw [hcongr, integral_rpow_mul_one_sub_rpow b (c - a - b) hb h,
      show b + (c - a - b) = c - a by ring]
  -- Recombine: multiply back by the prefactor and identify with the `tsum` definition.
  have hPne : Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) ≠ 0 :=
    div_ne_zero (Real.Gamma_pos_of_pos hcpos).ne'
      (mul_ne_zero (Real.Gamma_pos_of_pos hb).ne' (Real.Gamma_pos_of_pos (by linarith)).ne')
  have hscaled := hmain'.mul_right (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)))
  have hsc : (fun n : ℕ => (hypCoeff a b c n /
        (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)))) *
        (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))))
      = fun n : ℕ => hypCoeff a b c n := by
    funext n
    exact div_mul_cancel₀ _ hPne
  rw [hsc] at hscaled
  have huniq : hyp a b c 1 = (Real.Gamma b * Real.Gamma (c - a - b) / Real.Gamma (c - a)) *
      (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) := by
    rw [hyp_eq_tsum_coeff a b c 1]
    simp only [one_pow, mul_one]
    rw [hscaled.tsum_eq, hInt]
  rw [huniq]
  have hGca : Real.Gamma (c - a) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < c - a)).ne'
  have hGcb : Real.Gamma (c - b) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < c - b)).ne'
  field_simp

/-! ### Convergence of the hypergeometric series at `z = 1`

Abel's theorem is the tool that lets a relation proved on `|z| < 1` be evaluated at `z = 1`,
but it needs the series to converge there. That is the content of `summable_hypCoeff_one`:

the ratio of consecutive coefficients is

`c_{n+1}/c_n = (a+n)(b+n)/((c+n)(n+1)) = 1 − (1 + c − a − b)/n + O(1/n²)`,

so with `s = c − a − b > 0` and `α = 1 + s/2` (chosen with `1 < α < 1 + s`) the ratio is
eventually `≤ (1 − 1/n)^α`, by Bernoulli. Then `|c_n| n^α` is eventually nonincreasing, hence
`|c_n| = O(n^{−α})` with `α > 1`, and comparison with the `p`-series `∑ n^{−α}` finishes. -/

-- Theorem: eventual `n^(-α)` decay of the coefficients `hypCoeff a b c n` at `z = 1`.
theorem hypCoeff_le_const_mul_rpow_neg {a b c : ℝ} (h : 0 < c - a - b) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      ‖hypCoeff a b c n‖ ≤ C * (n : ℝ) ^ (-(1 + (c - a - b) / 2)) := by
  set s : ℝ := c - a - b with hs
  have hspos : 0 < s := by rw [hs]; linarith
  set α : ℝ := 1 + s / 2 with hα
  have hα1 : 1 ≤ α := by rw [hα]; linarith
  have hαgt : 1 < α := by rw [hα]; linarith
  have hαs : α < 1 + s := by rw [hα]; linarith
  -- The ratio of consecutive hypergeometric coefficients.
  set R : ℕ → ℝ := fun k => ((a + k) * (b + k)) / ((c + k) * (k + 1)) with hR
  have hstep : ∀ k : ℕ, hypCoeff a b c (k + 1) = hypCoeff a b c k * R k := by
    intro k
    rw [hR]
    exact hypCoeff_succ a b c k
  -- Eventually the ratio is positive.
  have hpos : ∀ᶠ k : ℕ in Filter.atTop, 0 < R k := by
    rw [hR]
    obtain ⟨K, hK⟩ := exists_nat_gt (max (max (-a) (-b)) (max (-c) 0) + 1)
    refine Filter.eventually_atTop.2 ⟨K, fun k hk => ?_⟩
    have hKle : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hka : -a < (k : ℝ) := by
      have h1 : -a ≤ max (max (-a) (-b)) (max (-c) 0) :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      linarith
    have hkb : -b < (k : ℝ) := by
      have h1 : -b ≤ max (max (-a) (-b)) (max (-c) 0) :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      linarith
    have hkc : -c < (k : ℝ) := by
      have h1 : -c ≤ max (max (-a) (-b)) (max (-c) 0) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      linarith
    exact div_pos (mul_pos (by linarith) (by linarith)) (mul_pos (by linarith) (by positivity))
  -- Eventually the ratio is at most `(1 - 1/k)^α`.
  have hbnd : ∀ᶠ k : ℕ in Filter.atTop, R k ≤ (((k : ℝ) - 1) / (k : ℝ)) ^ α := by
    obtain ⟨K, hK⟩ := exists_nat_gt
      (max (max 1 (-c)) ((|c - a * b - α * (c + 1)| + |α * c| + 1) / (1 + s - α)))
    refine Filter.eventually_atTop.2 ⟨K, fun k hk => ?_⟩
    have hKle : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have h1 : (1 : ℝ) ≤ max (max 1 (-c))
          ((|c - a * b - α * (c + 1)| + |α * c| + 1) / (1 + s - α)) :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      linarith
    have hck : (0 : ℝ) < c + (k : ℝ) := by
      have h1 : -c ≤ max (max 1 (-c))
          ((|c - a * b - α * (c + 1)| + |α * c| + 1) / (1 + s - α)) :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      linarith
    have hspos' : 0 < 1 + s - α := by linarith
    -- The key estimate: `(1 + s - α) k ≥ |B| + |α c| + 1`.
    have hkey : (1 + s - α) * (k : ℝ) ≥
        |c - a * b - α * (c + 1)| + |α * c| + 1 := by
      have h2 : ((|c - a * b - α * (c + 1)| + |α * c| + 1) / (1 + s - α)) < (K : ℝ) :=
        lt_of_le_of_lt (le_max_right _ _) hK
      have h3 : ((|c - a * b - α * (c + 1)| + |α * c| + 1) / (1 + s - α)) < (k : ℝ) :=
        lt_of_lt_of_le h2 hKle
      rw [div_lt_iff₀ hspos'] at h3
      linarith
    -- Hence `1 - R k ≥ α / k`.
    have hq : α * (c + (k : ℝ)) * ((k : ℝ) + 1)
        ≤ (k : ℝ) * ((1 + s) * (k : ℝ) + (c - a * b)) := by
      have hna := neg_le_abs (c - a * b - α * (c + 1))
      have hnb := le_abs_self (α * c)
      have hka := abs_nonneg (c - a * b - α * (c + 1))
      have hkb := abs_nonneg (α * c)
      nlinarith [hkey, hk1, hna, hnb, hka, hkb]
    have hRk : α / (k : ℝ) ≤ 1 - R k := by
      have hDpos : (0:ℝ) < (c + (k:ℝ)) * ((k:ℝ) + 1) := mul_pos hck (by positivity)
      have hck' : c + (k:ℝ) ≠ 0 := ne_of_gt hck
      have hk1ne : (k:ℝ) + 1 ≠ 0 := by positivity
      have hsimp : 1 - R k
          = ((1 + s) * (k:ℝ) + (c - a * b)) / ((c + (k:ℝ)) * ((k:ℝ) + 1)) := by
        rw [hR]
        field_simp
        rw [hs]
        ring
      have hkpos : (0:ℝ) < (k:ℝ) := by linarith
      rw [hsimp, div_le_iff₀ hkpos, div_mul_eq_mul_div, le_div_iff₀ hDpos]
      linarith [hq]
    -- Bernoulli: `1 - α/k ≤ (1 - 1/k)^α`.
    have hbern : 1 - α / (k : ℝ) ≤ (1 - 1 / (k : ℝ)) ^ α := by
      have hkpos : (0:ℝ) < (k:ℝ) := by linarith
      have hs' : (-1 : ℝ) ≤ -(1 / (k : ℝ)) := by
        rw [neg_le_neg_iff, div_le_iff₀ hkpos]
        linarith
      have := one_add_mul_self_le_rpow_one_add hs' hα1
      rwa [show (1 : ℝ) + α * (-(1 / (k:ℝ))) = 1 - α / (k:ℝ) by ring,
        show (1 : ℝ) + -(1 / (k:ℝ)) = 1 - 1 / (k:ℝ) by ring] at this
    have hkne : (k : ℝ) ≠ 0 := by linarith
    rw [show ((k : ℝ) - 1) / (k:ℝ) = 1 - 1 / (k:ℝ) by rw [sub_div, div_self hkne]]
    linarith
  have hk1ev : ∀ᶠ k : ℕ in Filter.atTop, 1 ≤ k := Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      1 ≤ k ∧ 0 < R k ∧ R k ≤ (((k : ℝ) - 1) / (k : ℝ)) ^ α := hk1ev.and (hpos.and hbnd)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  -- `|c_n| n^α` is nonincreasing for `n ≥ N`.
  have hcoef : ∀ m : ℕ, N ≤ m → R m * ((m : ℝ) + 1) ^ α ≤ (m : ℝ) ^ α := by
    intro m hm
    obtain ⟨hm1, hRpos, hRbnd⟩ := hN m hm
    have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1'
    have h1 : ((m : ℝ) - 1) / (m : ℝ) * ((m : ℝ) + 1) = ((m : ℝ) ^ 2 - 1) / (m : ℝ) := by
      rw [div_mul_eq_mul_div]; congr 1; ring
    calc R m * ((m : ℝ) + 1) ^ α
        ≤ (((m : ℝ) - 1) / (m : ℝ)) ^ α * ((m : ℝ) + 1) ^ α :=
          mul_le_mul_of_nonneg_right hRbnd (Real.rpow_nonneg (by positivity) _)
      _ = ((((m : ℝ) - 1) / (m : ℝ)) * ((m : ℝ) + 1)) ^ α := by
          rw [← Real.mul_rpow (div_nonneg (by linarith) (le_of_lt hmpos))
            (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1)]
      _ = (((m : ℝ) ^ 2 - 1) / (m : ℝ)) ^ α := by rw [h1]
      _ ≤ (m : ℝ) ^ α := by
          refine Real.rpow_le_rpow (div_nonneg (by nlinarith) (le_of_lt hmpos)) ?_
            (by linarith : (0 : ℝ) ≤ α)
          rw [div_le_iff₀ hmpos]; nlinarith
  have hmono : ∀ n, N ≤ n →
      ‖hypCoeff a b c n‖ * (n : ℝ) ^ α ≤ ‖hypCoeff a b c N‖ * (N : ℝ) ^ α := by
    have aux : ∀ j : ℕ,
        ‖hypCoeff a b c (N + j)‖ * ((N + j : ℕ) : ℝ) ^ α
          ≤ ‖hypCoeff a b c N‖ * (N : ℝ) ^ α := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          rw [Nat.add_succ]
          have hcast : (((N + j + 1 : ℕ)) : ℝ) = ((N + j : ℕ) : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          obtain ⟨hm1, hRpos, hRbnd⟩ := hN (N + j) (Nat.le_add_right N j)
          have habs : ‖hypCoeff a b c (N + j + 1)‖
              = ‖hypCoeff a b c (N + j)‖ * R (N + j) := by
            rw [hstep (N + j)]
            simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hRpos.le]
          rw [habs]
          calc ‖hypCoeff a b c (N + j)‖ * R (N + j) * (((N + j : ℕ) : ℝ) + 1) ^ α
              = ‖hypCoeff a b c (N + j)‖
                  * (R (N + j) * (((N + j : ℕ) : ℝ) + 1) ^ α) := by ring
            _ ≤ ‖hypCoeff a b c (N + j)‖ * (((N + j : ℕ) : ℝ)) ^ α :=
                mul_le_mul_of_nonneg_left (hcoef (N + j) (Nat.le_add_right N j)) (norm_nonneg _)
            _ ≤ ‖hypCoeff a b c N‖ * (N : ℝ) ^ α := ih
    intro n hn
    have h' := aux (n - N)
    rwa [Nat.add_sub_of_le hn] at h'
  -- Comparison with the `p`-series `∑ n^{-α}`.
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      ‖hypCoeff a b c n‖
        ≤ (‖hypCoeff a b c N‖ * (N : ℝ) ^ α) * (n : ℝ) ^ (-α) := by
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hm := hmono n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have := (hN n hn).1
      exact_mod_cast this
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
    have hrw : (n : ℝ) ^ α * (n : ℝ) ^ (-α) = 1 := by
      rw [← Real.rpow_add hnpos, add_neg_cancel, Real.rpow_zero]
    calc ‖hypCoeff a b c n‖
        = ‖hypCoeff a b c n‖ * ((n : ℝ) ^ α * (n : ℝ) ^ (-α)) := by rw [hrw, mul_one]
      _ = (‖hypCoeff a b c n‖ * (n : ℝ) ^ α) * (n : ℝ) ^ (-α) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hnpos.le _)
  exact ⟨‖hypCoeff a b c N‖ * (N : ℝ) ^ α, by
    rw [hα, hs] at hbound ⊢
    exact hbound⟩

-- Theorem: the hypergeometric series at `z = 1` converges when `c - a - b > 0`.
theorem summable_hypCoeff_one {a b c : ℝ} (h : 0 < c - a - b) :
    Summable (fun n : ℕ => hypCoeff a b c n) := by
  obtain ⟨C, hC⟩ := hypCoeff_le_const_mul_rpow_neg h
  exact Summable.of_norm_bounded_eventually_nat
    ((Real.summable_nat_rpow.mpr (by linarith : -(1 + (c - a - b) / 2) < -1)).mul_left C) hC

-- Theorem: `n · hypCoeff a b c n → 0` when `c - a - b > 0` (the decay behind the
-- convergence of the series at `z = 1`, made quantitative).
theorem tendsto_nat_mul_hypCoeff_one {a b c : ℝ} (h : 0 < c - a - b) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * hypCoeff a b c n) Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hypCoeff_le_const_mul_rpow_neg h
  set α : ℝ := 1 + (c - a - b) / 2 with hα
  have hCα : ∀ᶠ n : ℕ in Filter.atTop, ‖hypCoeff a b c n‖ ≤ C * (n : ℝ) ^ (-α) := by
    simpa only [hα] using hC
  have hlim : Filter.Tendsto (fun n : ℕ => C * (n : ℝ) ^ (1 - α)) Filter.atTop (𝓝 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - α)) Filter.atTop (𝓝 0) := by
      have hr := tendsto_rpow_neg_atTop (y := α - 1) (by rw [hα]; linarith)
      have hcomp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(α - 1))) Filter.atTop (𝓝 0) :=
        hr.comp tendsto_natCast_atTop_atTop
      simpa only [neg_sub] using hcomp
    simpa only [mul_zero] using h0.const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hCα, Filter.eventually_ge_atTop 1] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
  rw [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  have hcast : (n : ℝ) * (n : ℝ) ^ (-α) = (n : ℝ) ^ (1 - α) := by
    rw [show (1 : ℝ) - α = 1 + -α by ring, Real.rpow_add hnpos, Real.rpow_one]
  calc (n : ℝ) * ‖hypCoeff a b c n‖
      ≤ (n : ℝ) * (C * (n : ℝ) ^ (-α)) := mul_le_mul_of_nonneg_left hn (le_of_lt hnpos)
    _ = C * ((n : ℝ) * (n : ℝ) ^ (-α)) := by ring
    _ = C * (n : ℝ) ^ (1 - α) := by rw [hcast]

-- Theorem: `(1 - z) · d/dz ₂F₁(a,b;c;·)(z) → 0` as `z → 1⁻` when `c - a - b > 0`.
-- The power series of the left side has coefficients `(n+1)c_{n+1} - n c_n`, whose partial
-- sums telescope to `N c_N → 0`; Abel's theorem then gives the boundary limit.
theorem tendsto_one_sub_mul_deriv_hyp {a b c : ℝ} (h : 0 < c - a - b)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    Filter.Tendsto (fun z : ℝ => (1 - z) * deriv (fun w => hyp a b c w) z) (𝓝[<] 1) (𝓝 0) := by
  set d : ℕ → ℝ := fun n =>
    ((n : ℝ) + 1) * hypCoeff a b c (n + 1) - (n : ℝ) * hypCoeff a b c n with hd
  set g : ℕ → ℝ := fun m => (m : ℝ) * hypCoeff a b c m with hg
  have hpartial : Filter.Tendsto (fun N : ℕ => Finset.sum (Finset.range N) d)
      Filter.atTop (𝓝 0) := by
    have htele : ∀ N : ℕ, Finset.sum (Finset.range N) d = (N : ℝ) * hypCoeff a b c N := by
      intro N
      have hsum : Finset.sum (Finset.range N) d
          = Finset.sum (Finset.range N) (fun n => g (n + 1) - g n) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hd, hg]
        push_cast
        ring
      rw [hsum, Finset.sum_range_sub g N]
      simp [hg]
    simp only [htele]
    exact tendsto_nat_mul_hypCoeff_one h
  refine (Real.tendsto_tsum_powerSeries_nhdsWithin_lt hpartial).congr' ?_
  have hz0 : ∀ᶠ z : ℝ in 𝓝[<] 1, 0 < z :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hz0] with z hz1 hz0
  have hz : |z| < 1 := by rw [abs_of_pos hz0]; exact hz1
  have hderiv := hasSum_deriv_hyp (a := a) (b := b) (c := c) hc hz
  have hshift := hasSum_mul_z_shift hderiv
  have hshift' : HasSum (fun n : ℕ => ((n : ℝ) * hypCoeff a b c n) * z ^ n)
      (deriv (fun w => hyp a b c w) z * z) :=
    hshift.congr_fun fun n => by
      cases n with
      | zero => simp
      | succ m => simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]; push_cast; ring
  have hL := hderiv.sub hshift'
  have hLfun : (fun n : ℕ => ((n : ℝ) + 1) * hypCoeff a b c (n + 1) * z ^ n
      - ((n : ℝ) * hypCoeff a b c n) * z ^ n) = fun n => d n * z ^ n := by
    funext n
    rw [hd]
    ring
  rw [hLfun] at hL
  have hsum : deriv (fun w => hyp a b c w) z - deriv (fun w => hyp a b c w) z * z
      = (1 - z) * deriv (fun w => hyp a b c w) z := by ring
  rw [hsum] at hL
  exact hL.tsum_eq

/-! ### Abel's theorem: evaluating the contiguous relations at `z = 1`

With convergence at `z = 1` in hand, Abel's theorem identifies the value at the boundary
with the limit of the power series as `z → 1⁻`. This is the step that lets a relation proved
on the open unit disc, like the contiguous relation `hyp_contiguous_21`, be specialised to
`z = 1`. -/

-- Theorem: for `c - a - b > 0`, `₂F₁(a,b;c;z) → ₂F₁(a,b;c;1)` as `z → 1⁻` (Abel).
theorem tendsto_hyp_nhdsWithin_one {a b c : ℝ} (h : 0 < c - a - b) :
    Filter.Tendsto (fun z : ℝ => hyp a b c z) (𝓝[<] 1) (𝓝 (hyp a b c 1)) := by
  have hsum : HasSum (fun n : ℕ => hypCoeff a b c n) (hyp a b c 1) := by
    rw [hyp_eq_tsum_coeff a b c 1]
    simp only [one_pow, mul_one]
    exact (summable_hypCoeff_one h).hasSum
  have hlim := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hsum.tendsto_sum_nat
  have hfun : (fun z : ℝ => ∑' n : ℕ, hypCoeff a b c n * z ^ n) = fun z => hyp a b c z := by
    funext z
    exact (hyp_eq_tsum_coeff a b c z).symm
  rwa [hfun] at hlim

/-! ### The contiguous recurrence at `z = 1`

DLMF 15.5.21 holds on `|z| < 1`; Abel's theorem (`tendsto_hyp_nhdsWithin_one`) and the
vanishing of `(1 − z) ₂F₁′` at the boundary (`tendsto_one_sub_mul_deriv_hyp`) let it be
evaluated at `z = 1`, giving the recurrence in the parameter `c`,

`₂F₁(a,b;c+1;1) = c (c − a − b) / ((c − a)(c − b)) · ₂F₁(a,b;c;1)`. -/

-- Theorem: the contiguous relation `hyp_contiguous_21` evaluated at `z = 1`.
theorem hyp_one_recurrence {a b c : ℝ} (h : 0 < c - a - b)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : c - a ≠ 0) (hcb : c - b ≠ 0) :
    hyp a b (c + 1) 1 = c * (c - a - b) / ((c - a) * (c - b)) * hyp a b c 1 := by
  have hc1 : ∀ n : ℕ, c + 1 ≠ -(n : ℝ) := by
    intro n hcon
    exact hc (n + 1) (by push_cast at hcon ⊢; linarith)
  have h1 : Filter.Tendsto (fun z : ℝ => hyp a b (c + 1) z) (𝓝[<] 1)
      (𝓝 (hyp a b (c + 1) 1)) :=
    tendsto_hyp_nhdsWithin_one (by linarith : 0 < (c + 1) - a - b)
  have h2 : Filter.Tendsto (fun z : ℝ => hyp a b c z) (𝓝[<] 1) (𝓝 (hyp a b c 1)) :=
    tendsto_hyp_nhdsWithin_one h
  have hlim : Filter.Tendsto
      (fun z : ℝ => (c - a) * (c - b) * hyp a b (c + 1) z + c * (a + b - c) * hyp a b c z)
      (𝓝[<] 1)
      (𝓝 ((c - a) * (c - b) * hyp a b (c + 1) 1 + c * (a + b - c) * hyp a b c 1)) :=
    (h1.const_mul ((c - a) * (c - b))).add (h2.const_mul (c * (a + b - c)))
  have hlim0 : Filter.Tendsto (fun z : ℝ => c * (1 - z) * deriv (fun w => hyp a b c w) z)
      (𝓝[<] 1) (𝓝 0) := by
    simpa only [mul_zero, mul_assoc] using (tendsto_one_sub_mul_deriv_hyp h hc).const_mul c
  have heq : (fun z : ℝ => c * (1 - z) * deriv (fun w => hyp a b c w) z) =ᶠ[𝓝[<] 1]
      (fun z : ℝ => (c - a) * (c - b) * hyp a b (c + 1) z + c * (a + b - c) * hyp a b c z) := by
    have hz0 : ∀ᶠ z : ℝ in 𝓝[<] 1, 0 < z :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hz0] with z hz1 hz0
    exact hyp_contiguous_21 hc hc1 (by rw [abs_of_pos hz0]; exact hz1)
  have hval : (c - a) * (c - b) * hyp a b (c + 1) 1 + c * (a + b - c) * hyp a b c 1 = 0 :=
    tendsto_nhds_unique hlim (hlim0.congr' heq)
  have hp : (c - a) * (c - b) ≠ 0 := mul_ne_zero hca hcb
  have hX : (c - a) * (c - b) * hyp a b (c + 1) 1 = c * (c - a - b) * hyp a b c 1 := by
    linarith [hval]
  rw [show hyp a b (c + 1) 1 = c * (c - a - b) * hyp a b c 1 / ((c - a) * (c - b)) by
    rw [eq_div_iff hp]
    linarith [hX]]
  ring

/-- The `Γ`-ratio `Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b))` obeys the same recurrence in `c` as the
value `₂F₁(a,b;c;1)` — this is what makes the quotient of the two independent of `c`. -/
-- Theorem: `Γ(c+1)Γ(c+1-a-b)/(Γ(c+1-a)Γ(c+1-b))
--   = c(c-a-b)/((c-a)(c-b)) · Γ(c)Γ(c-a-b)/(Γ(c-a)Γ(c-b))`.
theorem Gamma_ratio_succ {a b c : ℝ} (h : 0 < c - a - b) (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ)) (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) :
    Real.Gamma (c + 1) * Real.Gamma (c + 1 - a - b) /
        (Real.Gamma (c + 1 - a) * Real.Gamma (c + 1 - b))
      = c * (c - a - b) / ((c - a) * (c - b)) *
        (Real.Gamma c * Real.Gamma (c - a - b) /
          (Real.Gamma (c - a) * Real.Gamma (c - b))) := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hs0 : c - a - b ≠ 0 := ne_of_gt h
  have hca0 : c - a ≠ 0 := by simpa using hca 0
  have hcb0 : c - b ≠ 0 := by simpa using hcb 0
  rw [show c + 1 - a - b = (c - a - b) + 1 by ring,
    show c + 1 - a = (c - a) + 1 by ring,
    show c + 1 - b = (c - b) + 1 by ring,
    Real.Gamma_add_one hc0, Real.Gamma_add_one hs0, Real.Gamma_add_one hca0,
    Real.Gamma_add_one hcb0]
  have hGc : Real.Gamma c ≠ 0 := Real.Gamma_ne_zero hc
  have hGs : Real.Gamma (c - a - b) ≠ 0 := (Real.Gamma_pos_of_pos h).ne'
  have hGca : Real.Gamma (c - a) ≠ 0 := Real.Gamma_ne_zero hca
  have hGcb : Real.Gamma (c - b) ≠ 0 := Real.Gamma_ne_zero hcb
  field_simp

-- Theorem: `₂F₁(a,b;c;1) / (Γ(c)Γ(c-a-b)/(Γ(c-a)Γ(c-b)))` is invariant under `c ↦ c+1`.
theorem hyp_one_div_Gamma_succ {a b c : ℝ} (h : 0 < c - a - b)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ))
    (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) :
    hyp a b (c + 1) 1 /
        (Real.Gamma (c + 1) * Real.Gamma (c + 1 - a - b) /
          (Real.Gamma (c + 1 - a) * Real.Gamma (c + 1 - b)))
      = hyp a b c 1 /
        (Real.Gamma c * Real.Gamma (c - a - b) /
          (Real.Gamma (c - a) * Real.Gamma (c - b))) := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hca0 : c - a ≠ 0 := by simpa using hca 0
  have hcb0 : c - b ≠ 0 := by simpa using hcb 0
  have hk : c * (c - a - b) / ((c - a) * (c - b)) ≠ 0 :=
    div_ne_zero (mul_ne_zero hc0 (ne_of_gt h)) (mul_ne_zero hca0 hcb0)
  rw [hyp_one_recurrence h hc hca0 hcb0, Gamma_ratio_succ h hc hca hcb]
  exact mul_div_mul_left _ _ hk

/-! ### The denominator-24 family

Instantiating Gauss's theorem at `a = m/24`, `b = n/24`, `c = l/24` turns the sum into a
quotient of four `Γ` values whose arguments all have denominator `24`
(`l/24`, `(l − m − n)/24`, `(l − m)/24`, `(l − n)/24`). Every one is P-constructible by
`Gamma_intCast_div_twentyfour_Pconstructible`, so their product and quotient are too. -/

-- Theorem: `₂F₁(m/24, n/24; l/24; 1)` is P-constructible for integers `m, n, l` with
-- `m, n > 0`, `l − m − n > 0` and `l/24 ∉ -ℕ`.
theorem hyp_one_Pconstructible_of_den_24 {m n l : ℤ}
    (hm : 0 < (m : ℝ)) (hn : 0 < (n : ℝ))
    (h : 0 < (l : ℝ) / 24 - (m : ℝ) / 24 - (n : ℝ) / 24)
    (hc : ∀ k : ℕ, (l : ℝ) / 24 ≠ -(k : ℝ)) :
    PConstructible (hyp ((m : ℝ) / 24) ((n : ℝ) / 24) ((l : ℝ) / 24) 1) := by
  have ha : 0 < (m : ℝ) / 24 := by positivity
  have hb : 0 < (n : ℝ) / 24 := by positivity
  have hbc : (n : ℝ) / 24 < (l : ℝ) / 24 := by linarith
  rw [hyp_one_eq_Gamma ha hb hbc h hc]
  rw [show (l : ℝ) / 24 - (m : ℝ) / 24 - (n : ℝ) / 24 =
        (((l - m - n : ℤ) : ℝ)) / 24 by push_cast; ring,
      show (l : ℝ) / 24 - (m : ℝ) / 24 = (((l - m : ℤ) : ℝ)) / 24 by push_cast; ring,
      show (l : ℝ) / 24 - (n : ℝ) / 24 = (((l - n : ℤ) : ℝ)) / 24 by push_cast; ring]
  exact PConstructible.div
    (PConstructible.mul (Gamma_intCast_div_twentyfour_Pconstructible l)
      (Gamma_intCast_div_twentyfour_Pconstructible (l - m - n)))
    (PConstructible.mul (Gamma_intCast_div_twentyfour_Pconstructible (l - m))
      (Gamma_intCast_div_twentyfour_Pconstructible (l - n)))

/-! ### Lifting the positivity hypotheses of Gauss's theorem

The original `hyp_one_eq_Gamma` needs `a, b > 0` and `b < c` because it is proved by a
term-by-term Beta integral. Those hypotheses can be removed using the contiguous relations
already developed: `hyp_one_recurrence` and the matching `Γ`-ratio invariance
`hyp_one_div_Gamma_succ` identify `D a b c = ₂F₁(a,b;c;1) / g a b c` along the `c` direction,
where `g a b c = Γ c Γ(c−a−b)/(Γ(c−a)Γ(c−b))`, and a second relation shifts `a` while also
shifting `c`. Composing the two moves `(a,b,c) ↦ (a+1,b+1,c+2)` leaves `D` unchanged, so any
admissible triple can be moved into the region where the original theorem applies.

The `a`-shift comes from DLMF 15.5.20a (`hyp_shift_a_down`) taken at `(a+1, b, c+1)` and then
to the limit `z → 1⁻`. Because the *new* parameters still satisfy `c − a − b > 0`, both sides
converge at `1` and the relation is non-degenerate; the hypothesis `b ≠ 0` is what 15.5.20a
itself requires. -/

/-- The `Γ`-quotient of Gauss's theorem, as a function of the parameters. -/
def gaussRatio (a b c : ℝ) : ℝ :=
  Real.Gamma c * Real.Gamma (c - a - b) / (Real.Gamma (c - a) * Real.Gamma (c - b))

-- Theorem: `hypCoeff 0 b c n = 0` for `n ≠ 0`.
lemma hypCoeff_zero_left (b c : ℝ) {n : ℕ} (hn : n ≠ 0) : hypCoeff 0 b c n = 0 := by
  have h0 : (ascPochhammer ℝ n).eval (0 : ℝ) = 0 :=
    (ascPochhammer_eval_eq_zero_iff n (0 : ℝ)).2 ⟨0, Nat.pos_of_ne_zero hn, by simp⟩
  unfold hypCoeff ordinaryHypergeometricCoefficient
  rw [h0]
  ring

-- Theorem: `hyp 0 b c z = 1` (the series truncates to the constant term).
lemma hyp_zero_left (b c z : ℝ) : hyp 0 b c z = 1 := by
  have hsum : (∑' n : ℕ, hypCoeff 0 b c n * z ^ n) = hypCoeff 0 b c 0 * z ^ 0 :=
    tsum_eq_single 0 (fun n hn => by rw [hypCoeff_zero_left b c hn, zero_mul])
  rw [hyp_eq_tsum_coeff, hsum]
  simp [hypCoeff, ordinaryHypergeometricCoefficient]

-- Theorem: `₂F₁(a+1,b;c+1;1) = (c-a)/(c-a-b) · ₂F₁(a,b;c+1;1)`, the non-degenerate `a`-shift.
theorem hyp_shift_a_up_one {a b c : ℝ} (h : 0 < c - a - b) (ha : a ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : c - a ≠ 0) (hcb : c - b ≠ 0) :
    hyp (a + 1) b (c + 1) 1 = (c - a) / (c - a - b) * hyp a b (c + 1) 1 := by
  have hcab : c - a - b ≠ 0 := ne_of_gt h
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hc1 : ∀ n : ℕ, c + 1 ≠ -(n : ℝ) := by
    intro n hcon
    exact hc (n + 1) (by push_cast at hcon ⊢; linarith)
  have hcm : ∀ n : ℕ, c + 1 - 1 ≠ -(n : ℝ) := by
    intro n
    rw [show c + 1 - 1 = c by ring]
    exact hc n
  have h1 : Filter.Tendsto (fun z : ℝ => hyp a b (c + 1) z) (𝓝[<] 1)
      (𝓝 (hyp a b (c + 1) 1)) :=
    tendsto_hyp_nhdsWithin_one (by linarith : 0 < (c + 1) - a - b)
  have h2 : Filter.Tendsto (fun z : ℝ => hyp (a + 1) b (c + 1) z) (𝓝[<] 1)
      (𝓝 (hyp (a + 1) b (c + 1) 1)) :=
    tendsto_hyp_nhdsWithin_one (by linarith : 0 < (c + 1) - (a + 1) - b)
  have h3 : Filter.Tendsto (fun z : ℝ => hyp a b c z) (𝓝[<] 1) (𝓝 (hyp a b c 1)) :=
    tendsto_hyp_nhdsWithin_one h
  have hlim : Filter.Tendsto
      (fun z : ℝ => (c - a) * hyp a b (c + 1) z + a * hyp (a + 1) b (c + 1) z
        - c * hyp a b c z) (𝓝[<] 1)
      (𝓝 ((c - a) * hyp a b (c + 1) 1 + a * hyp (a + 1) b (c + 1) 1
        - c * hyp a b c 1)) :=
    ((h1.const_mul (c - a)).add (h2.const_mul a)).sub (h3.const_mul c)
  have heq : (fun z : ℝ => (c - a) * hyp a b (c + 1) z + a * hyp (a + 1) b (c + 1) z
        - c * hyp a b c z) =ᶠ[𝓝[<] 1] (fun _ : ℝ => 0) := by
    have hz0 : ∀ᶠ z : ℝ in 𝓝[<] 1, 0 < z :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hz0] with z hzlt hzpos
    have hcc := hyp_contiguous_c (a := a) (b := b) (c := c + 1) hc1 hcm
      (by rw [abs_of_pos hzpos]; exact hzlt)
    rw [show c + 1 - 1 = c by ring, show c + 1 - a - 1 = c - a by ring] at hcc
    exact hcc
  have hval : (c - a) * hyp a b (c + 1) 1 + a * hyp (a + 1) b (c + 1) 1
      - c * hyp a b c 1 = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' heq.symm)
  have hp : hyp a b c 1 = (c - a) * (c - b) / (c * (c - a - b)) * hyp a b (c + 1) 1 := by
    rw [hyp_one_recurrence h hc hca hcb]
    field_simp
  rw [hp] at hval
  have hterm : c * ((c - a) * (c - b) / (c * (c - a - b)) * hyp a b (c + 1) 1)
      = (c - a) * (c - b) / (c - a - b) * hyp a b (c + 1) 1 := by
    field_simp
  rw [hterm] at hval
  have hkey : a * (hyp (a + 1) b (c + 1) 1 * (c - a - b))
      = a * ((c - a) * hyp a b (c + 1) 1) := by
    have h := hval
    field_simp at h
    ring_nf at h ⊢
    linear_combination h
  have hcancel : hyp (a + 1) b (c + 1) 1 * (c - a - b) = (c - a) * hyp a b (c + 1) 1 :=
    mul_left_cancel₀ ha hkey
  rw [div_mul_eq_mul_div, eq_div_iff hcab]
  exact hcancel

-- Theorem: `₂F₁(a,b+1;c+1;1) = (c-b)/(c-a-b) · ₂F₁(a,b;c+1;1)`, the non-degenerate `b`-shift.
theorem hyp_shift_b_up_one {a b c : ℝ} (h : 0 < c - a - b) (hb : b ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : c - a ≠ 0) (hcb : c - b ≠ 0) :
    hyp a (b + 1) (c + 1) 1 = (c - b) / (c - a - b) * hyp a b (c + 1) 1 := by
  have h' := hyp_shift_a_up_one (a := b) (b := a) (c := c) (by linarith) hb hc hcb hca
  rw [show c - b - a = c - a - b by ring] at h'
  rw [hyp_comm a (b + 1) (c + 1) 1, hyp_comm a b (c + 1) 1]
  exact h'

/-- The diagonal `a`-shift at `z = 1`: `₂F₁(a+1,b;c+1;1) = c/(c-b) · ₂F₁(a,b;c;1)`, the
composition of the `a`-up relation with the recurrence in `c`. -/
-- Theorem: `₂F₁(a+1,b;c+1;1) = c/(c-b) · ₂F₁(a,b;c;1)`.
theorem hyp_one_diag_a {a b c : ℝ} (h : 0 < c - a - b) (ha : a ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : c - a ≠ 0) (hcb : c - b ≠ 0) :
    hyp (a + 1) b (c + 1) 1 = c / (c - b) * hyp a b c 1 := by
  rw [hyp_shift_a_up_one h ha hc hca hcb, hyp_one_recurrence h hc hca hcb]
  field_simp

-- Theorem: `₂F₁(a,b+1;c+1;1) = c/(c-a) · ₂F₁(a,b;c;1)`.
theorem hyp_one_diag_b {a b c : ℝ} (h : 0 < c - a - b) (hb : b ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : c - a ≠ 0) (hcb : c - b ≠ 0) :
    hyp a (b + 1) (c + 1) 1 = c / (c - a) * hyp a b c 1 := by
  rw [hyp_shift_b_up_one h hb hc hca hcb, hyp_one_recurrence h hc hca hcb]
  field_simp

/-- `D a b c = ₂F₁(a,b;c;1) / g a b c`, the quotient that the recurrences pin down. -/
def hypD (a b c : ℝ) : ℝ := hyp a b c 1 / gaussRatio a b c

-- Theorem: `hyp a 0 c z = 1` (the second numerator parameter).
lemma hyp_zero_right (a c z : ℝ) : hyp a 0 c z = 1 := by
  rw [hyp_comm a 0 c z, hyp_zero_left]

-- Theorem: `g a b c ≠ 0` when `c`, `c-a`, `c-b` are not nonpositive integers.
theorem gaussRatio_ne_zero {a b c : ℝ} (h : 0 < c - a - b)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ))
    (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) : gaussRatio a b c ≠ 0 := by
  unfold gaussRatio
  exact div_ne_zero
    (mul_ne_zero (Real.Gamma_ne_zero hc) (Real.Gamma_pos_of_pos h).ne')
    (mul_ne_zero (Real.Gamma_ne_zero hca) (Real.Gamma_ne_zero hcb))

-- Theorem: `g (a+1) b (c+1) = c/(c-b) · g a b c`.
theorem gaussRatio_shift_a {a b c : ℝ} (h : 0 < c - a - b)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ))
    (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) :
    gaussRatio (a + 1) b (c + 1) = c / (c - b) * gaussRatio a b c := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hcb0 : c - b ≠ 0 := by simpa using hcb 0
  have hGc : Real.Gamma c ≠ 0 := Real.Gamma_ne_zero hc
  have hGs : Real.Gamma (c - a - b) ≠ 0 := (Real.Gamma_pos_of_pos h).ne'
  have hGca : Real.Gamma (c - a) ≠ 0 := Real.Gamma_ne_zero hca
  have hGcb : Real.Gamma (c - b) ≠ 0 := Real.Gamma_ne_zero hcb
  unfold gaussRatio
  rw [show c + 1 - (a + 1) - b = c - a - b by ring,
    show c + 1 - (a + 1) = c - a by ring,
    show c + 1 - b = (c - b) + 1 by ring,
    Real.Gamma_add_one hc0, Real.Gamma_add_one hcb0]
  field_simp

-- Theorem: `g a (b+1) (c+1) = c/(c-a) · g a b c`.
theorem gaussRatio_shift_b {a b c : ℝ} (h : 0 < c - a - b)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ))
    (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) :
    gaussRatio a (b + 1) (c + 1) = c / (c - a) * gaussRatio a b c := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hca0 : c - a ≠ 0 := by simpa using hca 0
  have hGc : Real.Gamma c ≠ 0 := Real.Gamma_ne_zero hc
  have hGs : Real.Gamma (c - a - b) ≠ 0 := (Real.Gamma_pos_of_pos h).ne'
  have hGca : Real.Gamma (c - a) ≠ 0 := Real.Gamma_ne_zero hca
  have hGcb : Real.Gamma (c - b) ≠ 0 := Real.Gamma_ne_zero hcb
  unfold gaussRatio
  rw [show c + 1 - a - (b + 1) = c - a - b by ring,
    show c + 1 - a = (c - a) + 1 by ring,
    show c + 1 - (b + 1) = c - b by ring,
    Real.Gamma_add_one hc0, Real.Gamma_add_one hca0]
  field_simp

-- Theorem: `D` is unchanged by `(a,b,c) ↦ (a+1,b,c+1)`.
theorem hypD_shift_a {a b c : ℝ} (h : 0 < c - a - b) (ha : a ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ))
    (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) : hypD a b c = hypD (a + 1) b (c + 1) := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hca0 : c - a ≠ 0 := by simpa using hca 0
  have hcb0 : c - b ≠ 0 := by simpa using hcb 0
  have hk : c / (c - b) ≠ 0 := div_ne_zero hc0 hcb0
  unfold hypD
  rw [hyp_one_diag_a h ha hc hca0 hcb0, gaussRatio_shift_a h hc hca hcb,
    mul_div_mul_left (hyp a b c 1) (gaussRatio a b c) hk]

-- Theorem: `D` is unchanged by `(a,b,c) ↦ (a,b+1,c+1)`.
theorem hypD_shift_b {a b c : ℝ} (h : 0 < c - a - b) (hb : b ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ))
    (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) : hypD a b c = hypD a (b + 1) (c + 1) := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hca0 : c - a ≠ 0 := by simpa using hca 0
  have hcb0 : c - b ≠ 0 := by simpa using hcb 0
  have hk : c / (c - a) ≠ 0 := div_ne_zero hc0 hca0
  unfold hypD
  rw [hyp_one_diag_b h hb hc hca0 hcb0, gaussRatio_shift_b h hc hca hcb,
    mul_div_mul_left (hyp a b c 1) (gaussRatio a b c) hk]

-- Theorem: `D (a+m) b (c+m) = D a b c`, provided `a, a+1, …, a+m-1 ≠ 0`.
theorem hypD_shift_a_nat {a b c : ℝ} (h : 0 < c - a - b) (m : ℕ)
    (ha : ∀ j : ℕ, j < m → a + (j : ℝ) ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ))
    (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) : hypD a b c = hypD (a + m) b (c + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ha' : ∀ j : ℕ, j < m → a + (j : ℝ) ≠ 0 :=
      fun j hj => ha j (Nat.lt_trans hj (Nat.lt_succ_self m))
    have ham : a + (m : ℝ) ≠ 0 := ha m (Nat.lt_succ_self m)
    have hcm : ∀ n : ℕ, c + (m : ℝ) ≠ -(n : ℝ) := by
      intro n hcon
      exact hc (n + m) (by push_cast at hcon ⊢; linarith)
    have hcam : ∀ n : ℕ, (c + (m : ℝ)) - (a + (m : ℝ)) ≠ -(n : ℝ) := by
      intro n hcon
      exact hca n (by linarith)
    have hcbm : ∀ n : ℕ, (c + (m : ℝ)) - b ≠ -(n : ℝ) := by
      intro n hcon
      exact hcb (n + m) (by push_cast at hcon ⊢; linarith)
    have hsm : 0 < (c + (m : ℝ)) - (a + (m : ℝ)) - b := by linarith [h]
    calc hypD a b c = hypD (a + (m : ℝ)) b (c + (m : ℝ)) := ih ha'
      _ = hypD (a + (m : ℝ) + 1) b ((c + (m : ℝ)) + 1) :=
          hypD_shift_a hsm ham hcm hcam hcbm
      _ = hypD (a + ((m + 1 : ℕ) : ℝ)) b (c + ((m + 1 : ℕ) : ℝ)) := by
          simp only [Nat.cast_add, Nat.cast_one, add_assoc]

-- Theorem: `D a (b+m) (c+m) = D a b c`, provided `b, b+1, …, b+m-1 ≠ 0`.
theorem hypD_shift_b_nat {a b c : ℝ} (h : 0 < c - a - b) (m : ℕ)
    (hb : ∀ j : ℕ, j < m → b + (j : ℝ) ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ))
    (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) : hypD a b c = hypD a (b + m) (c + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hb' : ∀ j : ℕ, j < m → b + (j : ℝ) ≠ 0 :=
      fun j hj => hb j (Nat.lt_trans hj (Nat.lt_succ_self m))
    have hbm : b + (m : ℝ) ≠ 0 := hb m (Nat.lt_succ_self m)
    have hcm : ∀ n : ℕ, c + (m : ℝ) ≠ -(n : ℝ) := by
      intro n hcon
      exact hc (n + m) (by push_cast at hcon ⊢; linarith)
    have hcam : ∀ n : ℕ, (c + (m : ℝ)) - a ≠ -(n : ℝ) := by
      intro n hcon
      exact hca (n + m) (by push_cast at hcon ⊢; linarith)
    have hcbm : ∀ n : ℕ, (c + (m : ℝ)) - (b + (m : ℝ)) ≠ -(n : ℝ) := by
      intro n hcon
      exact hcb n (by linarith)
    have hsm : 0 < (c + (m : ℝ)) - a - (b + (m : ℝ)) := by linarith [h]
    calc hypD a b c = hypD a (b + (m : ℝ)) (c + (m : ℝ)) := ih hb'
      _ = hypD a (b + (m : ℝ) + 1) ((c + (m : ℝ)) + 1) :=
          hypD_shift_b hsm hbm hcm hcam hcbm
      _ = hypD a (b + ((m + 1 : ℕ) : ℝ)) (c + ((m + 1 : ℕ) : ℝ)) := by
          simp only [Nat.cast_add, Nat.cast_one, add_assoc]

-- Theorem: `D 0 b c = 1`.
theorem hypD_zero_left {b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) : hypD 0 b c = 1 := by
  have hGc : Real.Gamma c ≠ 0 := Real.Gamma_ne_zero hc
  have hGcb : Real.Gamma (c - b) ≠ 0 := Real.Gamma_ne_zero hcb
  unfold hypD gaussRatio
  rw [hyp_zero_left b c 1, show c - 0 - b = c - b by ring, show c - 0 = c by ring]
  field_simp

-- Theorem: `D a 0 c = 1`.
theorem hypD_zero_right {a c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ)) : hypD a 0 c = 1 := by
  have hGc : Real.Gamma c ≠ 0 := Real.Gamma_ne_zero hc
  have hGca : Real.Gamma (c - a) ≠ 0 := Real.Gamma_ne_zero hca
  unfold hypD gaussRatio
  rw [hyp_zero_right a c 1, show c - a - 0 = c - a by ring, show c - 0 = c by ring]
  field_simp

/-! ### The lifted summation theorem

The invariant `D` is unchanged under `(a,b,c) ↦ (a+1,b+1,c+2)` and its value is `1` on the
region covered by `hyp_one_eq_Gamma`. Any admissible triple can either be shifted to a point
with `a = 0` (when `a` is a nonpositive integer, in which case `D = 1` directly) or moved
up to a point with `a, b > 0` where the original theorem applies. -/

-- Theorem: `₂F₁(a,b;c;1) = Γ(c)Γ(c-a-b)/(Γ(c-a)Γ(c-b))` for `c - a - b > 0`.
theorem hyp_one_eq_Gamma' {a b c : ℝ} (h : 0 < c - a - b)
    (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ)) (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ))
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    hyp a b c 1 = Real.Gamma c * Real.Gamma (c - a - b) /
      (Real.Gamma (c - a) * Real.Gamma (c - b)) := by
  have hG := gaussRatio_ne_zero h hc hca hcb
  have hD : hypD a b c = 1 := by
    by_cases ha : ∃ k : ℕ, a = -(k : ℝ)
    · obtain ⟨k, rfl⟩ := ha
      have haj : ∀ j : ℕ, j < k → -(k : ℝ) + (j : ℝ) ≠ 0 := by
        intro j hj hcon
        have hjk : (j : ℝ) < (k : ℝ) := by exact_mod_cast hj
        linarith
      have hck : ∀ n : ℕ, c + (k : ℝ) ≠ -(n : ℝ) := by
        intro n hcon
        exact hc (n + k) (by push_cast at hcon ⊢; linarith)
      have hcbk : ∀ n : ℕ, c + (k : ℝ) - b ≠ -(n : ℝ) := by
        intro n hcon
        exact hcb (n + k) (by push_cast at hcon ⊢; linarith)
      rw [hypD_shift_a_nat h k haj hc hca hcb, show -(k : ℝ) + (k : ℝ) = 0 by ring,
        hypD_zero_left hck hcbk]
    · by_cases hb : ∃ k : ℕ, b = -(k : ℝ)
      · obtain ⟨k, rfl⟩ := hb
        have hbj : ∀ j : ℕ, j < k → -(k : ℝ) + (j : ℝ) ≠ 0 := by
          intro j hj hcon
          have hjk : (j : ℝ) < (k : ℝ) := by exact_mod_cast hj
          linarith
        have hck : ∀ n : ℕ, c + (k : ℝ) ≠ -(n : ℝ) := by
          intro n hcon
          exact hc (n + k) (by push_cast at hcon ⊢; linarith)
        have hcak : ∀ n : ℕ, c + (k : ℝ) - a ≠ -(n : ℝ) := by
          intro n hcon
          exact hca (n + k) (by push_cast at hcon ⊢; linarith)
        rw [hypD_shift_b_nat h k hbj hc hca hcb, show -(k : ℝ) + (k : ℝ) = 0 by ring,
          hypD_zero_right hck hcak]
      · have haj : ∀ j : ℕ, a + (j : ℝ) ≠ 0 := by
          intro j hcon
          exact ha ⟨j, by linarith⟩
        have hbj : ∀ j : ℕ, b + (j : ℝ) ≠ 0 := by
          intro j hcon
          exact hb ⟨j, by linarith⟩
        obtain ⟨m, hm⟩ := exists_nat_gt (max (max (-a) (-b)) (b - c))
        have ham : 0 < a + (m : ℝ) := by
          have h1 : -a ≤ max (-a) (-b) := le_max_left _ _
          have h2 : max (-a) (-b) ≤ max (max (-a) (-b)) (b - c) := le_max_left _ _
          linarith
        have hbm : 0 < b + (m : ℝ) := by
          have h1 : -b ≤ max (-a) (-b) := le_max_right _ _
          have h2 : max (-a) (-b) ≤ max (max (-a) (-b)) (b - c) := le_max_left _ _
          linarith
        have hbmc : b + (m : ℝ) < c + (m : ℝ) + (m : ℝ) := by
          have h1 : b - c ≤ max (max (-a) (-b)) (b - c) := le_max_right _ _
          linarith
        have hcm : ∀ n : ℕ, c + (m : ℝ) ≠ -(n : ℝ) := by
          intro n hcon
          exact hc (n + m) (by push_cast at hcon ⊢; linarith)
        have hcam : ∀ n : ℕ, c + (m : ℝ) - (a + (m : ℝ)) ≠ -(n : ℝ) := by
          intro n hcon
          exact hca n (by linarith)
        have hcbm : ∀ n : ℕ, c + (m : ℝ) - b ≠ -(n : ℝ) := by
          intro n hcon
          exact hcb (n + m) (by push_cast at hcon ⊢; linarith)
        have hsm : 0 < c + (m : ℝ) - (a + (m : ℝ)) - b := by linarith [h]
        have hshift_b := hypD_shift_b_nat (a := a + (m : ℝ)) (b := b) (c := c + (m : ℝ))
          hsm m (fun j _ => hbj j) hcm hcam hcbm
        have hpos : 0 < c + (m : ℝ) + (m : ℝ) - (a + (m : ℝ)) - (b + (m : ℝ)) := by
          linarith [h]
        have hcN : ∀ n : ℕ, c + (m : ℝ) + (m : ℝ) ≠ -(n : ℝ) := by
          intro n hcon
          exact hc (n + m + m) (by push_cast at hcon ⊢; linarith)
        have hcaN : ∀ n : ℕ, c + (m : ℝ) + (m : ℝ) - (a + (m : ℝ)) ≠ -(n : ℝ) := by
          intro n hcon
          exact hca (n + m) (by push_cast at hcon ⊢; linarith)
        have hcbN : ∀ n : ℕ, c + (m : ℝ) + (m : ℝ) - (b + (m : ℝ)) ≠ -(n : ℝ) := by
          intro n hcon
          exact hcb (n + m) (by push_cast at hcon ⊢; linarith)
        have htop : hypD (a + (m : ℝ)) (b + (m : ℝ)) (c + (m : ℝ) + (m : ℝ)) = 1 := by
          unfold hypD
          rw [hyp_one_eq_Gamma ham hbm (by linarith) hpos hcN]
          exact div_self (gaussRatio_ne_zero hpos hcN hcaN hcbN)
        exact (hypD_shift_a_nat h m (fun j _ => haj j) hc hca hcb).trans (hshift_b.trans htop)
  have hFG : hyp a b c 1 = gaussRatio a b c := by
    have h1 := hD
    unfold hypD at h1
    exact (div_eq_one_iff_eq hG).mp h1
  simpa [gaussRatio] using hFG

end

end Pconstructible
