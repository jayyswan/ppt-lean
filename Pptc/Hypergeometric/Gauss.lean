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
import Pptc.Gamma
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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

open scoped Topology ENNReal

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

end

end Pconstructible
