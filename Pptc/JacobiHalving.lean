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

import Pptc.JacobiAddition

/-! # Pptc.JacobiHalving

The amplitude can be halved. Write `s = sn²(u/2)`. The duplication case of the addition
theorem for `cn` (`jacobiCn_add` at `v = w = u/2`), with `cn² = 1 - s` and `dn² = 1 - c s`,
reads

  `cn u · (1 - c s²) = 1 - 2 s + c s²`,

that is, `s` is a root of the quadratic `c (1 + cn u) s² - 2 s + (1 - cn u)`. Its linear
coefficient is `-2`, so the quadratic never vanishes identically, and its root `s` is
P-constructible as soon as `cn u` is. Then `sn(u/2) = ±√s`, and `sn` determines `am`.
(Explicitly, `sn²(u/2) = (1 - cn u)/(1 + dn u)`, but nothing below needs the closed form.)

Combined with `jacobiAm_Pconstructible_add`, this gives the following: the set of arguments
at which `am` is P-constructible is a `ℤ[1/2]`-module. It contains `F(φ)` for every
P-constructible `φ` (`jacobiAm_ellipticF_Pconstructible`), and in particular the complete
integral `K = F(π/2)`. -/

namespace Pconstructible

-- Lemma: for `c < 1` and `0 ≤ s ≤ 1`, the duplication denominator `1 - c s²` is positive.
private theorem one_sub_mul_sq_pos {c s : ℝ} (hc : c < 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < 1 - c * s ^ 2 := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  rcases le_total c 0 with h | h
  · nlinarith [sq_nonneg s]
  · nlinarith [mul_le_mul_of_nonneg_left hs2 h]

-- Theorem: the amplitude at `u / 2` is P-constructible whenever it is at `u`.
theorem jacobiAm_Pconstructible_half {c u : ℝ} (hcP : PConstructible c) (hc : c < 1)
    (hu : PConstructible (jacobiAm c u)) : PConstructible (jacobiAm c (u / 2)) := by
  set v := u / 2 with hv
  have huv : v + v = u := by rw [hv]; ring
  have hcu : PConstructible (jacobiCn c u) := jacobiCn_Pconstructible_of_am hu
  set s := jacobiSn c v ^ 2 with hs
  have hpy := jacobiSn_sq_add_jacobiCn_sq c v
  have hdn := jacobiDn_sq hc v
  have hs0 : 0 ≤ s := sq_nonneg _
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg (jacobiCn c v)]
  have hden := one_sub_mul_sq_pos hc hs0 hs1
  have hadd := jacobiCn_add hc v v
  rw [huv] at hadd
  have hden' : 1 - c * jacobiSn c v ^ 2 * jacobiSn c v ^ 2 = 1 - c * s ^ 2 := by
    rw [hs]; ring
  rw [hden'] at hadd
  have hlin : jacobiCn c u * (1 - c * s ^ 2) = 1 - 2 * s + c * s ^ 2 := by
    rw [hadd, div_mul_cancel₀ _ hden.ne']
    have hnum : jacobiCn c v * jacobiCn c v - jacobiSn c v * jacobiSn c v * jacobiDn c v
        * jacobiDn c v = jacobiCn c v ^ 2 - s * jacobiDn c v ^ 2 := by rw [hs]; ring
    rw [hnum, hdn, ← hs]
    linear_combination hpy
  have hq : cubicVal (1 - jacobiCn c u) (-2) (c * (1 + jacobiCn c u)) 0 s = 0 := by
    simp only [cubicVal]
    linear_combination (-1 : ℝ) * hlin
  have hsP : PConstructible s :=
    cubicVal_root_Pconstructible (by pconstructible) (by pconstructible) (by pconstructible)
      zero_Pconstructible (Or.inr (Or.inr (Or.inl (by norm_num)))) hq
  rw [jacobiAm_Pconstructible_iff_sn]
  have habs : |jacobiSn c v| = Real.sqrt s := by rw [hs, Real.sqrt_sq_eq_abs]
  rcases abs_choice (jacobiSn c v) with h | h
  · rw [← h, habs]
    exact sqrt_Pconstructible hsP
  · rw [show jacobiSn c v = -|jacobiSn c v| by rw [h]; ring, habs]
    exact neg_Pconstructible (sqrt_Pconstructible hsP)

-- Theorem: the amplitude at `u / 2 ^ n` is P-constructible whenever it is at `u`.
theorem jacobiAm_Pconstructible_div_two_pow {c u : ℝ} (hcP : PConstructible c) (hc : c < 1)
    (hu : PConstructible (jacobiAm c u)) (n : ℕ) :
    PConstructible (jacobiAm c (u / 2 ^ n)) := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
      have h := jacobiAm_Pconstructible_half hcP hc ih
      rwa [div_div, ← pow_succ] at h

-- Theorem: the amplitude is P-constructible at every dyadic multiple `(m / 2 ^ n) F(φ)` of a
-- first-kind integral with P-constructible amplitude `φ`; for `φ = π/2` these are the dyadic
-- multiples of the complete integral `K`.
theorem jacobiAm_dyadic_ellipticF_Pconstructible {c φ : ℝ} (hcP : PConstructible c)
    (hc : c < 1) (hφ : PConstructible φ) (m : ℤ) (n : ℕ) :
    PConstructible (jacobiAm c (m * ellipticF c φ / 2 ^ n)) := by
  refine jacobiAm_Pconstructible_div_two_pow hcP hc ?_ n
  have h0 := jacobiAm_ellipticF_Pconstructible (c := c) hφ hc
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · exact_mod_cast jacobiAm_Pconstructible_nsmul hcP hc h0 k
  · rw [Int.cast_neg, neg_mul, jacobiAm_neg hc]
    exact neg_Pconstructible (by exact_mod_cast jacobiAm_Pconstructible_nsmul hcP hc h0 k)

/-! ### The amplitude is exactly as hard as Jacobi's epsilon function

Jacobi's epsilon function is `ℰ(u) = E(am u)`. The ellipse inverts `E` exactly
(`ellipticEAm_Pconstructible`), so `am u = E⁻¹(ℰ(u))`: constructing the amplitude is the same
problem as constructing `ℰ(u)`. Every inversion the drawing operations offer pins down a
combination `α F + β E + R` at the unknown point, with `β` and the algebraic or elementary
remainder `R` never both zero. So evaluating such a combination at `am u` always needs `ℰ(u)`
(or `R(am u)`) first; making curve parameters depend on `u` does not remove this. -/

-- Theorem: the amplitude `am u` is P-constructible exactly when Jacobi's epsilon
-- `ℰ(u) = E(am u)` is.
theorem jacobiAm_Pconstructible_iff_epsilon {c u : ℝ} (hcP : PConstructible c) (hc : c < 1) :
    PConstructible (jacobiAm c u) ↔ PConstructible (ellipticE c (jacobiAm c u)) :=
  ⟨fun h => ellipticE_Pconstructible hcP h hc, fun h => by
    rw [← ellipticEAm_ellipticE hc (jacobiAm c u)]
    exact ellipticEAm_Pconstructible hcP h hc⟩

end Pconstructible
