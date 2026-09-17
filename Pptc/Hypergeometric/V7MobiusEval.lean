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

-- Targeted imports: `V7` supplies the Möbius substitution `mobius` and its pullback
-- `mSeries` from `Pptc.Hypergeometric.HeunMobius`; `PowerSeries.Binomial` supplies the
-- negative-binomial coefficients behind `PowerSeries.invOneSubPow`.
import Pptc.Hypergeometric.V7
import Mathlib.RingTheory.PowerSeries.Binomial

/-! # Pptc.Hypergeometric.V7MobiusEval

`mSeries = ∑ₙ bₙ · mobiusⁿ` is the Möbius pullback of `₂F₁(1/2,1/2;1;·)` by
`mobius = 2X/(1+X)`. This file evaluates it as an ordinary power series in the new variable
`w`, on a disc around the origin.

The Möbius substitution is *not* a polynomial, so the re-expansion is an infinite double sum
rather than the finite one used for the quadratic substitution `4X(1-X)` in
`Pptc.Hypergeometric.Quadratic`. Writing `b_n = hypCoeff (1/2)(1/2)1 n` and using

`coeff n (mobius^d) = 2^d (-1)^(n-d) C(n-1, d-1)`   (`d ≤ n`),

the `d`-th row of the double family `F(d,n) = b_d · coeff n (mobius^d) · w^n` sums to
`b_d (2w/(1+w))^d`, so the iterated sum is `₂F₁(1/2,1/2;1;2w/(1+w))`; the `k`-th column sums
to `coeff k mSeries · w^k` by `PowerSeries.coeff_subst'`. `Summable.tsum_prod` and
`HasSum.tsum_fiberwise` turn this into the `HasSum` for the coefficients of `mSeries`.

Summability is controlled by the majorant `∑ₙ |coeff n (mobius^d)| |w|ⁿ = (2|w|/(1-|w|))ᵈ`,
which is finite and summable against `b_d` exactly when `2|w|/(1-|w|) < 1`, i.e. `|w| < 1/3`.
-/

namespace Pconstructible

noncomputable section

open scoped ENNReal

/-! ### The reciprocal `(1+X)^{-d}`

`(1+X)^{-d}` is the image of `(1-X)^{-d}` under `X ↦ -X`; `PowerSeries.invOneSubPow ℝ d` is the
latter, so `rescale (-1) (invOneSubPow ℝ d).val` is the former and its coefficients are the
negative-binomial numbers `(-1)ⁿ C(d+n-1, d-1)`. -/

/-- The image of `1 - X` under `X ↦ -X` is `1 + X`. -/
-- Theorem: `rescale (-1) (1 - X) = 1 + X`.
private theorem rescale_neg_one_one_sub_X :
    PowerSeries.rescale (-1 : ℝ) (1 - PowerSeries.X) = (1 + PowerSeries.X : PowerSeries ℝ) := by
  rw [map_sub, map_one, PowerSeries.rescale_X]
  rw [show PowerSeries.C (-1 : ℝ) = -(1 : PowerSeries ℝ) by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, map_neg, map_one]]
  ring

/-- `(1+X)^{-d}` realized as the rescaled reciprocal of `(1-X)^d`. -/
private noncomputable def recipP (d : ℕ) : PowerSeries ℝ :=
  PowerSeries.rescale (-1) ((PowerSeries.invOneSubPow ℝ d).val)

/-- `recipP d` is a right inverse of `(1+X)^d`. -/
-- Theorem: `recipP d * (1 + X)^d = 1`.
private theorem recipP_mul_pow (d : ℕ) :
    recipP d * (1 + PowerSeries.X : PowerSeries ℝ) ^ d = 1 := by
  have h : (PowerSeries.invOneSubPow ℝ d).val
      * (1 - PowerSeries.X : PowerSeries ℝ) ^ d = 1 := by
    have hu := (PowerSeries.invOneSubPow ℝ d).val_inv
    rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at hu
    simpa using hu
  calc recipP d * (1 + PowerSeries.X : PowerSeries ℝ) ^ d
      = PowerSeries.rescale (-1) ((PowerSeries.invOneSubPow ℝ d).val)
          * (PowerSeries.rescale (-1) (1 - PowerSeries.X)) ^ d := by
            simp only [recipP, rescale_neg_one_one_sub_X]
    _ = PowerSeries.rescale (-1)
          ((PowerSeries.invOneSubPow ℝ d).val * (1 - PowerSeries.X) ^ d) := by
            rw [map_mul, map_pow]
    _ = PowerSeries.rescale (-1) (1 : PowerSeries ℝ) := by rw [h]
    _ = 1 := by rw [map_one]

/-- Coefficients of the reciprocal `(1+X)^{-d}`: `[Xⁿ](1+X)^{-d} = (-1)ⁿ C(d+n-1, d-1)`. -/
-- Theorem: `coeff n (recipP d) = (-1)^n * C(d+n-1, d-1)` for `0 < d`.
private theorem coeff_recipP (d n : ℕ) (hd : 0 < d) :
    PowerSeries.coeff n (recipP d)
      = (-1 : ℝ) ^ n * (Nat.choose (d + n - 1) (d - 1) : ℝ) := by
  rw [recipP, PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℝ d hd]
  simp only [PowerSeries.coeff_mk]
  rw [show d - 1 + n = d + n - 1 by omega]

/-- `(1+X)⁻¹` raised to the `d`-th power is `recipP d`. -/
-- Theorem: `((1 + X)⁻¹)^d = recipP d` for `0 < d`.
private theorem invOnePlusX_pow_eq_recipP {d : ℕ} (hd : 0 < d) :
    ((1 + PowerSeries.X : PowerSeries ℝ)⁻¹) ^ d = recipP d := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have hne : ((1 + PowerSeries.X : PowerSeries ℝ) ^ (e + 1)) ≠ 0 := by
    intro h
    have h1 : PowerSeries.constantCoeff ((1 + PowerSeries.X : PowerSeries ℝ) ^ (e + 1)) = 1 := by
      rw [map_pow]
      simp
    rw [h, map_zero] at h1
    exact one_ne_zero h1.symm
  have hA : recipP (e + 1) * (1 + PowerSeries.X : PowerSeries ℝ) ^ (e + 1) = 1 :=
    recipP_mul_pow (e + 1)
  have hB : ((1 + PowerSeries.X : PowerSeries ℝ)⁻¹) ^ (e + 1)
      * (1 + PowerSeries.X) ^ (e + 1) = 1 := by
    rw [← mul_pow,
      PowerSeries.inv_mul_cancel ((1 + PowerSeries.X : PowerSeries ℝ)) (by simp), one_pow]
  exact (mul_right_cancel₀ hne (hA.trans hB.symm)).symm

/-- `recipP 0 = 1`. -/
-- Theorem: `recipP 0 = 1`.
private theorem recipP_zero : recipP 0 = 1 := by
  simp [recipP, PowerSeries.invOneSubPow_zero]

/-! ### Coefficients of `mobius^d` -/

/-- `mobius^d = (2X)^d (1+X)^{-d}`. -/
-- Theorem: `mobius^d = 2^d * X^d * recipP d`.
private theorem mobius_pow_eq (d : ℕ) :
    mobius ^ d = (2 : PowerSeries ℝ) ^ d * PowerSeries.X ^ d * recipP d := by
  rcases d with _ | e
  · rw [pow_zero, recipP_zero]
    ring
  · rw [mobius, mul_pow, mul_pow, invOnePlusX_pow_eq_recipP (Nat.succ_pos e)]

/-- The coefficients of `mobius^d`: `[Xⁿ](mobius^d) = 2ᵈ (-1)^(n-d) C(n-1, d-1)` for
`0 < d ≤ n`. -/
-- Theorem: for `0 < d ≤ n`, `coeff n (mobius^d) = 2^d (-1)^(n-d) C(n-1, d-1)`.
private theorem coeff_mobius_pow_of_pos {d n : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    PowerSeries.coeff n (mobius ^ d)
      = 2 ^ d * (-1 : ℝ) ^ (n - d) * (Nat.choose (n - 1) (d - 1) : ℝ) := by
  rw [mobius_pow_eq,
    show (2 : PowerSeries ℝ) ^ d * PowerSeries.X ^ d * recipP d
        = PowerSeries.C ((2 : ℝ) ^ d) * (PowerSeries.X ^ d * recipP d) by
      rw [map_pow, show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl]
      ring,
    PowerSeries.coeff_C_mul]
  have hcoeff : PowerSeries.coeff n (PowerSeries.X ^ d * recipP d)
      = PowerSeries.coeff (n - d) (recipP d) := by
    have h := PowerSeries.coeff_X_pow_mul (recipP d) d (n - d)
    rwa [show (n - d) + d = n by omega] at h
  rw [hcoeff, coeff_recipP d (n - d) hd,
    show d + (n - d) - 1 = n - 1 by omega]
  ring

/-- `mobius^d` has order at least `d`, so its coefficients below `d` vanish. -/
-- Theorem: if `n < d` then `coeff n (mobius^d) = 0`.
private theorem coeff_mobius_pow_eq_zero_of_lt {d n : ℕ} (h : n < d) :
    PowerSeries.coeff n (mobius ^ d) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  have hconst : PowerSeries.constantCoeff mobius = 0 := by
    rw [mobius]
    simp
  have hle : d ≤ (mobius ^ d).order :=
    PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hconst
  exact lt_of_lt_of_le (by exact_mod_cast h) hle

/-! ### The negative-binomial series

`∑ⱼ C(d+j-1, d-1) xʲ = (1-x)^{-d}` is the analytic content of the row sums. -/

/-- The negative-binomial series in `x`, valid for `|x| < 1`:
`∑ⱼ C(d+j-1, d-1) xʲ = (1-x)^{-d}`. -/
-- Theorem: `HasSum (fun j => C(d+j-1, d-1) * x^j) ((1-x)^d)⁻¹` for `|x| < 1`, `0 < d`.
private theorem hasSum_negBinom (d : ℕ) (hd : 0 < d) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun j : ℕ => (Nat.choose (d + j - 1) (d - 1) : ℝ) * x ^ j)
      (1 / (1 - x) ^ d) := by
  have hz1 : (‖x‖ₑ : ℝ≥0∞) < 1 := by
    rw [enorm_eq_nnnorm]
    simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact hx
  have hmem : x ∈ Metric.eball (0 : ℝ) 1 := mem_eball_zero_iff.2 hz1
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero
    (a := (d : ℝ))).hasSum hmem
  rw [FormalMultilinearSeries.ofScalars_apply_eq'] at h
  have hterm : ∀ j : ℕ, (Nat.choose (d + j - 1) (d - 1) : ℝ) * x ^ j
      = Ring.choose ((d : ℝ) + j - 1) j • x ^ j := by
    intro j
    rw [smul_eq_mul]
    congr 1
    have hcast : (d : ℝ) + j - 1 = ((d + j - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ d + j), Nat.cast_add, Nat.cast_one]
    rw [hcast, Ring.choose_natCast]
    have hsym : Nat.choose (d + j - 1) j = Nat.choose (d + j - 1) (d - 1) := by
      rw [← Nat.choose_symm (show d - 1 ≤ d + j - 1 by omega)]
      congr 1
      omega
    exact_mod_cast hsym.symm
  have h' := h.congr_fun hterm
  rw [Real.rpow_natCast] at h'
  simpa only [zero_add] using h'

/-- The absolute majorant of the `d`-th row: `∑ₙ |[Xⁿ](mobius^d)| |w|ⁿ = (2|w|/(1-|w|))ᵈ`. -/
-- Theorem: `HasSum (fun n => ‖coeff n (mobius^d)‖ * |w|^n) ((2|w|/(1-|w|))^d)`.
private theorem hasSum_abs_coeff_mobius_pow (d : ℕ) (w : ℝ) (hw : |w| < 1) :
    HasSum (fun n : ℕ => ‖PowerSeries.coeff n (mobius ^ d)‖ * |w| ^ n)
      ((2 * |w| / (1 - |w|)) ^ d) := by
  rcases d with _ | e
  · have hfun : (fun n : ℕ => ‖PowerSeries.coeff n (mobius ^ 0)‖ * |w| ^ n)
        = fun n : ℕ => if n = 0 then (1 : ℝ) else 0 := by
      funext n
      rw [pow_zero, PowerSeries.coeff_one]
      rcases n with _ | n <;> simp
    rw [hfun]
    simpa using hasSum_single (f := fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 0
      (fun b hb => by simp [hb])
  · have hbase := hasSum_negBinom (e + 1) (Nat.succ_pos e) (x := |w|) (by simpa using hw)
    have hmul := hbase.mul_left ((2 * |w|) ^ (e + 1))
    have hval : (2 * |w|) ^ (e + 1) * (1 / (1 - |w|) ^ (e + 1))
        = (2 * |w| / (1 - |w|)) ^ (e + 1) := by
      simp only [div_eq_mul_inv, one_mul, mul_pow, inv_pow]
    rw [hval] at hmul
    have hnorm : ∀ j : ℕ, ‖(2 : ℝ) ^ (e + 1) * (-1 : ℝ) ^ j
          * (Nat.choose ((e + 1) + j - 1) ((e + 1) - 1) : ℝ)‖
        = (2 : ℝ) ^ (e + 1) * (Nat.choose ((e + 1) + j - 1) ((e + 1) - 1) : ℝ) := by
      intro j
      have hC : (0 : ℝ) ≤ (Nat.choose ((e + 1) + j - 1) ((e + 1) - 1) : ℝ) :=
        Nat.cast_nonneg _
      rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
        Real.norm_of_nonneg hC, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hshift : HasSum (fun j : ℕ => ‖PowerSeries.coeff (j + (e + 1)) (mobius ^ (e + 1))‖
        * |w| ^ (j + (e + 1))) ((2 * |w| / (1 - |w|)) ^ (e + 1)) := by
      refine hmul.congr_fun fun j => ?_
      rw [coeff_mobius_pow_of_pos (d := e + 1) (n := j + (e + 1))
          (Nat.succ_pos e) (by omega),
        show j + (e + 1) - (e + 1) = j by omega,
        show j + (e + 1) - 1 = (e + 1) + j - 1 by omega,
        hnorm j, pow_add, mul_pow]
      ring
    have hzero : (∑ i ∈ Finset.range (e + 1),
        ‖PowerSeries.coeff i (mobius ^ (e + 1))‖ * |w| ^ i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rw [coeff_mobius_pow_eq_zero_of_lt (by omega)]
      simp
    have := (hasSum_nat_add_iff
      (f := fun n : ℕ => ‖PowerSeries.coeff n (mobius ^ (e + 1))‖ * |w| ^ n) (e + 1)).mp hshift
    rwa [hzero, add_zero] at this

/-- The signed row sum: `∑ₙ [Xⁿ](mobius^d) wⁿ = (2w/(1+w))ᵈ`. -/
-- Theorem: `HasSum (fun n => coeff n (mobius^d) * w^n) ((2w/(1+w))^d)`.
private theorem hasSum_coeff_mobius_pow (d : ℕ) (w : ℝ) (hw : |w| < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (mobius ^ d) * w ^ n)
      ((2 * w / (1 + w)) ^ d) := by
  rcases d with _ | e
  · have hfun : (fun n : ℕ => PowerSeries.coeff n (mobius ^ 0) * w ^ n)
        = fun n : ℕ => if n = 0 then (1 : ℝ) else 0 := by
      funext n
      rw [pow_zero, PowerSeries.coeff_one]
      rcases n with _ | n <;> simp
    rw [hfun]
    simpa using hasSum_single (f := fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 0
      (fun b hb => by simp [hb])
  · have hbase := hasSum_negBinom (e + 1) (Nat.succ_pos e) (x := -w) (by simpa using hw)
    have hmul := hbase.mul_left ((2 * w) ^ (e + 1))
    have hval : (2 * w) ^ (e + 1) * (1 / (1 - -w) ^ (e + 1))
        = (2 * w / (1 + w)) ^ (e + 1) := by
      rw [show (1 : ℝ) - -w = 1 + w by ring]
      simp only [div_eq_mul_inv, one_mul, mul_pow, inv_pow]
    rw [hval] at hmul
    have hshift : HasSum (fun j : ℕ => PowerSeries.coeff (j + (e + 1)) (mobius ^ (e + 1))
        * w ^ (j + (e + 1))) ((2 * w / (1 + w)) ^ (e + 1)) := by
      refine hmul.congr_fun fun j => ?_
      rw [coeff_mobius_pow_of_pos (d := e + 1) (n := j + (e + 1))
          (Nat.succ_pos e) (by omega),
        show j + (e + 1) - (e + 1) = j by omega,
        show j + (e + 1) - 1 = (e + 1) + j - 1 by omega,
        show (-w : ℝ) = (-1) * w by ring, mul_pow, mul_pow, pow_add]
      ring
    have hzero : (∑ i ∈ Finset.range (e + 1),
        PowerSeries.coeff i (mobius ^ (e + 1)) * w ^ i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rw [coeff_mobius_pow_eq_zero_of_lt (by omega)]
      simp
    have := (hasSum_nat_add_iff
      (f := fun n : ℕ => PowerSeries.coeff n (mobius ^ (e + 1)) * w ^ n) (e + 1)).mp hshift
    rwa [hzero, add_zero] at this

/-! ### The fibre coefficients of `mSeries` -/

/-- The `k`-th coefficient of `mSeries` is the `d`-sum of `b_d · [Xᵏ](mobius^d)`. The sum is
finite because `mobius^d` has order `d`, so `[Xᵏ](mobius^d) = 0` for `d > k`. -/
-- Theorem: `coeff k mSeries = ∑' d, hypCoeff (1/2)(1/2)1 d * coeff k (mobius^d)`.
private theorem coeff_mSeries (k : ℕ) :
    PowerSeries.coeff k mSeries
      = ∑' d : ℕ,
          hypCoeff (1 / 2) (1 / 2) 1 d * PowerSeries.coeff k (mobius ^ d) := by
  have hsupp : ∀ d ∉ Finset.range (k + 1),
      hypCoeff (1 / 2) (1 / 2) 1 d * PowerSeries.coeff k (mobius ^ d) = 0 := by
    intro d hd
    rw [Finset.mem_range, not_lt] at hd
    rw [coeff_mobius_pow_eq_zero_of_lt (by omega), mul_zero]
  have hsupp' : Function.support (fun d : ℕ =>
      hypCoeff (1 / 2) (1 / 2) 1 d • PowerSeries.coeff k (mobius ^ d))
      ⊆ ↑(Finset.range (k + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    by_contra hcon
    exact hd (by rw [smul_eq_mul]; exact hsupp d hcon)
  have hsub := PowerSeries.coeff_subst' hasSubst_mobius (hypSeries (1 / 2) (1 / 2) 1) k
  simp only [coeff_hypSeries] at hsub
  rw [mSeries]
  rw [show PowerSeries.subst mobius (hypSeries (1 / 2) (1 / 2) 1)
      = (hypSeries (1 / 2) (1 / 2) 1).subst mobius from rfl,
    hsub, finsum_eq_sum_of_support_subset _ hsupp',
    tsum_eq_sum (s := Finset.range (k + 1)) hsupp]
  simp only [smul_eq_mul]

/-! ### The double family and its summability -/

/-- The double family of the re-expansion: its `(d,n)` term is `b_d · [Xⁿ](mobius^d) · wⁿ`. -/
private def mobiusFamily (w : ℝ) : ℕ × ℕ → ℝ := fun p =>
  hypCoeff (1 / 2) (1 / 2) 1 p.1 * PowerSeries.coeff p.2 (mobius ^ p.1) * w ^ p.2

/-- The double family is summable on the disc `2|w|/(1-|w|) < 1`. Every row is absolutely
summable with total `‖b_d‖ (2|w|/(1-|w|))ᵈ`, and those row totals are summable by
`hasSum_hyp`. -/
-- Theorem: `mobiusFamily w` is summable when `2|w|/(1-|w|) < 1`.
private theorem summable_mobiusFamily {w : ℝ} (hw : |w| < 1 / 3) :
    Summable (mobiusFamily w) := by
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw1 : |w| < 1 := by linarith [abs_nonneg w, hw]
  have hBnn : 0 ≤ 2 * |w| / (1 - |w|) :=
    div_nonneg (by positivity) (by linarith [abs_nonneg w])
  have hB : |2 * |w| / (1 - |w|)| < 1 := by
    rw [abs_of_nonneg hBnn, div_lt_one (by linarith [abs_nonneg w])]
    linarith [abs_nonneg w, hw]
  apply Summable.of_norm
  rw [summable_prod_of_nonneg (f := fun p : ℕ × ℕ => ‖mobiusFamily w p‖)
    (fun p => norm_nonneg _)]
  constructor
  · intro d
    have key : Summable (fun n : ℕ => ‖hypCoeff (1 / 2) (1 / 2) 1 d‖
        * (‖PowerSeries.coeff n (mobius ^ d)‖ * |w| ^ n)) :=
      ((hasSum_abs_coeff_mobius_pow d w hw1).mul_left
        ‖hypCoeff (1 / 2) (1 / 2) 1 d‖).summable
    refine key.congr fun n => ?_
    simp only [mobiusFamily, norm_mul, norm_pow, Real.norm_eq_abs]
    ring
  · have hsum : ∀ d : ℕ, (∑' n : ℕ, ‖mobiusFamily w (d, n)‖)
        = ‖hypCoeff (1 / 2) (1 / 2) 1 d‖ * (2 * |w| / (1 - |w|)) ^ d := by
      intro d
      rw [show (fun n : ℕ => ‖mobiusFamily w (d, n)‖)
            = fun n : ℕ => ‖hypCoeff (1 / 2) (1 / 2) 1 d‖
              * (‖PowerSeries.coeff n (mobius ^ d)‖ * |w| ^ n) by
          funext n
          simp only [mobiusFamily, norm_mul, norm_pow, Real.norm_eq_abs]
          ring,
        tsum_mul_left, (hasSum_abs_coeff_mobius_pow d w hw1).tsum_eq]
    simp_rw [hsum]
    refine ((hasSum_hyp (a := (1 : ℝ) / 2) (b := (1 : ℝ) / 2) (c := (1 : ℝ))
      (z := 2 * |w| / (1 - |w|)) hB hc).summable.abs).congr fun d => ?_
    calc ‖hypCoeff (1 / 2) (1 / 2) 1 d * (2 * |w| / (1 - |w|)) ^ d‖
        = ‖hypCoeff (1 / 2) (1 / 2) 1 d‖ * ‖(2 * |w| / (1 - |w|)) ^ d‖ := norm_mul _ _
      _ = ‖hypCoeff (1 / 2) (1 / 2) 1 d‖ * ‖2 * |w| / (1 - |w|)‖ ^ d := by rw [norm_pow]
      _ = ‖hypCoeff (1 / 2) (1 / 2) 1 d‖ * (2 * |w| / (1 - |w|)) ^ d := by
            rw [Real.norm_of_nonneg hBnn]

/-- For `|w| < 1/3` the Möbius-substituted series evaluates to `₂F₁(1/2,1/2;1;2w/(1+w))`. -/
-- Theorem: for `|w| < 1/3`, `HasSum (fun k => coeff k mSeries * w^k)
--   (hyp (1/2) (1/2) 1 (2*w/(1+w)))`.
theorem hasSum_mSeries {w : ℝ} (hw : |w| < 1 / 3) :
    HasSum (fun k : ℕ => PowerSeries.coeff k mSeries * w ^ k)
      (hyp (1 / 2) (1 / 2) 1 (2 * w / (1 + w))) := by
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw1 : |w| < 1 := by linarith [abs_nonneg w, hw]
  have h1w : 0 < 1 + w := by linarith [neg_abs_le w, abs_nonneg w, hw]
  have hz' : |2 * w / (1 + w)| < 1 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos h1w,
      div_lt_one h1w]
    linarith [abs_nonneg w, neg_abs_le w, hw]
  have hg : Summable (mobiusFamily w) := summable_mobiusFamily hw
  have hrow : ∀ d : ℕ, (∑' n : ℕ, mobiusFamily w (d, n))
      = hypCoeff (1 / 2) (1 / 2) 1 d * (2 * w / (1 + w)) ^ d := by
    intro d
    have h := (hasSum_coeff_mobius_pow d w hw1).mul_left (hypCoeff (1 / 2) (1 / 2) 1 d)
    rw [show (∑' n : ℕ, mobiusFamily w (d, n))
          = ∑' n : ℕ, hypCoeff (1 / 2) (1 / 2) 1 d
              * (PowerSeries.coeff n (mobius ^ d) * w ^ n) from
        tsum_congr fun n => by simp only [mobiusFamily]; ring]
    rw [h.tsum_eq]
  have hcol : ∀ k : ℕ, (∑' d : ℕ, mobiusFamily w (d, k))
      = PowerSeries.coeff k mSeries * w ^ k := by
    intro k
    rw [show (fun d : ℕ => mobiusFamily w (d, k))
          = fun d : ℕ => (hypCoeff (1 / 2) (1 / 2) 1 d
              * PowerSeries.coeff k (mobius ^ d)) * w ^ k by
        funext d; simp only [mobiusFamily]]
    rw [tsum_mul_right, ← coeff_mSeries k]
  have hfiber : ∀ k : ℕ, (∑' p : {p : ℕ × ℕ // p.2 = k}, mobiusFamily w p.val)
      = ∑' d : ℕ, mobiusFamily w (d, k) := by
    intro k
    let e : ℕ ≃ {p : ℕ × ℕ // p.2 = k} :=
      { toFun := fun d => ⟨(d, k), rfl⟩
        invFun := fun p => p.val.1
        left_inv := fun d => rfl
        right_inv := fun p => by
          obtain ⟨⟨a, b⟩, hb⟩ := p
          change b = k at hb
          subst hb
          rfl }
    rw [← Equiv.tsum_eq e (fun p : {p : ℕ × ℕ // p.2 = k} => mobiusFamily w p.val)]
    exact tsum_congr fun d => rfl
  have ha : (∑' p : ℕ × ℕ, mobiusFamily w p)
      = hyp (1 / 2) (1 / 2) 1 (2 * w / (1 + w)) := by
    rw [hg.tsum_prod]
    rw [show (fun d : ℕ => ∑' n : ℕ, mobiusFamily w (d, n))
          = fun d : ℕ => hypCoeff (1 / 2) (1 / 2) 1 d * (2 * w / (1 + w)) ^ d by
        funext d; exact hrow d]
    exact (hasSum_hyp (a := (1 : ℝ) / 2) (b := (1 : ℝ) / 2) (c := (1 : ℝ))
      hz' hc).tsum_eq
  have hfib := hg.hasSum.tsum_fiberwise (Prod.snd : ℕ × ℕ → ℕ)
  rw [ha] at hfib
  exact hfib.congr_fun fun k => by
    change PowerSeries.coeff k mSeries * w ^ k
      = ∑' (p : {p : ℕ × ℕ // p.2 = k}), mobiusFamily w p.val
    rw [hfiber k, hcol k]

end

end Pconstructible
