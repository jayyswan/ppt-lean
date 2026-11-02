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
-- `Gauss` supplies the summability `summable_hypCoeff_one`; `Binomial` the
-- Pochhammer form of the Chu-Vandermonde identity.
import Pptc.Hypergeometric.Gauss
import Mathlib.RingTheory.Binomial
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Pptc.Hypergeometric.Pfaff

Pfaff's transformation

`₂F₁(a, b; c; z) = (1 - z)^(-a) ₂F₁(a, c - b; c; z / (z - 1))` for `z ∈ (-1, 1/2)`,

together with the continuity of `z ↦ ₂F₁(A, B; C; z)` at `z = -1` from the right and the
`HasSum` representation of the boundary value, valid when `0 < C - A - B` and `C` is not a
nonpositive integer. Both statements are infrastructure for the Kummer and Bailey
evaluations of phase 5.

## Why the coefficient route works

Write `w = z / (z - 1)`. Then `w = -z (1 - z)⁻¹`, so `w^n = (-1)^n z^n (1 - z)^{-n}`, and
expanding `(1 - z)^{-a-n}` binomially turns the right-hand side into the double series

`∑_{n,k} ₂F₁-coefficient(a, c-b; c; n) · (-1)^n · (a + n)_k / k! · z^{n+k}`.

It is absolutely summable for `|z| < 1/2`: the inner `k`-sum is bounded by
`(1 - |z|)^{-|a|-n}` because `|(a + n)_k| ≤ (|a| + n)_k` once the exponent is
nonnegative, and `∑ₙ |₂F₁-coefficient(a, c-b; c; n)| ρⁿ` converges for every `ρ < 1` by
the convergence of the hypergeometric series at `ρ`. Summing by fibres `n + k = N` gives

`z^N (a)_N / N! · ∑_{k≤N} C(N,k) (-1)^k (c-b)_k / (c)_k`,

so the Chu-Vandermonde identity `∑ₖ C(N,k) (-1)^k (c-b)_k / (c)_k = (b)_N / (c)_N`
(read off from Mathlib's `descPochhammer_smeval_add`) identifies the coefficients of the
right-hand side with `₂F₁-coefficient(a, b; c; N)`. Hence Pfaff holds on `|z| < 1/2`, and
both sides are analytic on the larger interval `(-1, 1/2)` (where `|z| < 1` and
`|z/(z-1)| < 1`), so the identity theorem extends it there.

## Continuity at `-1`

When `0 < C - A - B` the coefficients `₂F₁-coefficient(A, B; C; ·)` are summable
(`summable_hypCoeff_one`), so the Weierstrass M-test makes the series converge uniformly on
`[-1, 1]`. Its sum is `hyp` inside the disc, hence its boundary value at `-1` is the
expected absolutely convergent series. -/

open scoped Topology ENNReal BigOperators

namespace Pconstructible

noncomputable section

open Polynomial

/-! ### Chu-Vandermonde

The coefficient identity behind Pfaff's transformation. Mathlib's
`descPochhammer_smeval_add` is the Chu-Vandermonde identity for descending Pochhammers;
the two rewriting lemmas below put it in the ascending form that the hypergeometric
coefficients use. -/

/-- The descending Pochhammer `(b-c)_k` in terms of the ascending one: it equals
`(-1)^k (c-b)_k`. -/
theorem descPochhammer_smeval_sub_eq (b c : ℝ) (k : ℕ) :
    (descPochhammer ℤ k).smeval (b - c) = (-1) ^ k * (ascPochhammer ℝ k).eval (c - b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, pow_succ]
    simp only [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, ih, ascPochhammer_succ_eval]
    ring

/-- Chu-Vandermonde in the form needed for Pfaff's transformation:
`∑ₖ C(n,k) (-1)^k (c-b)_k / (c)_k = (b)_n / (c)_n`, where `(x)_k` is the ascending
Pochhammer symbol. -/
theorem sum_choose_neg_one_mul_pochhammer_div (b c : ℝ) (n : ℕ)
    (hc : ∀ k : ℕ, (ascPochhammer ℝ k).eval c ≠ 0) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * (-1) ^ k *
          ((ascPochhammer ℝ k).eval (c - b) / (ascPochhammer ℝ k).eval c)
      = (ascPochhammer ℝ n).eval b / (ascPochhammer ℝ n).eval c := by
  have hkey := Ring.descPochhammer_smeval_add (R := ℝ) (r := b - c)
    (s := c + (n : ℝ) - 1) n (Commute.all _ _)
  rw [show b - c + (c + (n : ℝ) - 1) = b + (n : ℝ) - 1 by ring] at hkey
  have hleft : (descPochhammer ℤ n).smeval (b + (n : ℝ) - 1)
      = (ascPochhammer ℝ n).eval b := by
    rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval]
    congr 1
    ring
  have hterm : ∀ ij ∈ Finset.antidiagonal n,
      (n.choose ij.1 : ℝ) * ((descPochhammer ℤ ij.1).smeval (b - c) *
          (descPochhammer ℤ ij.2).smeval (c + (n : ℝ) - 1))
        = (n.choose ij.1 : ℝ) * (-1) ^ ij.1 *
            ((ascPochhammer ℝ ij.1).eval (c - b) *
              (ascPochhammer ℝ ij.2).eval (c + (ij.1 : ℝ))) := by
    intro ij hij
    have hsum : ij.1 + ij.2 = n := by
      simpa using Finset.mem_antidiagonal.mp hij
    have hsecond : (descPochhammer ℤ ij.2).smeval (c + (n : ℝ) - 1)
        = (ascPochhammer ℝ ij.2).eval (c + (ij.1 : ℝ)) := by
      rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
        Polynomial.ascPochhammer_smeval_eq_eval]
      congr 1
      have hcast : (n : ℝ) = (ij.1 : ℝ) + (ij.2 : ℝ) := by
        rw [← hsum]
        push_cast
        ring
      rw [hcast]
      ring
    rw [descPochhammer_smeval_sub_eq, hsecond]
    ring
  have hanti : (∑ ij ∈ Finset.antidiagonal n,
      (n.choose ij.1 : ℝ) * ((descPochhammer ℤ ij.1).smeval (b - c) *
          (descPochhammer ℤ ij.2).smeval (c + (n : ℝ) - 1)))
      = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * (-1) ^ k *
            ((ascPochhammer ℝ k).eval (c - b) *
              (ascPochhammer ℝ (n - k)).eval (c + (k : ℝ))) := by
    refine (Finset.sum_congr rfl hterm).trans ?_
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j =>
      (n.choose i : ℝ) * (-1) ^ i * ((ascPochhammer ℝ i).eval (c - b) *
        (ascPochhammer ℝ j).eval (c + (i : ℝ)))) n
  have hker : (∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * (-1) ^ k *
        ((ascPochhammer ℝ k).eval (c - b) *
          (ascPochhammer ℝ (n - k)).eval (c + (k : ℝ))))
      = (ascPochhammer ℝ n).eval b := by
    rw [← hanti, ← hkey, hleft]
  have hprod : ∀ k ≤ n, (ascPochhammer ℝ n).eval c
      = (ascPochhammer ℝ k).eval c * (ascPochhammer ℝ (n - k)).eval (c + (k : ℝ)) := by
    intro k hk
    have hmul := ascPochhammer_mul (S := ℝ) k (n - k)
    have h := congrArg (fun p : Polynomial ℝ => p.eval c) hmul
    simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_natCast] at h
    rw [show k + (n - k) = n by omega] at h
    exact h.symm
  have hterm2 : ∀ k ∈ Finset.range (n + 1),
      (ascPochhammer ℝ n).eval c *
        ((n.choose k : ℝ) * (-1) ^ k *
          ((ascPochhammer ℝ k).eval (c - b) / (ascPochhammer ℝ k).eval c))
      = (n.choose k : ℝ) * (-1) ^ k *
          ((ascPochhammer ℝ k).eval (c - b) *
            (ascPochhammer ℝ (n - k)).eval (c + (k : ℝ))) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [hprod k hk']
    field_simp [hc k]
  have hmul : (ascPochhammer ℝ n).eval c *
      (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * (-1) ^ k *
          ((ascPochhammer ℝ k).eval (c - b) / (ascPochhammer ℝ k).eval c))
      = (ascPochhammer ℝ n).eval b := by
    rw [Finset.mul_sum]
    exact (Finset.sum_congr rfl hterm2).trans hker
  rw [eq_div_iff (hc n), mul_comm]
  exact hmul

/-! ### The double series of the Pfaff re-expansion

The right-hand side of Pfaff's transformation is
`(1 - z)^(-a) ₂F₁(a, c-b; c; z/(z-1))`. Since `z/(z-1) = -z(1-z)⁻¹`, expanding
`(1-z)^(-a-n)` binomially turns it into a double series in the two indices `n` (the
hypergeometric coefficient) and `k` (the binomial coefficient). This section shows that
the double series is absolutely summable on `|z| < 1/2` and computes both its row sums
and its fibre sums. -/

/-- The ascending Pochhammer symbol is nonnegative at a nonnegative argument. -/
theorem ascPochhammer_eval_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ (ascPochhammer ℝ k).eval x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval]
    exact mul_nonneg ih (by positivity)

/-- Comparing the ascending Pochhammer symbol at `a + n` and at `|a| + n`. -/
theorem abs_eval_ascPochhammer_add_le (a : ℝ) (n k : ℕ) :
    |(ascPochhammer ℝ k).eval (a + (n : ℝ))| ≤
      (ascPochhammer ℝ k).eval (|a| + (n : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, abs_mul]
    have h2 : |a + (n : ℝ) + (k : ℝ)| ≤ |a| + (n : ℝ) + (k : ℝ) := by
      have hn : |(n : ℝ) + (k : ℝ)| = (n : ℝ) + (k : ℝ) := abs_of_nonneg (by positivity)
      calc |a + (n : ℝ) + (k : ℝ)| = |a + ((n : ℝ) + (k : ℝ))| := by ring_nf
        _ ≤ |a| + |(n : ℝ) + (k : ℝ)| := abs_add_le _ _
        _ = |a| + ((n : ℝ) + (k : ℝ)) := by rw [hn]
        _ = |a| + (n : ℝ) + (k : ℝ) := by ring
    exact mul_le_mul ih h2 (abs_nonneg _) (ascPochhammer_eval_nonneg (by positivity) k)

/-- The binomial series in ascending-Pochhammer form:
`(1 - x)^(-A) = ∑ₖ (A)ₖ / k! · xᵏ` for `|x| < 1`. -/
theorem hasSum_ascPochhammer_div_factorial_mul_pow {A x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => (ascPochhammer ℝ k).eval A / (k.factorial : ℝ) * x ^ k)
      ((1 - x) ^ (-A)) := by
  have hmem : x ∈ Metric.eball (0 : ℝ) (1 : ℝ≥0∞) := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact hx
  have hbase := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero A).hasSum hmem
  have hterm : ∀ n : ℕ,
      (FormalMultilinearSeries.ofScalars ℝ fun k => Ring.choose (A + k - 1) k) n (fun _ => x)
        = (ascPochhammer ℝ n).eval A / (n.factorial : ℝ) * x ^ n := by
    intro n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    congr 1
    rw [ring_choose_eq_ascPochhammer, div_eq_mul_inv]
  have hsum : (1 / (1 - x) ^ A) = (1 - x) ^ (-A) := by
    rw [one_div, ← Real.rpow_neg]
    linarith [(abs_lt.mp hx).2]
  rw [zero_add, hsum] at hbase
  exact hbase.congr_fun fun n => (hterm n).symm

/-- The double family of the Pfaff re-expansion:
`₂F₁-coefficient(a, c-b; c; n) · (-1)^n · (a+n)ₖ / k! · z^(n+k)`. -/
def pfaffFamily (a b c z : ℝ) : ℕ × ℕ → ℝ := fun p =>
  hypCoeff a (c - b) c p.1 * (-1) ^ p.1 *
    ((ascPochhammer ℝ p.2).eval (a + p.1) / (p.2.factorial : ℝ)) * z ^ (p.1 + p.2)

/-- Termwise bound for the Pfaff double family by a nonnegative comparison family. -/
theorem norm_pfaffFamily_le (a b c z : ℝ) (p : ℕ × ℕ) :
    ‖pfaffFamily a b c z p‖ ≤
      ‖hypCoeff a (c - b) c p.1‖ * |z| ^ p.1 *
        ((ascPochhammer ℝ p.2).eval (|a| + (p.1 : ℝ)) / (p.2.factorial : ℝ) *
          |z| ^ p.2) := by
  obtain ⟨n, k⟩ := p
  have hfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hpz : (0 : ℝ) ≤ |z| := abs_nonneg z
  have h1 : |(ascPochhammer ℝ k).eval (a + (n : ℝ))| / (k.factorial : ℝ)
      ≤ (ascPochhammer ℝ k).eval (|a| + (n : ℝ)) / (k.factorial : ℝ) :=
    div_le_div_of_nonneg_right (abs_eval_ascPochhammer_add_le a n k) hfac
  have hnorm : ‖pfaffFamily a b c z (n, k)‖
      = ‖hypCoeff a (c - b) c n‖ * |z| ^ n *
          (|(ascPochhammer ℝ k).eval (a + (n : ℝ))| / (k.factorial : ℝ) * |z| ^ k) := by
    simp only [pfaffFamily, norm_mul, norm_div, norm_pow, norm_neg,
      norm_one, Real.norm_eq_abs, one_pow, mul_one]
    rw [pow_add, abs_of_nonneg hfac]
    ring
  rw [hnorm]
  gcongr

/-- The double series of the Pfaff re-expansion is absolutely summable on `|z| < 1/2`. -/
theorem summable_pfaffFamily {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hz : |z| < 1 / 2) : Summable (pfaffFamily a b c z) := by
  have hz1 : |z| < 1 := by linarith
  have hpos : 0 < 1 - |z| := by linarith
  set ρ : ℝ := |z| / (1 - |z|) with hρdef
  have hρ1 : ρ < 1 := by
    rw [hρdef, div_lt_one hpos]
    linarith
  have hρpos : 0 ≤ ρ := div_nonneg (abs_nonneg z) hpos.le
  have hρ1' : |ρ| < 1 := by rwa [abs_of_nonneg hρpos]
  have hA : Summable (fun n : ℕ => hypCoeff a (c - b) c n * ρ ^ n) :=
    (hasSum_hyp (a := a) (b := c - b) (c := c) (z := ρ) hρ1' hc).summable
  have hAnorm : Summable (fun n : ℕ => ‖hypCoeff a (c - b) c n‖ * ρ ^ n) := by
    refine hA.norm.congr fun n => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hρpos]
  have hrpow : ∀ n : ℕ, (1 - |z|) ^ (-(|a| + (n : ℝ))) * |z| ^ n
      = (1 - |z|) ^ (-|a|) * ρ ^ n := by
    intro n
    have hsplit : (1 - |z|) ^ (-(|a| + (n : ℝ)))
        = (1 - |z|) ^ (-|a|) * ((1 - |z|) ^ (n : ℝ))⁻¹ := by
      rw [show -(|a| + (n : ℝ)) = -|a| + -(n : ℝ) by ring, Real.rpow_add hpos]
      simp_rw [Real.rpow_neg hpos.le]
    rw [hsplit, hρdef, div_pow, Real.rpow_natCast, div_eq_mul_inv]
    ring
  set G : ℕ × ℕ → ℝ := fun p =>
    ‖hypCoeff a (c - b) c p.1‖ * |z| ^ p.1 *
      ((ascPochhammer ℝ p.2).eval (|a| + (p.1 : ℝ)) / (p.2.factorial : ℝ) * |z| ^ p.2)
    with hG
  have hGsum : Summable G := by
    rw [summable_prod_of_nonneg (f := G) (fun p => by
      obtain ⟨n, k⟩ := p
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg z) _))
        (mul_nonneg (div_nonneg (ascPochhammer_eval_nonneg (by positivity) k)
          (by positivity)) (pow_nonneg (abs_nonneg z) _)))]
    constructor
    · intro n
      have hbin := hasSum_ascPochhammer_div_factorial_mul_pow (A := |a| + (n : ℝ)) (x := |z|)
        (by simpa using hz1)
      exact (hbin.mul_left (‖hypCoeff a (c - b) c n‖ * |z| ^ n)).summable
    · have hrow : ∀ n : ℕ, (∑' k : ℕ, G (n, k))
          = (1 - |z|) ^ (-|a|) * (‖hypCoeff a (c - b) c n‖ * ρ ^ n) := by
        intro n
        have hbin := hasSum_ascPochhammer_div_factorial_mul_pow (A := |a| + (n : ℝ)) (x := |z|)
          (by simpa using hz1)
        have h1 : (∑' k : ℕ, G (n, k))
            = ‖hypCoeff a (c - b) c n‖ * |z| ^ n *
                (1 - |z|) ^ (-(|a| + (n : ℝ))) := by
          rw [← (hbin.mul_left (‖hypCoeff a (c - b) c n‖ * |z| ^ n)).tsum_eq]
        rw [h1]
        linear_combination ‖hypCoeff a (c - b) c n‖ * hrpow n
      simp_rw [hrow]
      exact hAnorm.mul_left ((1 - |z|) ^ (-|a|))
  exact Summable.of_norm_bounded hGsum
    (fun p => norm_pfaffFamily_le a b c z p)

/-! ### Row sums and fibre sums

Summing the double series in the second index gives the closed form
`(1 - z)^(-a-n)`, and summing along the fibres `n + k = N` gives back the coefficient of
`hyp a b c`. -/

/-- If `c` is not a nonpositive integer then no ascending Pochhammer symbol at `c` vanishes. -/
theorem ascPochhammer_eval_ne_zero_of_forall_ne_neg {c : ℝ}
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (k : ℕ) : (ascPochhammer ℝ k).eval c ≠ 0 := by
  intro h0
  obtain ⟨j, _, hj⟩ := (ascPochhammer_eval_eq_zero_iff k c).1 h0
  exact hc j (by linarith)

/-- Row sums of the Pfaff double family: summing the binomial series in the second index. -/
theorem tsum_pfaffFamily_row {a b c z : ℝ} (hz : |z| < 1) (n : ℕ) :
    (∑' k : ℕ, pfaffFamily a b c z (n, k))
      = hypCoeff a (c - b) c n * (-1) ^ n * z ^ n * (1 - z) ^ (-(a + (n : ℝ))) := by
  have hbin := hasSum_ascPochhammer_div_factorial_mul_pow (A := a + (n : ℝ)) (x := z) hz
  have h := hbin.mul_left (hypCoeff a (c - b) c n * (-1) ^ n * z ^ n)
  rw [← h.tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [pfaffFamily]
  rw [pow_add]
  ring

/-- The fibre identity in coefficient form: the `N`-th coefficient of `hyp a b c` is the sum
over `k` of the `k`-th coefficient of `hyp a (c-b) c` times the remaining Pochhammer factor.
This is Chu-Vandermonde multiplied by `(a)_N / N!`. -/
theorem sum_hypCoeff_mul_pochhammer_div (a b c : ℝ) (N : ℕ)
    (hc : ∀ k : ℕ, (ascPochhammer ℝ k).eval c ≠ 0) :
    ∑ k ∈ Finset.range (N + 1),
        hypCoeff a (c - b) c k * (-1) ^ k *
          ((ascPochhammer ℝ (N - k)).eval (a + (k : ℝ)) / ((N - k).factorial : ℝ))
      = hypCoeff a b c N := by
  have hprod : ∀ k ≤ N, (ascPochhammer ℝ k).eval a *
      (ascPochhammer ℝ (N - k)).eval (a + (k : ℝ)) = (ascPochhammer ℝ N).eval a := by
    intro k hk
    have hmul := ascPochhammer_mul (S := ℝ) k (N - k)
    have h := congrArg (fun p : Polynomial ℝ => p.eval a) hmul
    simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_natCast] at h
    rw [show k + (N - k) = N by omega] at h
    exact h
  have hfac : ∀ k ≤ N, ((N.factorial : ℝ)) =
      (N.choose k : ℝ) * (k.factorial : ℝ) * ((N - k).factorial : ℝ) := by
    intro k hk
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial hk]
  have hterm : ∀ k ∈ Finset.range (N + 1),
      hypCoeff a (c - b) c k * (-1) ^ k *
          ((ascPochhammer ℝ (N - k)).eval (a + (k : ℝ)) / ((N - k).factorial : ℝ))
        = (ascPochhammer ℝ N).eval a * (N.factorial : ℝ)⁻¹ *
            ((N.choose k : ℝ) * (-1) ^ k *
              ((ascPochhammer ℝ k).eval (c - b) / (ascPochhammer ℝ k).eval c)) := by
    intro k hk
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hPk := hprod k hk'
    have hf := hfac k hk'
    rw [← hPk, hf]
    unfold hypCoeff ordinaryHypergeometricCoefficient
    have hk0 : (k.factorial : ℝ) ≠ 0 := by positivity
    have hNk0 : ((N - k).factorial : ℝ) ≠ 0 := by positivity
    have hC0 : (N.choose k : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk'
      exact ne_of_gt this
    have hc0 : (ascPochhammer ℝ k).eval c ≠ 0 := hc k
    field_simp
  calc
    ∑ k ∈ Finset.range (N + 1),
        hypCoeff a (c - b) c k * (-1) ^ k *
          ((ascPochhammer ℝ (N - k)).eval (a + (k : ℝ)) / ((N - k).factorial : ℝ))
        = (ascPochhammer ℝ N).eval a * (N.factorial : ℝ)⁻¹ *
            ∑ k ∈ Finset.range (N + 1),
              (N.choose k : ℝ) * (-1) ^ k *
                ((ascPochhammer ℝ k).eval (c - b) / (ascPochhammer ℝ k).eval c) := by
          rw [Finset.sum_congr rfl hterm]
          rw [Finset.mul_sum]
    _ = (ascPochhammer ℝ N).eval a * (N.factorial : ℝ)⁻¹ *
          ((ascPochhammer ℝ N).eval b / (ascPochhammer ℝ N).eval c) := by
          rw [sum_choose_neg_one_mul_pochhammer_div b c N hc]
    _ = hypCoeff a b c N := by
          unfold hypCoeff ordinaryHypergeometricCoefficient
          have hN0 : (N.factorial : ℝ) ≠ 0 := by positivity
          have hcN : (ascPochhammer ℝ N).eval c ≠ 0 := hc N
          field_simp

/-- The fibre sum of the Pfaff family at `n + k = N` is the `N`-th term of `hyp a b c`. -/
theorem sum_pfaffFamily_fiber {a b c z : ℝ} (N : ℕ)
    (hc : ∀ k : ℕ, (ascPochhammer ℝ k).eval c ≠ 0) :
    ∑ k ∈ Finset.range (N + 1), pfaffFamily a b c z (k, N - k)
      = hypCoeff a b c N * z ^ N := by
  have hzpow : ∀ k ∈ Finset.range (N + 1), z ^ (k + (N - k)) = z ^ N := by
    intro k hk
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show k + (N - k) = N by omega]
  calc
    ∑ k ∈ Finset.range (N + 1), pfaffFamily a b c z (k, N - k)
        = ∑ k ∈ Finset.range (N + 1),
            (hypCoeff a (c - b) c k * (-1) ^ k *
              ((ascPochhammer ℝ (N - k)).eval (a + (k : ℝ)) /
                ((N - k).factorial : ℝ))) * z ^ N := by
          refine Finset.sum_congr rfl fun k hk => ?_
          simp only [pfaffFamily]
          rw [hzpow k hk]
    _ = (∑ k ∈ Finset.range (N + 1),
            hypCoeff a (c - b) c k * (-1) ^ k *
              ((ascPochhammer ℝ (N - k)).eval (a + (k : ℝ)) /
                ((N - k).factorial : ℝ))) * z ^ N := by
          rw [Finset.sum_mul]
    _ = hypCoeff a b c N * z ^ N := by
          rw [sum_hypCoeff_mul_pochhammer_div a b c N hc]

/-! ### Pfaff's transformation

Combining the two summations of the double series gives the identity on the small disc
`|z| < 1/2`; it is then extended to `(-1, 1/2)` by analytic continuation. -/

/-- Pfaff's transformation on the small disc `|z| < 1/2`. -/
theorem hyp_pfaff_small {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz : |z| < 1 / 2) :
    hyp a b c z = (1 - z) ^ (-a) * hyp a (c - b) c (z / (z - 1)) := by
  have hz1 : |z| < 1 := by linarith
  have hzlt : z < 1 := by linarith [(abs_lt.mp hz1).2]
  have h1zpos : 0 < 1 - z := by linarith
  have hzabs : |z| < 1 - z := by linarith [hz, (abs_lt.mp hz).2]
  have hw : |-(z / (1 - z))| < 1 := by
    rw [abs_neg, abs_div, abs_of_pos h1zpos, div_lt_one h1zpos]
    exact hzabs
  have hneg : -(z / (1 - z)) = z / (z - 1) := by
    have h1 : (1 - z) ≠ 0 := ne_of_gt h1zpos
    have h2 : z - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hsum := summable_pfaffFamily (a := a) (b := b) (c := c) (z := z) hc hz
  have hterm : ∀ n : ℕ, hypCoeff a (c - b) c n * (-1) ^ n * z ^ n *
        (1 - z) ^ (-(a + (n : ℝ)))
      = (1 - z) ^ (-a) * (hypCoeff a (c - b) c n * (-(z / (1 - z))) ^ n) := by
    intro n
    have hpow : (-(z / (1 - z))) ^ n = (-1) ^ n * z ^ n * ((1 - z) ^ n)⁻¹ := by
      rw [neg_pow, div_pow, div_eq_mul_inv]
      ring
    rw [hpow, show -(a + (n : ℝ)) = -a + -(n : ℝ) by ring, Real.rpow_add h1zpos]
    simp_rw [Real.rpow_neg h1zpos.le, Real.rpow_natCast]
    ring
  have htotal : (∑' p : ℕ × ℕ, pfaffFamily a b c z p)
      = (1 - z) ^ (-a) * hyp a (c - b) c (z / (z - 1)) := by
    calc (∑' p : ℕ × ℕ, pfaffFamily a b c z p)
        = ∑' n : ℕ, hypCoeff a (c - b) c n * (-1) ^ n * z ^ n *
            (1 - z) ^ (-(a + (n : ℝ))) := by
          rw [hsum.tsum_prod]
          simp_rw [tsum_pfaffFamily_row hz1]
      _ = ∑' n : ℕ, (1 - z) ^ (-a) *
            (hypCoeff a (c - b) c n * (-(z / (1 - z))) ^ n) := tsum_congr hterm
      _ = (1 - z) ^ (-a) * hyp a (c - b) c (-(z / (1 - z))) := by
          rw [tsum_mul_left]
          exact congrArg (fun t => (1 - z) ^ (-a) * t) (hasSum_hyp hw hc).tsum_eq
      _ = (1 - z) ^ (-a) * hyp a (c - b) c (z / (z - 1)) := by rw [hneg]
  have hfiber : ∀ N : ℕ,
      (∑' p : {p : ℕ × ℕ // p.1 + p.2 = N}, pfaffFamily a b c z p.val)
        = hypCoeff a b c N * z ^ N := by
    intro N
    have hc' : ∀ k : ℕ, (ascPochhammer ℝ k).eval c ≠ 0 :=
      ascPochhammer_eval_ne_zero_of_forall_ne_neg hc
    rw [tsum_congr_subtype (fun p : ℕ × ℕ => pfaffFamily a b c z p)
      (Q := fun p : ℕ × ℕ => p ∈ Finset.antidiagonal N)
      (fun p => (Finset.mem_antidiagonal (n := N)).symm)]
    rw [Finset.tsum_subtype,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun p : ℕ × ℕ => pfaffFamily a b c z p) N]
    exact sum_pfaffFamily_fiber N hc'
  have hfib := hsum.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 + p.2)
  have hfib' : HasSum (fun N : ℕ => hypCoeff a b c N * z ^ N)
      (∑' p : ℕ × ℕ, pfaffFamily a b c z p) :=
    hfib.congr_fun fun N => (hfiber N).symm
  rw [(hasSum_hyp (a := a) (b := b) (c := c) hz1 hc).unique hfib']
  exact htotal

/-- Pfaff's transformation on `(-1, 1/2)`, by analytic continuation from the small disc. -/
theorem hyp_pfaff {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz1 : -1 < z)
    (hz2 : z < 1 / 2) :
    hyp a b c z = (1 - z) ^ (-a) * hyp a (c - b) c (z / (z - 1)) := by
  have hF : AnalyticOnNhd ℝ (fun w : ℝ => hyp a b c w) (Set.Ioo (-1) (1 / 2)) := by
    let S : FormalMultilinearSeries ℝ ℝ ℝ := ordinaryHypergeometricSeries ℝ a b c
    have hrad : (1 : ℝ≥0∞) ≤ S.radius :=
      one_le_hypergeometric_radius (a := a) (b := b) (c := c) hc
    have hpos : 0 < S.radius := lt_of_lt_of_le (by norm_num) hrad
    refine ((S.hasFPowerSeriesOnBall hpos).analyticOnNhd).mono fun w hw => ?_
    have hwabs : |w| < 1 := by
      rw [Set.mem_Ioo] at hw
      rw [abs_lt]
      exact ⟨hw.1, by linarith [hw.2]⟩
    rw [mem_eball_zero_iff, Real.enorm_eq_ofReal_abs]
    exact lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr hwabs) hrad
  have hG : AnalyticOnNhd ℝ
      (fun w : ℝ => (1 - w) ^ (-a) * hyp a (c - b) c (w / (w - 1)))
      (Set.Ioo (-1) (1 / 2)) := by
    have hbase : AnalyticOnNhd ℝ (fun w : ℝ => (1 - w) ^ (-a))
        (Metric.eball 0 (1 : ℝ≥0∞)) := by
      refine AnalyticOnNhd.congr Metric.isOpen_eball
        (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).analyticOnNhd
        (fun w hw => ?_)
      have hwabs : |w| < 1 := by
        rw [mem_eball_zero_iff, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_one] at hw
        exact hw
      have hwl : w < 1 := (abs_lt.mp hwabs).2
      rw [one_div, ← Real.rpow_neg (x := 1 - w) (y := a) (by linarith : (0 : ℝ) ≤ 1 - w)]
    have hpre : AnalyticOnNhd ℝ (fun w : ℝ => (1 - w) ^ (-a)) (Set.Ioo (-1) (1 / 2)) :=
      hbase.mono fun w hw => by
        rw [Set.mem_Ioo] at hw
        have hwabs : |w| < 1 := by
          rw [abs_lt]
          exact ⟨hw.1, by linarith [hw.2]⟩
        rw [mem_eball_zero_iff, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_one]
        exact hwabs
    let S : FormalMultilinearSeries ℝ ℝ ℝ := ordinaryHypergeometricSeries ℝ a (c - b) c
    have hrad : (1 : ℝ≥0∞) ≤ S.radius :=
      one_le_hypergeometric_radius (a := a) (b := c - b) (c := c) hc
    have hpos : 0 < S.radius := lt_of_lt_of_le (by norm_num) hrad
    have houter : AnalyticOnNhd ℝ (fun v : ℝ => hyp a (c - b) c v)
        (Metric.eball 0 (1 : ℝ≥0∞)) :=
      ((S.hasFPowerSeriesOnBall hpos).analyticOnNhd).mono (Metric.eball_subset_eball hrad)
    have hinner : AnalyticOnNhd ℝ (fun w : ℝ => w / (w - 1)) (Set.Ioo (-1) (1 / 2)) :=
      analyticOnNhd_id.div (analyticOnNhd_id.sub analyticOnNhd_const) fun w hw => by
        rw [Set.mem_Ioo] at hw
        have : w - 1 < 0 := by linarith [hw.2]
        linarith
    have hmaps : Set.MapsTo (fun w : ℝ => w / (w - 1))
        (Set.Ioo (-1) (1 / 2)) (Metric.eball 0 (1 : ℝ≥0∞)) := by
      intro w hw
      rw [Set.mem_Ioo] at hw
      have hwabs : |w / (w - 1)| < 1 := by
        rw [abs_div, abs_of_neg (by linarith [hw.2] : w - 1 < 0),
          show -(w - 1) = 1 - w by ring,
          div_lt_one (by linarith [hw.2] : (0 : ℝ) < 1 - w), abs_lt]
        exact ⟨by linarith, by linarith⟩
      rw [mem_eball_zero_iff, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_one]
      exact hwabs
    exact hpre.mul (houter.comp hinner hmaps)
  have hev : (fun w : ℝ => hyp a b c w) =ᶠ[𝓝 0]
      fun w : ℝ => (1 - w) ^ (-a) * hyp a (c - b) c (w / (w - 1)) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 8))
      fun w hw => ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hw
    exact hyp_pfaff_small hc (by linarith [abs_nonneg w, hw])
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1) (1 / 2) := by
    rw [Set.mem_Ioo]
    exact ⟨by norm_num, by norm_num⟩
  have hzmem : z ∈ Set.Ioo (-1) (1 / 2) := by
    rw [Set.mem_Ioo]
    exact ⟨hz1, hz2⟩
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hG isPreconnected_Ioo h0 hev hzmem

/-! ### Continuity at `-1`

When `0 < C - A - B` the coefficients are summable in absolute value, so the Weierstrass
M-test makes the hypergeometric series continuous on `[-1, 1]`. -/

/-- The hypergeometric series at `-1`, absolutely convergent when `0 < C - A - B`. -/
-- Theorem: `∑ₙ hypCoeff A B C n * (-1)^n = hyp A B C (-1)` for `0 < C - A - B`.
theorem hasSum_hypCoeff_neg_one {A B C : ℝ} (h : 0 < C - A - B)
    (hC : ∀ n : ℕ, C ≠ -(n : ℝ)) :
    HasSum (fun n : ℕ => hypCoeff A B C n * (-1) ^ n) (hyp A B C (-1)) := by
  have _ := hC
  rw [hyp_eq_tsum_coeff]
  have h2 : Summable (fun n : ℕ => ‖hypCoeff A B C n‖) :=
    (summable_hypCoeff_one (a := A) (b := B) (c := C) h).norm
  exact (Summable.of_norm_bounded h2 fun n => by
    have h1 : ‖(-1 : ℝ) ^ n‖ = 1 := by simp
    rw [norm_mul, h1, mul_one]).hasSum

/-- Continuity of `hyp A B C` at `-1` from the right, when `0 < C - A - B`. -/
-- Theorem: `Tendsto (fun w => hyp A B C w) (𝓝[>] (-1)) (𝓝 (hyp A B C (-1)))`.
theorem tendsto_hyp_nhdsWithin_neg_one {A B C : ℝ} (h : 0 < C - A - B)
    (hC : ∀ n : ℕ, C ≠ -(n : ℝ)) :
    Filter.Tendsto (fun w : ℝ => hyp A B C w) (nhdsWithin (-1) (Set.Ioi (-1)))
      (nhds (hyp A B C (-1))) := by
  have _ := hC
  have hcont : ContinuousOn (fun x : ℝ => hyp A B C x) (Set.Icc (-1) 1) := by
    have hsum : Summable (fun n : ℕ => ‖hypCoeff A B C n‖) :=
      (summable_hypCoeff_one (a := A) (b := B) (c := C) h).norm
    have hcont_tsum : ContinuousOn (fun x : ℝ => ∑' n : ℕ, hypCoeff A B C n * x ^ n)
        (Set.Icc (-1) 1) := by
      refine continuousOn_tsum (u := fun n : ℕ => ‖hypCoeff A B C n‖)
        (fun n => continuousOn_const.mul (continuousOn_id.pow n)) hsum fun n x hx => ?_
      have hx1 : |x| ≤ 1 := by
        rw [Set.mem_Icc] at hx
        rw [abs_le]
        exact ⟨hx.1, hx.2⟩
      rw [norm_mul, norm_pow, Real.norm_eq_abs]
      calc ‖hypCoeff A B C n‖ * |x| ^ n ≤ ‖hypCoeff A B C n‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hx1) (norm_nonneg _)
        _ = ‖hypCoeff A B C n‖ := mul_one _
    exact hcont_tsum.congr fun x _ => hyp_eq_tsum_coeff A B C x
  have hpt : ContinuousWithinAt (fun x : ℝ => hyp A B C x) (Set.Icc (-1) 1) (-1) :=
    hcont (-1) ⟨le_rfl, by norm_num⟩
  have hmem : Set.Icc (-1 : ℝ) 1 ∈ 𝓝[Set.Ioi (-1)] (-1) := by
    have h2 : Set.Iio (1 : ℝ) ∈ 𝓝[Set.Ioi (-1)] (-1) :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by norm_num))
    have h3 : Set.Ioi (-1 : ℝ) ∈ 𝓝[Set.Ioi (-1)] (-1) := self_mem_nhdsWithin
    refine Filter.mem_of_superset (Filter.inter_mem h3 h2) ?_
    intro x hx
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  exact hpt.mono_left (nhdsWithin_le_iff.mpr hmem)

end

end Pconstructible
