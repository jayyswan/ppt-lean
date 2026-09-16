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
-- `Pptc.Hypergeometric.Basic` supplies the ₂F₁ API and already brings in the binomial
-- series (`Mathlib.Analysis.Analytic.Binomial`) and the interval-integral toolkit.
import Pptc.Hypergeometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Pptc.Hypergeometric.Graphs

Arc lengths of the monomial graphs `y = xⁿ` as Gauss hypergeometric values.

The verified identity (V4 of `PLAN-hypergeometric-00-overview`) is

`∫₀^X √(1 + b² xᵐ) dx = X · ₂F₁(−½, 1/m; 1 + 1/m; −b² Xᵐ)`,

valid when `|b² Xᵐ| < 1`. Its proof is a termwise integration exactly parallel to
`hasSum_arcsin` in `Pptc.Hypergeometric.Basic`: expand `√(1 + u)` by the binomial series
`∑ₖ Ring.choose (1/2) k uᵏ`, integrate `u = b² xᵐ` term by term on `0..X` with
`intervalIntegral.hasSum_integral_of_dominated_convergence`, and match

`Ring.choose (1/2) k / (m k + 1) = (−1)ᵏ · hypCoeff (−1/2) (1/m) (1 + 1/m) k`.

The coefficient identity is the only place the hypergeometric parameters enter: the two
ascending factorials `(1/m)ₖ` and `(1 + 1/m)ₖ` telescope to `1/(m k + 1)`, and
`(−1/2)ₖ/k!` is `(−1)ᵏ C(1/2, k)`.

## The monomial graph

For `y = xⁿ` one has `y' = n xⁿ⁻¹`, so `speed = √(1 + n² x^{2n−2})`: the power-law identity
with `m = 2n − 2` and `b = n`. This is the arc length that H6 feeds into the programme.
-/

open scoped Topology ENNReal

namespace Pconstructible

noncomputable section

/-! ### The binomial series for `√(1 + u)`

`√(1 + u) = (1 + u)^{1/2}` is the binomial series `binomialSeries ℝ (1/2)`, whose `k`-th
coefficient is `Ring.choose (1/2) k`, and `binomialSeries ℝ a` is by definition
`ofScalars ℝ (Ring.choose a ·)`. Mathlib's `Real.one_add_rpow_hasFPowerSeriesOnBall_zero`
supplies the series; the only work is to read off the value `(1 + u)^{1/2} = √(1 + u)` and
to turn the multilinear coefficient into `Ring.choose (1/2) k * uᵏ`. -/

/-- The binomial series for the square root: `√(1 + u) = ∑ₖ Ring.choose (1/2) k uᵏ` for
`|u| < 1`. This is `Real.one_add_rpow_hasFPowerSeriesOnBall_zero` at `a = 1/2`, with the
power series evaluated at `u` and `Real.sqrt` written as the `1/2` power. -/
-- Theorem: for `|u| < 1`, `HasSum (fun k => Ring.choose (1/2) k * u^k) (√(1 + u))`.
lemma hasSum_sqrt_one_add {u : ℝ} (hu : |u| < 1) :
    HasSum (fun k : ℕ => Ring.choose (1 / 2) k * u ^ k) (Real.sqrt (1 + u)) := by
  have hmem : u ∈ Metric.eball (0 : ℝ) (1 : ℝ≥0∞) := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact hu
  have hbase := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (1 / 2 : ℝ))).hasSum hmem
  rw [zero_add, ← Real.sqrt_eq_rpow] at hbase
  exact hbase.congr_fun fun k => by
    simp only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-! ### Coefficient identities

Two elementary facts about ascending factorials, both proved by matching Mathlib's
`Ring.choose` against `(ascPochhammer ℝ k).eval`. The first rewrites `(−1/2)ₖ/k!` as
`(−1)ᵏ C(1/2, k)` — the signs come from `ascPochhammer_eval_neg_eq_descPochhammer`, which
flips a descending factorial into an ascending one at the negated argument. The second is
the telescoping `(1/m)ₖ / (1 + 1/m)ₖ = 1/(m k + 1)` that identifies the integral's
`1/(m k + 1)` with the ratio of the hypergeometric Pochhammer symbols. -/

/-- `Ring.choose (1/2) k = (1/2 − k + 1)ₖ / k!`, the closed form of the binomial
coefficient used to compare with `ascPochhammer` at `−1/2`. -/
-- Theorem: `Ring.choose (1/2) k = (ascPochhammer ℝ k).eval (1/2 - k + 1) / k!`.
lemma ring_choose_half (k : ℕ) :
    Ring.choose (1 / 2) k =
      (ascPochhammer ℝ k).eval ((1 / 2 : ℝ) - k + 1) / (k.factorial : ℝ) := by
  rw [Ring.choose_eq_smul, smul_eq_mul,
    Polynomial.descPochhammer_smeval_eq_ascPochhammer, Polynomial.ascPochhammer_smeval_eq_eval]
  ring

/-- `(−1/2)ₖ / k! = (−1)ᵏ Ring.choose (1/2) k`. The ascending factorial at `−1/2` and the
binomial coefficient at `1/2` differ by the alternating sign `(−1)ᵏ`, which is exactly what
turns the binomial series of `√(1 + u)` into the `₂F₁(−1/2, ·; ·; −u)` coefficient. -/
-- Theorem: `(ascPochhammer ℝ k).eval (-(1/2)) / k! = (-1)^k * Ring.choose (1/2) k`.
lemma ascPochhammer_neg_half_div_factorial (k : ℕ) :
    (ascPochhammer ℝ k).eval (-(1 / 2)) / (k.factorial : ℝ) =
      (-1) ^ k * Ring.choose (1 / 2) k := by
  rw [ring_choose_half k, ascPochhammer_eval_neg_eq_descPochhammer ℝ (1 / 2) k,
    descPochhammer_eval_eq_ascPochhammer ℝ (1 / 2) k]
  ring

/-- The telescoping `(1/m)ₖ / (1 + 1/m)ₖ = 1/(m k + 1)`. The numerator's factor at step `j`
is `1/m + j` and the denominator's is `1 + 1/m + j`, so the product telescopes to
`(1/m)/(k + 1/m) = 1/(m k + 1)`. This is the identity that makes the V4 series a `₂F₁`. -/
-- Theorem: `(ascPochhammer ℝ k).eval (1/m) / (ascPochhammer ℝ k).eval (1+1/m) = 1/(mk+1)`.
lemma ascPochhammer_one_div_ratio (m : ℕ) (hm : 0 < m) (k : ℕ) :
    (ascPochhammer ℝ k).eval (1 / (m : ℝ)) /
        (ascPochhammer ℝ k).eval (1 + 1 / (m : ℝ)) = 1 / ((m : ℝ) * k + 1) := by
  induction k with
  | zero => simp [ascPochhammer]
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ← div_mul_div_comm, ih]
    field_simp
    push_cast
    ring

/-- The hypergeometric coefficient of `₂F₁(−1/2, 1/m; 1 + 1/m; ·)` in terms of the
binomial coefficient of the square-root series. Combining the two preceding lemmas, the
`k`-th coefficient is `(−1)ᵏ C(1/2, k)/(m k + 1)` — the precise factor the termwise
integration produces. -/
-- Theorem: `hypCoeff (-(1/2)) (1/m) (1+1/m) k = (-1)^k * (Ring.choose (1/2) k / (m k + 1))`.
lemma hypCoeff_neg_half_one_div_m (m : ℕ) (hm : 0 < m) (k : ℕ) :
    hypCoeff (-(1 / 2)) (1 / (m : ℝ)) (1 + 1 / (m : ℝ)) k =
      (-1) ^ k * (Ring.choose (1 / 2) k / ((m : ℝ) * k + 1)) := by
  have hA := ascPochhammer_neg_half_div_factorial k
  have hB := ascPochhammer_one_div_ratio m hm k
  have hA' : (ascPochhammer ℝ k).eval (-(1 / 2)) * (k.factorial : ℝ)⁻¹
      = (-1) ^ k * Ring.choose (1 / 2) k := by rw [← hA]; ring
  have hB' : (ascPochhammer ℝ k).eval (1 / (m : ℝ)) *
        ((ascPochhammer ℝ k).eval (1 + 1 / (m : ℝ)))⁻¹ = 1 / ((m : ℝ) * k + 1) := by
    rw [← hB]; ring
  unfold hypCoeff ordinaryHypergeometricCoefficient
  rw [show (k.factorial : ℝ)⁻¹ * (ascPochhammer ℝ k).eval (-(1 / 2)) *
        (ascPochhammer ℝ k).eval (1 / (m : ℝ)) *
        ((ascPochhammer ℝ k).eval (1 + 1 / (m : ℝ)))⁻¹
      = ((ascPochhammer ℝ k).eval (-(1 / 2)) * (k.factorial : ℝ)⁻¹) *
        ((ascPochhammer ℝ k).eval (1 / (m : ℝ)) *
          ((ascPochhammer ℝ k).eval (1 + 1 / (m : ℝ)))⁻¹) by ring,
    hA', hB']
  ring

/-! ### The power-law arc length (V4)

The main theorem. The dominated-convergence bound is the geometric series `∑ |C(1/2, k)| Rᵏ`
for some `R` with `|b² Xᵐ| < R < 1`; every point of `[0, X]` has `|b² xᵐ| ≤ |b² Xᵐ| < R`, so
the binomial term is bounded by `|C(1/2, k)| Rᵏ`, which is summable because the binomial
series is absolutely convergent on `|R| < 1`. -/

/-- **V4, the general power-law arc length.** For `m > 0`, `X ≥ 0` and `|b² Xᵐ| < 1`,

`∫₀^X √(1 + b² xᵐ) dx = X · ₂F₁(−½, 1/m; 1 + 1/m; −b² Xᵐ)`.

The smallness hypothesis is what keeps the binomial series of `√(1 + b² xᵐ)` inside its
open disc of convergence on the whole interval of integration; at `|b² Xᵐ| = 1` the
dominating geometric bound of the proof no longer exists (the identity itself is true but
needs a separate limiting argument). -/
-- Theorem: `∫₀^X √(1 + b² x^m) = X * hyp (-(1/2)) (1/m) (1 + 1/m) (-(b² X^m))`.
theorem integral_sqrt_one_add_sq_mul_pow {m : ℕ} (hm : 0 < m) {b X : ℝ} (hX : 0 ≤ X)
    (hsmall : |b ^ 2 * X ^ m| < 1) :
    ∫ x in (0 : ℝ)..X, Real.sqrt (1 + b ^ 2 * x ^ m)
      = X * hyp (-(1 / 2)) (1 / m) (1 + 1 / m) (-(b ^ 2 * X ^ m)) := by
  obtain ⟨R, hRz, hR1⟩ := exists_between hsmall
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg _) hRz
  have hRpos' : 0 ≤ R := hRpos.le
  have hRlt : |R| < 1 := by rwa [abs_of_pos hRpos]
  -- The geometric bound series is absolutely summable.
  have hsumC : Summable fun k : ℕ => |Ring.choose (1 / 2) k| * R ^ k := by
    have h := (hasSum_sqrt_one_add (u := R) hRlt).summable.abs
    simpa only [abs_mul, abs_pow, abs_of_nonneg hRpos'] using h
  -- Every point of `(0, X]` has `|b² tᵐ| ≤ R`.
  have hbnd : ∀ t : ℝ, t ∈ Set.uIoc (0 : ℝ) X → |b ^ 2 * t ^ m| ≤ R := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) X := by
      have hsub := Set.uIoc_subset_uIcc ht
      rwa [Set.uIcc_of_le hX] at hsub
    have ht0 : (0 : ℝ) ≤ t := htI.1
    have hb2 : (0 : ℝ) ≤ b ^ 2 := sq_nonneg b
    have hle : t ^ m ≤ X ^ m := pow_le_pow_left₀ ht0 htI.2 m
    have hnonneg : 0 ≤ b ^ 2 * t ^ m := mul_nonneg hb2 (pow_nonneg ht0 m)
    have hzle : b ^ 2 * X ^ m ≤ R := by
      rw [← abs_of_nonneg (mul_nonneg hb2 (pow_nonneg hX m))]
      exact hRz.le
    rw [abs_of_nonneg hnonneg]
    exact le_trans (mul_le_mul_of_nonneg_left hle hb2) hzle
  -- Termwise integration.
  have hmain : HasSum
      (fun k : ℕ => ∫ t in (0 : ℝ)..X, Ring.choose (1 / 2) k * (b ^ 2 * t ^ m) ^ k)
      (∫ t in (0 : ℝ)..X, Real.sqrt (1 + b ^ 2 * t ^ m)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun k (_ : ℝ) => |Ring.choose (1 / 2) k| * R ^ k)
    · intro k
      exact (continuous_const.mul
        ((continuous_const.mul (continuous_id.pow m)).pow k)).aestronglyMeasurable
    · intro k
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have hC : (0 : ℝ) ≤ |Ring.choose (1 / 2) k| := abs_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hbnd t ht) k) hC
    · exact Filter.Eventually.of_forall (fun _ _ => hsumC)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall
        (fun t ht => hasSum_sqrt_one_add (lt_of_le_of_lt (hbnd t ht) hR1))
  -- Evaluate each term.
  have hterm : ∀ k : ℕ,
      (∫ t in (0 : ℝ)..X, Ring.choose (1 / 2) k * (b ^ 2 * t ^ m) ^ k)
        = X * (Ring.choose (1 / 2) k * (b ^ 2 * X ^ m) ^ k / ((m : ℝ) * k + 1)) := by
    intro k
    have hfun : (fun t : ℝ => Ring.choose (1 / 2) k * (b ^ 2 * t ^ m) ^ k)
        = fun t => (Ring.choose (1 / 2) k * b ^ (2 * k)) * t ^ (m * k) := by
      funext t
      rw [mul_pow, show (b ^ 2) ^ k = b ^ (2 * k) by rw [← pow_mul],
        show (t ^ m) ^ k = t ^ (m * k) by rw [← pow_mul]]
      ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
    rw [zero_pow (Nat.succ_ne_zero (m * k)), sub_zero]
    have hxp : (b ^ 2 * X ^ m) ^ k = b ^ (2 * k) * X ^ (m * k) := by
      rw [mul_pow, show (b ^ 2) ^ k = b ^ (2 * k) by rw [← pow_mul],
        show (X ^ m) ^ k = X ^ (m * k) by rw [← pow_mul]]
    rw [hxp, pow_succ']
    field_simp
    push_cast
    ring
  -- Assemble: the `X`-multiple of the hypergeometric series.
  have hXG : HasSum
      (fun k : ℕ => X *
        (Ring.choose (1 / 2) k * (b ^ 2 * X ^ m) ^ k / ((m : ℝ) * k + 1)))
      (X * hyp (-(1 / 2)) (1 / m) (1 + 1 / m) (-(b ^ 2 * X ^ m))) := by
    have hc : ∀ k : ℕ, (1 + 1 / (m : ℝ)) ≠ -(k : ℝ) := by
      intro k
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hpos : (0 : ℝ) < 1 + 1 / (m : ℝ) := by positivity
      linarith
    have hz : |(-(b ^ 2 * X ^ m))| < 1 := by rwa [abs_neg]
    have hh := (hasSum_hyp (a := -(1 / 2)) (b := 1 / (m : ℝ)) (c := 1 + 1 / (m : ℝ))
      (z := -(b ^ 2 * X ^ m)) hz hc).mul_left X
    refine hh.congr_fun (fun k => ?_)
    have hsign : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hneg : (-(b ^ 2 * X ^ m) : ℝ) ^ k = (-1) ^ k * (b ^ 2 * X ^ m) ^ k := by
      rw [neg_pow]
    have hterm' : (-1 : ℝ) ^ k * (Ring.choose (1 / 2) k / ((m : ℝ) * k + 1)) *
          ((-1) ^ k * (b ^ 2 * X ^ m) ^ k)
        = Ring.choose (1 / 2) k * (b ^ 2 * X ^ m) ^ k / ((m : ℝ) * k + 1) := by
      rw [show (-1 : ℝ) ^ k * (Ring.choose (1 / 2) k / ((m : ℝ) * k + 1)) *
            ((-1) ^ k * (b ^ 2 * X ^ m) ^ k)
          = ((-1 : ℝ) ^ k * (-1) ^ k) *
            (Ring.choose (1 / 2) k / ((m : ℝ) * k + 1)) * (b ^ 2 * X ^ m) ^ k by ring,
        hsign, one_mul]
      ring
    rw [hypCoeff_neg_half_one_div_m m hm k, hneg]
    congr 1
    rw [hterm']
  refine hmain.congr_fun (fun k => (hterm k).symm) |>.unique hXG

/-- **V4 for the monomial graph `y = xⁿ`.** Substituting `m = 2n − 2`, `b = n` into
`integral_sqrt_one_add_sq_mul_pow` gives the arc-length element `√(1 + n² x^{2n−2})`. -/
-- Theorem: `∫₀^X √(1 + n² x^{2n-2}) = X * hyp (-(1/2)) (1/(2n-2)) (1+1/(2n-2)) (-(n² X^{2n-2}))`.
theorem integral_sqrt_one_add_sq_pow_of_nat {n : ℕ} (hn : 2 ≤ n) {X : ℝ} (hX : 0 ≤ X)
    (hsmall : |(n : ℝ) ^ 2 * X ^ (2 * n - 2)| < 1) :
    ∫ x in (0 : ℝ)..X, Real.sqrt (1 + (n : ℝ) ^ 2 * x ^ (2 * n - 2))
      = X * hyp (-(1 / 2)) (1 / ((2 * n - 2 : ℕ) : ℝ))
          (1 + 1 / ((2 * n - 2 : ℕ) : ℝ))
          (-((n : ℝ) ^ 2 * X ^ (2 * n - 2))) := by
  have hm : 0 < 2 * n - 2 := by omega
  exact integral_sqrt_one_add_sq_mul_pow (m := 2 * n - 2) hm (b := (n : ℝ)) hX hsmall

/-! ### Arc length of the monomial graph

With `γ x = (x, xⁿ)` we have `x' = 1` and `y' = n xⁿ⁻¹`, so

`speed γ t = √(1² + (n tⁿ⁻¹)²) = √(1 + n² t^{2n−2})`.

This is a pointwise rewriting of the definition of `speed` (which is the Euclidean norm
`√(x'² + y'²)` written out — see the note in `Pptc.Defs`), followed by the power-law
integral above. -/

/-- The speed of the monomial graph `y = xⁿ` is `√(1 + n² x^{2n−2})`. -/
-- Theorem: `speed (fun x => (x, x^n)) t = √(1 + n² t^(2n-2))`.
lemma speed_graph_pow {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    speed (fun x : ℝ => (x, x ^ n)) t = Real.sqrt (1 + (n : ℝ) ^ 2 * t ^ (2 * n - 2)) := by
  have h1 : deriv (fun s : ℝ => ((fun x : ℝ => (x, x ^ n)) s).1) t = 1 := by simp
  have h2 : deriv (fun s : ℝ => ((fun x : ℝ => (x, x ^ n)) s).2) t = (n : ℝ) * t ^ (n - 1) := by
    change deriv (fun s : ℝ => s ^ n) t = (n : ℝ) * t ^ (n - 1)
    rw [deriv_pow_field]
  have hpow : (n - 1) * 2 = 2 * n - 2 := by omega
  simp only [speed]
  rw [h1, h2, one_pow, mul_pow, ← pow_mul, hpow]

set_option linter.unusedVariables false in
/-- **Arc length of `y = xⁿ` from the origin.** The arc length of the monomial graph is the
power-law integral with `m = 2n − 2`, `b = n`. -/
-- Theorem: `arcLengthOf (fun x => (x, x^n)) 0 X = ∫₀^X √(1 + n² x^(2n-2))`.
theorem arcLengthOf_graph_pow {n : ℕ} (hn : 2 ≤ n) {X : ℝ} (hX : 0 ≤ X) :
    arcLengthOf (fun x : ℝ => (x, x ^ n)) 0 X
      = ∫ x in (0 : ℝ)..X, Real.sqrt (1 + (n : ℝ) ^ 2 * x ^ (2 * n - 2)) := by
  rw [arcLengthOf]
  exact intervalIntegral.integral_congr (fun t _ => speed_graph_pow hn t)

/-- **The monomial arc length as a ₂F₁** (H6). Combining the two theorems above:
for `n ≥ 2`, `X ≥ 0` and `|n² X^{2n−2}| < 1`, the arc length of `y = xⁿ` from `(0, 0)` to
`(X, Xⁿ)` is `X · ₂F₁(−½, 1/(2n−2); 1 + 1/(2n−2); −n² X^{2n−2})`. -/
-- Theorem: `arcLengthOf (fun x => (x, x^n)) 0 X = X * hyp (-(1/2)) (1/(2n-2)) ...`.
theorem arcLengthOf_graph_pow_eq_hyp {n : ℕ} (hn : 2 ≤ n) {X : ℝ} (hX : 0 ≤ X)
    (hsmall : |(n : ℝ) ^ 2 * X ^ (2 * n - 2)| < 1) :
    arcLengthOf (fun x : ℝ => (x, x ^ n)) 0 X
      = X * hyp (-(1 / 2)) (1 / ((2 * n - 2 : ℕ) : ℝ))
          (1 + 1 / ((2 * n - 2 : ℕ) : ℝ))
          (-((n : ℝ) ^ 2 * X ^ (2 * n - 2))) := by
  rw [arcLengthOf_graph_pow hn hX]
  exact integral_sqrt_one_add_sq_pow_of_nat hn hX hsmall

/-! ### The scaled monomial graph `y = (b / n) xⁿ`

The graph `y = xⁿ` is the `b = n` case of V4. The general coefficient `b` is reached by an
*affine* move: `PConstructibleCurve.scale_y (b / n)` carries the graph of `xⁿ` to the graph
of `(b / n) xⁿ`, so the latter is again a `PConstructibleCurve` and `arc_length` reads its
arc. The differential is what makes this exactly V4: the derivative of `(b / n) xⁿ` is
`(b / n) · n xⁿ⁻¹ = b xⁿ⁻¹`, so the `b / n` scaling cancels the `n` that came from
differentiating the monomial and the speed is `√(1 + b² x^{2n−2})`. Feeding
`integral_sqrt_one_add_sq_mul_pow` with `m = 2n − 2` then produces the `₂F₁` value, and
since the arc length is `X` times that value, dividing by the P-constructible `X` recovers
the hypergeometric value itself. -/

/-- The speed of the scaled monomial graph `y = (b / n) xⁿ` is `√(1 + b² x^{2n−2})`. The
coefficient `b / n` cancels the `n` in the derivative `(b / n) · n xⁿ⁻¹ = b xⁿ⁻¹`, which is
why the general-`b` family is still the V4 integral. -/
-- Theorem: `speed (fun x => (x, (b/n) * x^n)) t = √(1 + b² t^(2n-2))`.
lemma speed_scaledGraph_pow {n : ℕ} (hn : 2 ≤ n) (b t : ℝ) :
    speed (fun x : ℝ => (x, (b / n) * x ^ n)) t
      = Real.sqrt (1 + b ^ 2 * t ^ (2 * n - 2)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have h1 : deriv (fun s : ℝ => ((fun x : ℝ => (x, (b / n) * x ^ n)) s).1) t = 1 := by simp
  have h2 : deriv (fun s : ℝ => ((fun x : ℝ => (x, (b / n) * x ^ n)) s).2) t
      = b * t ^ (n - 1) := by
    change deriv (fun s : ℝ => (b / n) * s ^ n) t = b * t ^ (n - 1)
    rw [deriv_const_mul_field, deriv_pow_field]
    have hc : (b / n) * (n : ℝ) = b := by field_simp
    rw [← mul_assoc, hc]
  have hpow : (n - 1) * 2 = 2 * n - 2 := by omega
  simp only [speed]
  rw [h1, h2, one_pow, mul_pow, ← pow_mul, hpow]

/-- **V4 for the scaled monomial graph `y = (b / n) xⁿ`.** For `n ≥ 2`, `X ≥ 0` and
`|b² X^{2n−2}| < 1`,

`arcLengthOf (fun t => (t, (b / n) tⁿ)) 0 X = X · ₂F₁(−½, 1/(2n−2); 1 + 1/(2n−2); −b² X^{2n−2})`.

This is the general-`b` form of `arcLengthOf_graph_pow_eq_hyp`, which is the case `b = n`. -/
-- Theorem: `arcLengthOf (fun t => (t, (b/n) * t^n)) 0 X
--   = X * hyp (-(1/2)) (1/(2n-2)) (1 + 1/(2n-2)) (-(b² X^(2n-2)))`.
theorem arcLengthOf_scaledGraph_pow {n : ℕ} (hn : 2 ≤ n) {b X : ℝ} (hX0 : 0 ≤ X)
    (hsmall : |b ^ 2 * X ^ (2 * n - 2)| < 1) :
    arcLengthOf (fun t : ℝ => (t, (b / n) * t ^ n)) 0 X
      = X * hyp (-(1 / 2)) (1 / ((2 * n - 2 : ℕ) : ℝ))
          (1 + 1 / ((2 * n - 2 : ℕ) : ℝ))
          (-(b ^ 2 * X ^ (2 * n - 2))) := by
  rw [arcLengthOf]
  rw [show (∫ t in (0 : ℝ)..X, speed (fun x : ℝ => (x, (b / n) * x ^ n)) t)
        = ∫ t in (0 : ℝ)..X, Real.sqrt (1 + b ^ 2 * t ^ (2 * n - 2)) from
      intervalIntegral.integral_congr (fun t _ => speed_scaledGraph_pow hn b t)]
  exact integral_sqrt_one_add_sq_mul_pow (m := 2 * n - 2) (by omega) hX0 hsmall

/-- **The general-`b` V4 value is P-constructible.** The curve `y = (b / n) xⁿ` is the
`scale_y (b / n)` image of `PConstructibleCurve.poly_graph (X ^ n)`, hence a
`PConstructibleCurve` (the degree bound `n ≤ 6` is inherited from `poly_graph`), and
`arc_length` measures the arc from the origin. By `arcLengthOf_scaledGraph_pow` that arc
length is `X · ₂F₁(…)`; since `X > 0` the hypergeometric value is `arcLengthOf γ 0 X / X`,
and both the arc length and `X` are P-constructible. -/
-- Theorem: `PConstructible (hyp (-(1/2)) (1/(2n-2)) (1+1/(2n-2)) (-(b² X^(2n-2))))`.
@[pconstructible_cond]
theorem hyp_neg_half_arcLength_Pconstructible {n : ℕ} (hn : 2 ≤ n) (hn6 : n ≤ 6) {b X : ℝ}
    (hb : PConstructible b) (hX : PConstructible X) (hX0 : 0 < X)
    (hsmall : |b ^ 2 * X ^ (2 * n - 2)| < 1) :
    PConstructible (hyp (-(1 / 2)) (1 / ((2 * n - 2 : ℕ) : ℝ))
          (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) (-(b ^ 2 * X ^ (2 * n - 2)))) := by
  have hdeg : (Polynomial.X ^ n : Polynomial ℚ).natDegree ≤ 6 := by
    rw [Polynomial.natDegree_X_pow]; exact hn6
  have hcurve := PConstructibleCurve.scale_y
    (PConstructibleCurve.poly_graph (Polynomial.X ^ n) hdeg)
    (PConstructible.div hb (nat_Pconstructible n))
  have hlen : PConstructible (arcLengthOf (fun t : ℝ => (t, (b / n) * t ^ n)) 0 X) := by
    refine PConstructible.arc_length hcurve (fun t : ℝ => (t, (b / n) * t ^ n)) hX0.le
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro q ⟨t, _, rfl⟩
      exact ⟨(t, t ^ n), by simp [Polynomial.aeval_X_pow], rfl⟩
    · intro t₁ _ t₂ _ h
      exact congrArg Prod.fst h
    · intro t _
      exact ⟨differentiableAt_id, (differentiableAt_id.pow n).const_mul (b / n)⟩
    · rw [show speed (fun x : ℝ => (x, (b / n) * x ^ n))
            = fun t => Real.sqrt (1 + b ^ 2 * t ^ (2 * n - 2)) from
          funext (speed_scaledGraph_pow hn b)]
      apply Continuous.intervalIntegrable
      fun_prop
    · simpa using zero_Pconstructible
    · have h0 : (b / n) * (0 : ℝ) ^ n = 0 := by
        rw [zero_pow (by omega : n ≠ 0), mul_zero]
      rw [h0]; exact zero_Pconstructible
    · simpa using hX
    · simpa using PConstructible.mul (PConstructible.div hb (nat_Pconstructible n))
        (pow_Pconstructible hX n)
  have hArc := arcLengthOf_scaledGraph_pow hn hX0.le hsmall
  have hhyp : hyp (-(1 / 2)) (1 / ((2 * n - 2 : ℕ) : ℝ))
        (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) (-(b ^ 2 * X ^ (2 * n - 2)))
      = arcLengthOf (fun t : ℝ => (t, (b / n) * t ^ n)) 0 X / X := by
    rw [eq_div_iff (ne_of_gt hX0), mul_comm]
    exact hArc.symm
  rw [hhyp]
  exact PConstructible.div hlen hX

/-! ### Affine images of the monomial graph (bonus)

An affine map of the plane acts on the monomial graph `(t, tⁿ)` as
`(t, tⁿ) ↦ (a t + b tⁿ + e, c t + d tⁿ + f)`, so the image is the parametric curve

`γ t = (a t + b tⁿ + e, c t + d tⁿ + f)`.

That image is a constructible curve: `linearMap_PConstructibleCurve` supplies the linear
part `(x, y) ↦ (a x + b y, c x + d y)` and `PConstructibleCurve.translate_x` /
`translate_y` supply the translation `(e, f)`. Hence `PConstructible.arc_length` measures
any sub-arc whose plane endpoints are P-constructible, which is the theorem below.

`arc_length` also requires the tracing to be injective on the parameter interval, and that
is genuinely an extra hypothesis here — unlike the graph case, an affine image need not be
injective (a degenerate image can double back). It is automatic whenever the linear part is
invertible: if `a * d - b * c ≠ 0` then `a u + b v = c u + d v = 0` forces `u = v = 0`, so
`γ t = γ s` gives `t = s` and `tⁿ = sⁿ`. It is carried explicitly rather than derived so
that the statement also covers the non-invertible but still injective images.

Only the axis-scaling sub-case `b = c = 0`, `e = f = 0` — the curve `t ↦ (a t, d tⁿ)` —
returns a monomial graph, and under the substitution `x = a t` it is exactly the family of
the previous section with effective coefficient `b = d / a`. A genuine shear (`b ≠ 0` or
`c ≠ 0`) leaves the `₂F₁` world: the speed is
`√((a + b n tⁿ⁻¹)² + (c + d n tⁿ⁻¹)²)`, whose radicand is a *quadratic* in `tⁿ⁻¹`, so the
arc length is a hyperelliptic integral rather than a `₂F₁` value. -/

/-- The speed of the affine image of the monomial graph. The velocity of
`γ t = (a t + b tⁿ + e, c t + d tⁿ + f)` is `(a + b n tⁿ⁻¹, c + d n tⁿ⁻¹)`, so the speed is
the square root of the sum of their squares. -/
-- Theorem: `speed (fun t => (a*t + b*t^n + e, c*t + d*t^n + f)) t
--   = √((a + b*n*t^(n-1))² + (c + d*n*t^(n-1))²)`.
lemma speed_affineImageGraph_pow {n : ℕ} (a b c d e f t : ℝ) :
    speed (fun s : ℝ => (a * s + b * s ^ n + e, c * s + d * s ^ n + f)) t
      = Real.sqrt ((a + b * n * t ^ (n - 1)) ^ 2
          + (c + d * n * t ^ (n - 1)) ^ 2) := by
  have hx : HasDerivAt (fun s : ℝ => a * s + b * s ^ n + e)
      (a + b * (n * t ^ (n - 1))) t := by
    have h1 : HasDerivAt (fun s : ℝ => a * s) a t := hasDerivAt_const_mul a
    have h2 : HasDerivAt (fun s : ℝ => b * s ^ n) (b * (n * t ^ (n - 1))) t :=
      (hasDerivAt_pow n t).const_mul b
    simpa using (hasDerivAt_add_const_iff (f := fun s : ℝ => a * s + b * s ^ n) e).mpr
      (h1.add h2)
  have hy : HasDerivAt (fun s : ℝ => c * s + d * s ^ n + f)
      (c + d * (n * t ^ (n - 1))) t := by
    have h1 : HasDerivAt (fun s : ℝ => c * s) c t := hasDerivAt_const_mul c
    have h2 : HasDerivAt (fun s : ℝ => d * s ^ n) (d * (n * t ^ (n - 1))) t :=
      (hasDerivAt_pow n t).const_mul d
    simpa using (hasDerivAt_add_const_iff (f := fun s : ℝ => c * s + d * s ^ n) f).mpr
      (h1.add h2)
  have hdx : deriv (fun s : ℝ => ((fun s : ℝ => (a * s + b * s ^ n + e,
      c * s + d * s ^ n + f)) s).1) t = a + b * (n * t ^ (n - 1)) := by
    change deriv (fun s : ℝ => a * s + b * s ^ n + e) t = a + b * (n * t ^ (n - 1))
    exact hx.deriv
  have hdy : deriv (fun s : ℝ => ((fun s : ℝ => (a * s + b * s ^ n + e,
      c * s + d * s ^ n + f)) s).2) t = c + d * (n * t ^ (n - 1)) := by
    change deriv (fun s : ℝ => c * s + d * s ^ n + f) t = c + d * (n * t ^ (n - 1))
    exact hy.deriv
  simp only [speed, hdx, hdy]
  congr 1
  ring

/-- **Affine images of the monomial graph have P-constructible arc length.** For
P-constructible `a, b, c, d, e, f, X` with `0 ≤ X`, and a tracing that is injective on
`[0, X]`, the arc length of `t ↦ (a t + b tⁿ + e, c t + d tⁿ + f)` over `[0, X]` is
P-constructible. The curve is the affine image of `PConstructibleCurve.poly_graph (X ^ n)`
and `PConstructible.arc_length` reads the length off it. -/
-- Theorem: `PConstructible (arcLengthOf (fun t => (a*t + b*t^n + e, c*t + d*t^n + f)) 0 X)`.
theorem arcLengthOf_affineImageGraph_pow_Pconstructible {n : ℕ} (hn : 2 ≤ n) (hn6 : n ≤ 6)
    {a b c d e f X : ℝ} (ha : PConstructible a) (hb : PConstructible b)
    (hc : PConstructible c) (hd : PConstructible d) (he : PConstructible e)
    (hf : PConstructible f) (hX : PConstructible X) (hX0 : 0 ≤ X)
    (hinj : Set.InjOn (fun t : ℝ => (a * t + b * t ^ n + e, c * t + d * t ^ n + f))
      (Set.Icc 0 X)) :
    PConstructible (arcLengthOf
      (fun t : ℝ => (a * t + b * t ^ n + e, c * t + d * t ^ n + f)) 0 X) := by
  have hdeg : (Polynomial.X ^ n : Polynomial ℚ).natDegree ≤ 6 := by
    rw [Polynomial.natDegree_X_pow]; exact hn6
  have hcurve := PConstructibleCurve.translate_y
    (PConstructibleCurve.translate_x
      (linearMap_PConstructibleCurve
        (PConstructibleCurve.poly_graph (Polynomial.X ^ n) hdeg) ha hb hc hd) he) hf
  refine PConstructible.arc_length hcurve
    (fun t : ℝ => (a * t + b * t ^ n + e, c * t + d * t ^ n + f)) hX0 ?_ hinj
      ?_ ?_ ?_ ?_ ?_ ?_
  · rintro q ⟨t, _, rfl⟩
    refine ⟨(a * t + b * t ^ n + e, c * t + d * t ^ n), ?_, rfl⟩
    refine ⟨(a * t + b * t ^ n, c * t + d * t ^ n), ?_, rfl⟩
    exact ⟨(t, t ^ n), by simp [Polynomial.aeval_X_pow], rfl⟩
  · intro t _
    constructor <;> fun_prop
  · rw [show speed (fun s : ℝ => (a * s + b * s ^ n + e, c * s + d * s ^ n + f))
          = fun t => Real.sqrt ((a + b * n * t ^ (n - 1)) ^ 2
              + (c + d * n * t ^ (n - 1)) ^ 2) from
        funext (speed_affineImageGraph_pow a b c d e f)]
    apply Continuous.intervalIntegrable
    fun_prop
  · simpa [zero_pow (by omega : n ≠ 0)] using he
  · simpa [zero_pow (by omega : n ≠ 0)] using hf
  · simpa using PConstructible.add (PConstructible.add (PConstructible.mul ha hX)
      (PConstructible.mul hb (pow_Pconstructible hX n))) he
  · simpa using PConstructible.add (PConstructible.add (PConstructible.mul hc hX)
      (PConstructible.mul hd (pow_Pconstructible hX n))) hf

end

end Pconstructible
