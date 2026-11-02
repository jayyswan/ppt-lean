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

import Pptc.Hypergeometric.SubstODE
import Pptc.Hypergeometric.Quadratic
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # The general Goursat quadratic transformation

Goursat's quadratic transformation of the Gauss hypergeometric function,

`₂F₁(2a, 2b; a + b + 1/2; z) = ₂F₁(a, b; a + b + 1/2; 4z(1-z))` for `0 ≤ z < 1/2`,

in the general case, together with the formal-power-series identity behind it.

The proof has the same two-part shape as the symmetric case `a = b = 1/4` of
`Pptc.Hypergeometric.Quadratic`, and reuses its substitution machinery `w = 4X(1-X)`:

* **Formal identity.** If `c = a + b + 1/2` then substituting `w = 4X(1-X)` into
  `₂F₁(a,b;c;·)` produces a series satisfying the hypergeometric equation of `(2a, 2b; c)`.
  Pulling back the `(a,b;c)` equation along `w` multiplies it by `(w')³ = 64(1-2X)³`; using
  `w(1-w)w'² = 16w(1-w)`, `w(1-w)w'' + w'² = 16(1-2X)²` and `c = a+b+1/2` collects the
  result as `16(1-2X)³ (X(1-X)F'' + c(1-2X)F' - 4abF) = 0`. Since `1-2X` is a unit in
  `ℝ⟦X⟧`, the parenthesis vanishes — the `(2a,2b;c)` equation. Reading off coefficients
  gives the recurrence `(n+1)(n+c)b_{n+1} = (n+2a)(n+2b)b_n`, so `b_n = hypCoeff (2a)(2b)c n`
  by induction; here the hypothesis that `c` is not a nonpositive integer is exactly what
  makes `n + c` invertible.
* **Analytic transfer.** The substitution converges absolutely on `4|z|(1+|z|) < 1`: the
  double series `∑ₘ ∑ₙ c_m · [Xⁿ](w^m) · zⁿ` is summable because its rows are
  finite, its row sums are `hypCoeff a b c m (4z(1-z))^m`, and the resulting series is
  dominated by the hypergeometric series at `B = 4|z|(1+|z|) < 1`. Fubini then identifies
  the iterated sum with `∑ₙ hypCoeff (2a)(2b)c n zⁿ = ₂F₁(2a,2b;c;z)`.
* **Extension to `[0, 1/2)`.** The identity holds near `0`; both sides are analytic on the
  interval `((1-√2)/2, 1/2)` — the inner map lands in the unit disc there — so the identity
  theorem propagates it.
-/

open scoped Topology ENNReal PowerSeries

namespace Pconstructible

noncomputable section

/-! ### The formal identity

The pullback of the `(a,b;c)` hypergeometric equation along `w = 4X(1-X)` is, after
multiplying by `16(1-2X)³`, literally the `(2a,2b;c)` hypergeometric equation. -/

/-- The substituted formal series `₂F₁(a,b;c;4X(1-X))`. -/
def hypSeriesQuadG (a b c : ℝ) : PowerSeries ℝ :=
  PowerSeries.subst quadSubst (hypSeries a b c)

/-- The only rational constant the quadratic substitution needs: `C (1/2)` is a square root
of `1/4`, i.e. `2 · C (1/2) = 1`. -/
-- Theorem: `2 * C (1/2) = 1` in `ℝ⟦X⟧`.
theorem two_mul_C_half : (2 : PowerSeries ℝ) * PowerSeries.C (1 / 2 : ℝ) = 1 := by
  rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, ← map_mul,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, map_one]

/-- The algebraic factorisation behind the formal identity: with `c = a + b + 1/2`,
the `(a,b;c)` equation pulled back along `w = 4X(1-X)` equals `16(1-2X)³` times the
`(2a,2b;c)` equation. Written for an arbitrary `(F, F', F'')` so that it can be applied
to the derivatives of the substituted series. -/
-- Theorem: the pulled-back `(a,b;c)` operator factors as `16(1-2X)³` times the
-- `(2a,2b;c)` operator when `c = a + b + 1/2`.
theorem quadSubst_operator_factor {a b c : ℝ} (h : c = a + b + 1 / 2)
    (F F' F'' : PowerSeries ℝ) :
    quadSubst * (1 - quadSubst) * PowerSeries.derivative ℝ quadSubst * F''
      + (-(quadSubst * (1 - quadSubst)
              * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ quadSubst))
            + (PowerSeries.C c - PowerSeries.C (a + b + 1) * quadSubst)
              * PowerSeries.derivative ℝ quadSubst ^ 2) * F'
      - PowerSeries.C (a * b) * PowerSeries.derivative ℝ quadSubst ^ 3 * F
      = PowerSeries.C 16 * ((1 - 2 * PowerSeries.X) ^ 3
          * (PowerSeries.X * (1 - PowerSeries.X) * F''
            + PowerSeries.C c * (1 - 2 * PowerSeries.X) * F'
            - PowerSeries.C (4 * a * b) * F)) := by
  rw [derivative_derivative_quadSubst, derivative_quadSubst]
  unfold quadSubst
  rw [h]
  simp only [map_add, map_mul, map_ofNat, map_one]
  linear_combination (32 * F' * PowerSeries.X * (1 - PowerSeries.X)
    * (1 - 2 * PowerSeries.X) ^ 2) * two_mul_C_half

/-- The substituted series satisfies the hypergeometric equation of `(2a, 2b; c)` when
`c = a + b + 1/2`: this is the pullback of the `(a,b;c)` equation, divided by the unit
`16 (1-2X)³`. -/
-- Theorem: with `c = a + b + 1/2`, `F = ₂F₁(a,b;c;4X(1-X))` satisfies
-- `X(1-X)F'' + c(1-2X)F' - 4ab F = 0`.
theorem hypSeriesQuadG_ode {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (h : c = a + b + 1 / 2) :
    PowerSeries.X * (1 - PowerSeries.X)
        * PowerSeries.derivative ℝ
            (PowerSeries.derivative ℝ (hypSeriesQuadG a b c))
      + PowerSeries.C c * (1 - 2 * PowerSeries.X)
        * PowerSeries.derivative ℝ (hypSeriesQuadG a b c)
      - PowerSeries.C (4 * a * b) * hypSeriesQuadG a b c = 0 := by
  have hE := hypSeries_subst_ode hc hasSubst_quadSubst
    (φ := quadSubst) (a := a) (b := b) (c := c)
  have hfac := quadSubst_operator_factor (h := h) (F := hypSeriesQuadG a b c)
    (F' := PowerSeries.derivative ℝ (hypSeriesQuadG a b c))
    (F'' := PowerSeries.derivative ℝ
      (PowerSeries.derivative ℝ (hypSeriesQuadG a b c)))
  rw [show hypSeriesQuadG a b c = PowerSeries.subst quadSubst (hypSeries a b c) from rfl] at hfac
  rw [hfac] at hE
  have hunit : IsUnit (PowerSeries.C (16 : ℝ) * (1 - 2 * PowerSeries.X) ^ 3) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hc16 : PowerSeries.constantCoeff
        (PowerSeries.C (16 : ℝ) * (1 - 2 * PowerSeries.X) ^ 3) = 16 := by
      simp
    rw [hc16]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have h2 : (PowerSeries.C (16 : ℝ) * (1 - 2 * PowerSeries.X) ^ 3)
      * (PowerSeries.X * (1 - PowerSeries.X)
          * PowerSeries.derivative ℝ
              (PowerSeries.derivative ℝ (hypSeriesQuadG a b c))
        + PowerSeries.C c * (1 - 2 * PowerSeries.X)
          * PowerSeries.derivative ℝ (hypSeriesQuadG a b c)
        - PowerSeries.C (4 * a * b) * hypSeriesQuadG a b c) = 0 := by
    rw [mul_assoc]
    exact hE
  exact (hunit.mul_right_eq_zero).mp h2

/-- The expanded form of `hypSeriesQuadG_ode`, with the powers of `X` separated so that
coefficient extraction can use the shift lemmas for `X` and `X²`. -/
-- Theorem: `(2c)`-form of the `(2a,2b;c)` equation satisfied by `₂F₁(a,b;c;4X(1-X))`.
theorem hypSeriesQuadG_ode_expand {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (h : c = a + b + 1 / 2) :
    PowerSeries.X
        * PowerSeries.derivative ℝ
            (PowerSeries.derivative ℝ (hypSeriesQuadG a b c))
      - PowerSeries.X ^ 2
        * PowerSeries.derivative ℝ
            (PowerSeries.derivative ℝ (hypSeriesQuadG a b c))
      + PowerSeries.C c * PowerSeries.derivative ℝ (hypSeriesQuadG a b c)
      - PowerSeries.C (2 * c)
        * (PowerSeries.X * PowerSeries.derivative ℝ (hypSeriesQuadG a b c))
      - PowerSeries.C (4 * a * b) * hypSeriesQuadG a b c = 0 := by
  have h0 := hypSeriesQuadG_ode hc h
  rw [show PowerSeries.C (2 * c) = 2 * PowerSeries.C c by rw [map_mul]; rfl]
  linear_combination h0

/-- The coefficient recurrence of the `(2a,2b;c)` equation for the substituted series:
`(n+1)(n+c) b_{n+1} = (n+2a)(n+2b) b_n`. -/
-- Theorem: the coefficients of `₂F₁(a,b;c;4X(1-X))` satisfy the `(2a,2b;c)` recurrence.
theorem coeff_hypSeriesQuadG_rec {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (h : c = a + b + 1 / 2) (n : ℕ) :
    ((n : ℝ) + 1) * ((n : ℝ) + c)
        * PowerSeries.coeff (n + 1) (hypSeriesQuadG a b c)
      = ((n : ℝ) + 2 * a) * ((n : ℝ) + 2 * b)
        * PowerSeries.coeff n (hypSeriesQuadG a b c) := by
  have hcoeff := congrArg (PowerSeries.coeff n) (hypSeriesQuadG_ode_expand hc h)
  rw [map_zero] at hcoeff
  rcases n with _ | _ | k
  · rw [show PowerSeries.X ^ 2 = PowerSeries.X * PowerSeries.X by ring] at hcoeff
    simp only [Nat.cast_zero, zero_add, map_add, map_sub, PowerSeries.coeff_C_mul,
      mul_assoc, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative,
      one_mul] at hcoeff ⊢
    linear_combination hcoeff
  · rw [show PowerSeries.X ^ 2 = PowerSeries.X * PowerSeries.X by ring] at hcoeff
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
      mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_derivative] at hcoeff ⊢
    push_cast
    linear_combination hcoeff + (2 * PowerSeries.coeff 1 (hypSeriesQuadG a b c)) * h
  · rw [show PowerSeries.X ^ 2 = PowerSeries.X * PowerSeries.X by ring] at hcoeff
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, mul_assoc,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative] at hcoeff ⊢
    rw [show k + 1 + 1 = k + 2 by omega, show k + 1 + 1 + 1 = k + 3 by omega] at hcoeff ⊢
    push_cast at hcoeff ⊢
    linear_combination hcoeff
      + (2 * ((k : ℝ) + 2) * PowerSeries.coeff (k + 2) (hypSeriesQuadG a b c)) * h

/-- The formal identity behind the general Goursat transformation:
`₂F₁(a,b;c;4X(1-X)) = ₂F₁(2a,2b;c;X)` as formal power series, when `c = a + b + 1/2`
and `c` is not a nonpositive integer. -/
-- Theorem: `subst (4X(1-X)) (hypSeries a b c) = hypSeries (2a) (2b) c` when `c = a+b+1/2`.
theorem hypSeriesQuadG_eq {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (h : c = a + b + 1 / 2) :
    hypSeriesQuadG a b c = hypSeries (2 * a) (2 * b) c := by
  have h0 : PowerSeries.coeff 0 (hypSeriesQuadG a b c) = 1 := by
    rw [hypSeriesQuadG, PowerSeries.coeff_subst' hasSubst_quadSubst (hypSeries a b c) 0]
    simp only [coeff_hypSeries]
    rw [finsum_eq_single _ (a := 0)]
    · simp [hypCoeff, ordinaryHypergeometricCoefficient]
    · intro d hd
      rw [show PowerSeries.coeff 0 (quadSubst ^ d) = 0 from
        coeff_quadSubst_pow_eq_zero_of_lt (m := d) (n := 0) (by omega), smul_zero]
  have hratio : ∀ n : ℕ,
      PowerSeries.coeff (n + 1) (hypSeriesQuadG a b c)
        = PowerSeries.coeff n (hypSeriesQuadG a b c)
          * (((2 * a + n) * (2 * b + n)) / ((c + n) * (n + 1))) := by
    intro n
    have hrec := coeff_hypSeriesQuadG_rec hc h n
    have hden : ((c : ℝ) + n) * ((n : ℝ) + 1) ≠ 0 := by
      apply mul_ne_zero
      · intro hz
        exact hc n (by linarith)
      · positivity
    rw [← mul_div_assoc, eq_div_iff hden]
    linear_combination hrec
  have hcoeff_eq : ∀ n : ℕ,
      PowerSeries.coeff n (hypSeriesQuadG a b c) = hypCoeff (2 * a) (2 * b) c n := by
    intro n
    induction n with
    | zero =>
      rw [h0]
      norm_num [hypCoeff, ordinaryHypergeometricCoefficient]
    | succ n ih =>
      rw [hratio n, ih, ← hypCoeff_succ (2 * a) (2 * b) c n]
  ext n
  rw [hcoeff_eq n, coeff_hypSeries]

/-! ### The analytic transfer

The formal identity upgrades to an identity of analytic functions: the double series of the
re-expansion is absolutely summable on `4|z|(1+|z|) < 1`, and Fubini identifies its two
iterated sums. -/

/-- The double family whose summation is the re-expansion of
`₂F₁(a,b;c;4z(1-z))` in powers of `z`: the `(m,n)` term is
`c_m · [Xⁿ]((4X(1-X))ᵐ) · zⁿ`. -/
def quadFamilyG (a b c : ℝ) (z : ℝ) : ℕ × ℕ → ℝ := fun p =>
  hypCoeff a b c p.1 * PowerSeries.coeff p.2 (quadSubst ^ p.1) * z ^ p.2

/-- The double family of the re-expansion is summable on the disc `4|z|(1+|z|) < 1`.
Its rows are finite sums (`[Xⁿ]((4X(1-X))ᵐ) = 0` for `n > 2m`) and its iterated sum is
`∑_m |c_m| (4|z|(1+|z|))ᵐ`, summable by the convergence of the hypergeometric series at
the point `4|z|(1+|z|) < 1`. -/
-- Theorem: the double family of the re-expansion is summable on 4|z|(1+|z|) < 1.
theorem summable_quadFamilyG {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) {z : ℝ}
    (hz : 4 * |z| * (1 + |z|) < 1) : Summable (quadFamilyG a b c z) := by
  have hBnn : 0 ≤ 4 * |z| * (1 + |z|) :=
    mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg z)) (by linarith [abs_nonneg z])
  have hB : |4 * |z| * (1 + |z|)| < 1 := by rwa [abs_of_nonneg hBnn]
  apply Summable.of_norm
  change Summable (fun p : ℕ × ℕ =>
    ‖hypCoeff a b c p.1 * PowerSeries.coeff p.2 (quadSubst ^ p.1) * z ^ p.2‖)
  rw [summable_prod_of_nonneg (f := fun p : ℕ × ℕ =>
    ‖hypCoeff a b c p.1 * PowerSeries.coeff p.2 (quadSubst ^ p.1) * z ^ p.2‖)
    (fun p => norm_nonneg _)]
  constructor
  · intro m
    apply summable_of_ne_finset_zero (s := Finset.range (2 * m + 1))
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have h0 : PowerSeries.coeff n (quadSubst ^ m) = 0 :=
      coeff_quadSubst_pow_eq_zero_of_gt (m := m) (n := n) (by omega)
    rw [h0]
    simp
  · have hsum : ∀ m : ℕ, (∑' n : ℕ,
        ‖hypCoeff a b c m * PowerSeries.coeff n (quadSubst ^ m) * z ^ n‖)
        = ‖hypCoeff a b c m‖ * (4 * |z| * (1 + |z|)) ^ m := by
      intro m
      rw [show (fun n : ℕ => ‖hypCoeff a b c m
            * PowerSeries.coeff n (quadSubst ^ m) * z ^ n‖)
          = fun n : ℕ => ‖hypCoeff a b c m‖
            * (‖PowerSeries.coeff n (quadSubst ^ m)‖ * |z| ^ n) by
        funext n
        simp only [norm_mul, norm_pow, Real.norm_eq_abs]
        ring]
      rw [tsum_mul_left, tsum_abs_coeff_quadSubst_pow]
    simp_rw [hsum]
    refine ((hasSum_hyp (a := a) (b := b) (c := c)
      (z := 4 * |z| * (1 + |z|)) hB hc).summable.abs).congr fun m => ?_
    calc ‖hypCoeff a b c m * (4 * |z| * (1 + |z|)) ^ m‖
        = ‖hypCoeff a b c m‖ * ‖(4 * |z| * (1 + |z|)) ^ m‖ := norm_mul _ _
      _ = ‖hypCoeff a b c m‖ * ‖4 * |z| * (1 + |z|)‖ ^ m := by rw [norm_pow]
      _ = ‖hypCoeff a b c m‖ * (4 * |z| * (1 + |z|)) ^ m := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hBnn]

/-- The `n`-th coefficient of the re-expanded series, read off the formal identity
`H(4X(1-X)) = ₂F₁(2a,2b;c;X)`:
`∑_d [Xᵈ]H · [Xⁿ]((4X(1-X))ᵈ) = hypCoeff (2a) (2b) c n`. The `d`-sum is finite because
`[Xⁿ]((4X(1-X))ᵈ) = 0` for `d > n`. -/
-- Theorem: ∑' d, c_d [Xⁿ]((4X(1-X))^d) = hypCoeff (2a) (2b) c n.
theorem tsum_hypCoeff_mul_coeff_quadSubstG {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (h : c = a + b + 1 / 2) (n : ℕ) :
    (∑' d : ℕ, hypCoeff a b c d * PowerSeries.coeff n (quadSubst ^ d))
      = hypCoeff (2 * a) (2 * b) c n := by
  have hsupp : ∀ d ∉ Finset.range (n + 1),
      hypCoeff a b c d * PowerSeries.coeff n (quadSubst ^ d) = 0 := by
    intro d hd
    rw [Finset.mem_range, not_lt] at hd
    rw [coeff_quadSubst_pow_eq_zero_of_lt (by omega), mul_zero]
  have hsupp' : Function.support (fun d : ℕ =>
      hypCoeff a b c d • PowerSeries.coeff n (quadSubst ^ d))
      ⊆ ↑(Finset.range (n + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    by_contra hcon
    exact hd (by rw [smul_eq_mul]; exact hsupp d hcon)
  have hsub := PowerSeries.coeff_subst' hasSubst_quadSubst (hypSeries a b c) n
  rw [show PowerSeries.subst quadSubst (hypSeries a b c)
      = hypSeries (2 * a) (2 * b) c from hypSeriesQuadG_eq hc h] at hsub
  simp only [coeff_hypSeries] at hsub
  rw [hsub, tsum_eq_sum hsupp, finsum_eq_sum_of_support_subset _ hsupp']
  simp only [smul_eq_mul]

/-- The re-expansion of `₂F₁(a,b;c;4z(1-z))` as a power series in `z` converges to it on
the disc `4|z|(1+|z|) < 1`: the double family is summable, its iterated sum is
`₂F₁(a,b;c;4z(1-z))`, and its fibre sums are the coefficients of `₂F₁(2a,2b;c;·)`. -/
-- Theorem: the re-expansion converges to `hyp a b c (4z(1-z))` on 4|z|(1+|z|) < 1.
theorem hasSum_quadFamilyG {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (h : c = a + b + 1 / 2) {z : ℝ} (hz : 4 * |z| * (1 + |z|) < 1) :
    HasSum (fun n : ℕ => hypCoeff (2 * a) (2 * b) c n * z ^ n)
      (hyp a b c (4 * z * (1 - z))) := by
  have hzB : |4 * z * (1 - z)| < 1 := by
    have h1z : |1 - z| ≤ 1 + |z| := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [neg_abs_le z, le_abs_self z]
    calc |4 * z * (1 - z)| = 4 * |z| * |1 - z| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      _ ≤ 4 * |z| * (1 + |z|) :=
          mul_le_mul_of_nonneg_left h1z (mul_nonneg (by norm_num) (abs_nonneg z))
      _ < 1 := hz
  have hg : Summable (quadFamilyG a b c z) := summable_quadFamilyG hc hz
  have hrow : ∀ m : ℕ, (∑' n : ℕ, quadFamilyG a b c z (m, n))
      = hypCoeff a b c m * (4 * z * (1 - z)) ^ m := by
    intro m
    change (∑' n : ℕ, hypCoeff a b c m * PowerSeries.coeff n (quadSubst ^ m)
        * z ^ n) = hypCoeff a b c m * (4 * z * (1 - z)) ^ m
    rw [show (fun n : ℕ => hypCoeff a b c m * PowerSeries.coeff n (quadSubst ^ m)
          * z ^ n) = fun n : ℕ => hypCoeff a b c m
          * (PowerSeries.coeff n (quadSubst ^ m) * z ^ n) by
      funext n; ring]
    rw [tsum_mul_left, tsum_coeff_quadSubst_pow]
  have hcol : ∀ n : ℕ, (∑' m : ℕ, quadFamilyG a b c z (m, n))
      = hypCoeff (2 * a) (2 * b) c n * z ^ n := by
    intro n
    change (∑' m : ℕ, hypCoeff a b c m * PowerSeries.coeff n (quadSubst ^ m)
        * z ^ n) = hypCoeff (2 * a) (2 * b) c n * z ^ n
    rw [show (fun m : ℕ => hypCoeff a b c m * PowerSeries.coeff n (quadSubst ^ m)
          * z ^ n) = fun m : ℕ => (hypCoeff a b c m
          * PowerSeries.coeff n (quadSubst ^ m)) * z ^ n by
      funext m; ring]
    rw [tsum_mul_right, tsum_hypCoeff_mul_coeff_quadSubstG hc h]
  have hfiber : ∀ n : ℕ, (∑' p : {p : ℕ × ℕ // p.2 = n}, quadFamilyG a b c z p.val)
      = ∑' m : ℕ, quadFamilyG a b c z (m, n) := by
    intro n
    let e : ℕ ≃ {p : ℕ × ℕ // p.2 = n} :=
      { toFun := fun m => ⟨(m, n), rfl⟩
        invFun := fun p => p.val.1
        left_inv := fun m => rfl
        right_inv := fun p => by
          obtain ⟨⟨a, b⟩, hb⟩ := p
          change b = n at hb
          subst hb
          rfl }
    rw [← Equiv.tsum_eq e (fun p : {p : ℕ × ℕ // p.2 = n} => quadFamilyG a b c z p.val)]
    exact tsum_congr fun m => rfl
  have ha : (∑' p : ℕ × ℕ, quadFamilyG a b c z p) = hyp a b c (4 * z * (1 - z)) := by
    rw [hg.tsum_prod]
    rw [show (fun m : ℕ => ∑' n : ℕ, quadFamilyG a b c z (m, n))
        = fun m : ℕ => hypCoeff a b c m * (4 * z * (1 - z)) ^ m by
      funext m; exact hrow m]
    exact (hasSum_hyp hzB hc).tsum_eq
  have hfib := hg.hasSum.tsum_fiberwise (Prod.snd : ℕ × ℕ → ℕ)
  rw [ha] at hfib
  exact hfib.congr_fun fun n => by
    change hypCoeff (2 * a) (2 * b) c n * z ^ n
      = ∑' (p : {p : ℕ × ℕ // p.2 = n}), quadFamilyG a b c z p.val
    rw [hfiber n, hcol n]

/-- The general Goursat identity on the small disc `4|z|(1+|z|) < 1`: it follows from the
two `HasSum`s and uniqueness of sums. -/
-- Theorem: the Goursat identity on the disc 4|z|(1+|z|) < 1.
theorem hyp_goursat_small {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (h : c = a + b + 1 / 2) {z : ℝ} (hz : 4 * |z| * (1 + |z|) < 1) :
    hyp (2 * a) (2 * b) c z = hyp a b c (4 * z * (1 - z)) := by
  have hz1 : |z| < 1 := by
    have h4 : 4 * |z| ≤ 4 * |z| * (1 + |z|) := by nlinarith [abs_nonneg z]
    linarith
  exact (hasSum_hyp hz1 hc).unique (hasSum_quadFamilyG hc h hz)

/-- The general Goursat quadratic transformation of the Gauss hypergeometric function:
`₂F₁(2a, 2b; a + b + 1/2; z) = ₂F₁(a, b; a + b + 1/2; 4z(1-z))` for `0 ≤ z < 1/2`.

The small-disc identity `hyp_goursat_small` is extended to `[0, 1/2)` by analytic
continuation on the Cassini interval `((1-√2)/2, 1/2)`, where `|z| < 1` and
`|4z(1-z)| < 1` so both sides are analytic (`hyp` is the sum of its power series on the
unit disc) and they agree near the origin. -/
-- Theorem: the general Goursat quadratic transformation for `0 ≤ z < 1/2`.
theorem hyp_goursat {a b : ℝ} (hc : ∀ n : ℕ, a + b + 1 / 2 ≠ -(n : ℝ))
    {z : ℝ} (hz0 : 0 ≤ z) (hz : z < 1 / 2) :
    hyp (2 * a) (2 * b) (a + b + 1 / 2) z
      = hyp a b (a + b + 1 / 2) (4 * z * (1 - z)) := by
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hzlt : ∀ w ∈ Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2), |w| < 1 := by
    intro w hw
    rw [Set.mem_Ioo] at hw
    obtain ⟨hwl, hwr⟩ := hw
    rw [abs_lt]
    constructor <;> nlinarith [hr, hrnn]
  have hwlt : ∀ w ∈ Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2), |4 * w * (1 - w)| < 1 := by
    intro w hw
    rw [Set.mem_Ioo] at hw
    obtain ⟨hwl, hwr⟩ := hw
    rw [abs_lt]
    constructor
    · have hneg : (w - (1 - Real.sqrt 2) / 2) * (w - (1 + Real.sqrt 2) / 2) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by linarith)
      nlinarith [hneg, hr]
    · nlinarith [sq_pos_of_ne_zero (show 2 * w - 1 ≠ 0 by linarith)]
  have hF : AnalyticOnNhd ℝ (fun w : ℝ => hyp (2 * a) (2 * b) (a + b + 1 / 2) w)
      (Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2)) := by
    let S : FormalMultilinearSeries ℝ ℝ ℝ :=
      ordinaryHypergeometricSeries ℝ (2 * a) (2 * b) (a + b + 1 / 2)
    have hrad : (1 : ℝ≥0∞) ≤ S.radius :=
      one_le_hypergeometric_radius (a := 2 * a) (b := 2 * b) (c := a + b + 1 / 2) hc
    have hpos : 0 < S.radius := lt_of_lt_of_le (by norm_num) hrad
    refine ((S.hasFPowerSeriesOnBall hpos).analyticOnNhd).mono fun w hw => ?_
    have hw1 : (‖w‖ₑ : ℝ≥0∞) < 1 := by
      rw [enorm_eq_nnnorm]
      simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
      exact hzlt w hw
    rw [mem_eball_zero_iff]
    exact lt_of_lt_of_le hw1 hrad
  have hG : AnalyticOnNhd ℝ
      (fun w : ℝ => hyp a b (a + b + 1 / 2) (4 * w * (1 - w)))
      (Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2)) := by
    let S : FormalMultilinearSeries ℝ ℝ ℝ :=
      ordinaryHypergeometricSeries ℝ a b (a + b + 1 / 2)
    have hrad : (1 : ℝ≥0∞) ≤ S.radius :=
      one_le_hypergeometric_radius (a := a) (b := b) (c := a + b + 1 / 2) hc
    have hpos : 0 < S.radius := lt_of_lt_of_le (by norm_num) hrad
    have houter : AnalyticOnNhd ℝ (fun w : ℝ => hyp a b (a + b + 1 / 2) w)
        (Metric.eball 0 (1 : ℝ≥0∞)) :=
      ((S.hasFPowerSeriesOnBall hpos).analyticOnNhd).mono (Metric.eball_subset_eball hrad)
    have hinner : AnalyticOnNhd ℝ (fun w : ℝ => 4 * w * (1 - w))
        (Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2)) :=
      ((analyticOnNhd_const (v := (4 : ℝ))).mul analyticOnNhd_id).mul
        ((analyticOnNhd_const (v := (1 : ℝ))).sub analyticOnNhd_id)
    have hmaps : Set.MapsTo (fun w : ℝ => 4 * w * (1 - w))
        (Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2)) (Metric.eball 0 (1 : ℝ≥0∞)) := by
      intro w hw
      have hw1 : (‖4 * w * (1 - w)‖ₑ : ℝ≥0∞) < 1 := by
        rw [enorm_eq_nnnorm]
        simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
        exact hwlt w hw
      rw [mem_eball_zero_iff]
      exact hw1
    exact houter.comp hinner hmaps
  have hev : (fun w : ℝ => hyp (2 * a) (2 * b) (a + b + 1 / 2) w) =ᶠ[𝓝 0]
      fun w : ℝ => hyp a b (a + b + 1 / 2) (4 * w * (1 - w)) := by
    refine Filter.eventually_of_mem
      (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 8)) fun w hw => ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hw
    exact hyp_goursat_small (c := a + b + 1 / 2) hc rfl (by nlinarith [abs_nonneg w, hw])
  have h0 : (0 : ℝ) ∈ Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2) := by
    rw [Set.mem_Ioo]
    exact ⟨by nlinarith [hr, hrnn], by norm_num⟩
  have hzmem : z ∈ Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2) := by
    rw [Set.mem_Ioo]
    exact ⟨by nlinarith [hr, hrnn, hz0], hz⟩
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hG isPreconnected_Ioo h0 hev hzmem

end

end Pconstructible
