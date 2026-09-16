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
-- `Hypergeometric.Basic` is the fixed L1 API; `FDeriv.Analytic` supplies
-- `HasFPowerSeriesOnBall.fderiv`, which turns the hypergeometric power series into its
-- derivative series.
import Pptc.Hypergeometric.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Pptc.Hypergeometric.Contiguous

The derivative and the Gauss contiguous relations for `₂F₁(a, b; c; z)` over the reals.

## Why the derivative is the bridge

Mathlib's `ordinaryHypergeometric` is the sum of its power series, which is analytic on the
open unit disc. Differentiating termwise gives

`d/dz ₂F₁(a,b;c;z) = (ab/c) ₂F₁(a+1,b+1;c+1;z)` (DLMF 15.5.1),

and the Gauss contiguous relations (DLMF 15.5.11–15.5.18) then express each of the six
neighbours `₂F₁(a±1,b;c)`, `₂F₁(a,b±1;c)`, `₂F₁(a,b;c±1)` as a rational combination of
`F` and two of its neighbours. Together they say that the whole contiguous class
`{₂F₁(a+i,b+j;c+k;z)}` lies in the `ℚ(z)`-span of `F` and `F′` — the hypergeometric
analogue of the `Γ` class `{Γ(x+n)}ₙ`.
-/

open scoped Topology ENNReal

namespace Pconstructible

noncomputable section

/-! ### The shifted ascending factorial

`ascPochhammer_succ_eval` reads `(a)_{n+1} = (a)_n (a+n)`, stepping the *index* up at fixed
parameter. The derivative identity needs the other factorisation, `(a)_{n+1} = a (a+1)_n`,
which steps the *parameter* up at fixed index. It is the composition form
`ascPochhammer_succ_left` of the ascending factorial evaluated at `a`. -/

/-- `(a)_{n+1} = a (a+1)_n`: the ascending factorial with the parameter shifted up. -/
-- Theorem: `(ascPochhammer ℝ (n+1)).eval a = a * (ascPochhammer ℝ n).eval (a + 1)`.
lemma ascPochhammer_succ_eval_left (a : ℝ) (n : ℕ) :
    (ascPochhammer ℝ (n + 1)).eval a = a * (ascPochhammer ℝ n).eval (a + 1) := by
  rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]

/-! ### The derivative coefficient identity

Termwise differentiation multiplies the `n`-th coefficient of `₂F₁(a,b;c;·)` by `n`, i.e. it
sends `hypCoeff a b c (n+1)` to `(n+1) · hypCoeff a b c (n+1)`. The factorial ratio
`(a)_{n+1}(b)_{n+1}/(c)_{n+1}` factors as `(ab/c)` times
`(a+1)_n (b+1)_n / (c+1)_n`, which is exactly `(ab/c) · hypCoeff (a+1)(b+1)(c+1) n`. This
is DLMF 15.5.1 read off at the level of coefficients. -/

/-- The coefficient identity behind `d/dz ₂F₁(a,b;c;·) = (ab/c) ₂F₁(a+1,b+1;c+1;·)`:
`(n+1) · hypCoeff a b c (n+1) = (a b / c) · hypCoeff (a+1) (b+1) (c+1) n`.

It holds unconditionally, including when `c = 0`: both sides are then `0` because `(c)_1 = 0`
on the left and `a b / 0 = 0` in `ℝ` on the right. -/
-- Theorem: `(n+1) * hypCoeff a b c (n+1) = (a*b/c) * hypCoeff (a+1) (b+1) (c+1) n`.
lemma hypCoeff_succ_mul (a b c : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * hypCoeff a b c (n + 1)
      = a * b / c * hypCoeff (a + 1) (b + 1) (c + 1) n := by
  unfold hypCoeff ordinaryHypergeometricCoefficient
  rw [ascPochhammer_succ_eval_left a n, ascPochhammer_succ_eval_left b n,
    ascPochhammer_succ_eval_left c n]
  rw [mul_inv]
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp
  push_cast
  ring

/-! ### The derivative (DLMF 15.5.1)

`hyp a b c` is the sum of its power series, so it is analytic on the open unit disc. The
`n`-th coefficient of the derivative series is `(n+1) · hypCoeff a b c (n+1)`, which
`hypCoeff_succ_mul` rewrites as `(a b / c) · hypCoeff (a+1) (b+1) (c+1) n`. That is exactly
the `n`-th coefficient of `(a b / c) · ₂F₁(a+1,b+1;c+1;·)`, so the two functions agree on
the disc.

The radius bookkeeping is the same as in `hasSum_hyp`: the radius of
`ordinaryHypergeometricSeries` is `1` unless one of `a`, `b` is a nonpositive integer, in
which case it is `⊤`. -/
/-- The radius of `ordinaryHypergeometricSeries ℝ a b c` is at least `1` when `c` is not a
nonpositive integer. -/
-- Theorem: `1 ≤ (ordinaryHypergeometricSeries ℝ a b c).radius` for `c ∉ -ℕ`.
lemma one_le_hypergeometric_radius {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    (1 : ℝ≥0∞) ≤ (ordinaryHypergeometricSeries ℝ a b c).radius := by
  by_cases ha : ∃ k : ℕ, a = -(k : ℝ)
  · obtain ⟨k, rfl⟩ := ha
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₁]
    exact le_top
  · by_cases hb : ∃ k : ℕ, b = -(k : ℝ)
    · obtain ⟨k, rfl⟩ := hb
      rw [ordinaryHypergeometric_radius_top_of_neg_nat₂]
      exact le_top
    · push Not at ha hb
      have habc : ∀ kn : ℕ, (kn : ℝ) ≠ -a ∧ (kn : ℝ) ≠ -b ∧ (kn : ℝ) ≠ -c := by
        intro kn
        refine ⟨?_, ?_, ?_⟩ <;> intro hcon
        · exact ha kn (by linarith)
        · exact hb kn (by linarith)
        · exact hc kn (by linarith)
      rw [ordinaryHypergeometricSeries_radius_eq_one (𝔸 := ℝ) a b c habc]

/-- The derivative series of `₂F₁(a,b;c;·)`: for `|z| < 1`,
`deriv (₂F₁(a,b;c;·)) z = ∑ₙ (n+1) · hypCoeff a b c (n+1) · zⁿ`.

This is the termwise derivative of the hypergeometric power series, obtained from
`HasFPowerSeriesOnBall.fderiv`; the value `deriv f z` is `fderiv ℝ f z 1`, so each
continuous linear map in the derivative series is evaluated at `1`. -/
-- Theorem: `HasSum (fun n => (n+1) * hypCoeff a b c (n+1) * z^n) (deriv (hyp a b c) z)`.
theorem hasSum_deriv_hyp {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz : |z| < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * hypCoeff a b c (n + 1) * z ^ n)
      (deriv (fun w => hyp a b c w) z) := by
  have hrad : (1 : ℝ≥0∞) ≤ (ordinaryHypergeometricSeries ℝ a b c).radius :=
    one_le_hypergeometric_radius hc
  have hpos : 0 < (ordinaryHypergeometricSeries ℝ a b c).radius :=
    lt_of_lt_of_le (by norm_num) hrad
  have hz1 : (‖z‖ₑ : ℝ≥0∞) < 1 := by
    rw [enorm_eq_nnnorm]
    simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact hz
  have hmem : z ∈ Metric.eball (0 : ℝ) (ordinaryHypergeometricSeries ℝ a b c).radius := by
    rw [mem_eball_zero_iff]
    exact lt_of_lt_of_le hz1 hrad
  have hps : HasFPowerSeriesOnBall (fun w => hyp a b c w)
      (ordinaryHypergeometricSeries ℝ a b c) 0 (ordinaryHypergeometricSeries ℝ a b c).radius :=
    (ordinaryHypergeometricSeries ℝ a b c).hasFPowerSeriesOnBall hpos
  have hmap := (hps.fderiv.hasSum hmem).map (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
    (ContinuousLinearMap.continuous _)
  have hterm : ∀ n : ℕ,
      (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
          ((ordinaryHypergeometricSeries ℝ a b c).derivSeries n (fun _ => z))
        = ((n : ℝ) + 1) * hypCoeff a b c (n + 1) * z ^ n := by
    intro n
    rw [ContinuousLinearMap.apply_apply, FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp only [smul_apply, FormalMultilinearSeries.derivSeries_coeff_one,
      FormalMultilinearSeries.coeff_ofScalars, ordinaryHypergeometricSeries, smul_eq_mul]
    ring
  have hsum_eq : (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
      ((fderiv ℝ (fun w => hyp a b c w)) (0 + z))
        = deriv (fun w => hyp a b c w) z := by
    rw [ContinuousLinearMap.apply_apply, zero_add, fderiv_apply_one_eq_deriv]
  rw [hsum_eq] at hmap
  exact hmap.congr_fun fun n => (hterm n).symm

/-- **DLMF 15.5.1**: `d/dz ₂F₁(a,b;c;z) = (a b / c) ₂F₁(a+1,b+1;c+1;z)` on `|z| < 1`.

The two hypotheses on `c` are what the two series involved need to converge to their
`tsum` definitions: `c ∉ -ℕ` for `hyp a b c` and `c + 1 ∉ -ℕ` for
`hyp (a+1) (b+1) (c+1)`. `c ≠ 0` follows from the first at `n = 0`. -/
-- Theorem: `deriv (hyp a b c) z = (a*b/c) * hyp (a+1) (b+1) (c+1) z`.
theorem hyp_deriv {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hc1 : ∀ n : ℕ, c + 1 ≠ -(n : ℝ)) {z : ℝ} (hz : |z| < 1) :
    deriv (fun w => hyp a b c w) z = (a * b / c) * hyp (a + 1) (b + 1) (c + 1) z := by
  have hderiv := hasSum_deriv_hyp (a := a) (b := b) (c := c) hc hz
  have hrhs := (hasSum_hyp (a := a + 1) (b := b + 1) (c := c + 1) hz hc1).mul_left (a * b / c)
  refine hderiv.unique (hrhs.congr_fun fun n => ?_)
  rw [hypCoeff_succ_mul]
  ring

/-! ### The contiguous relation in `a` and `b` (DLMF 15.5.12)

`(b - a) ₂F₁(a,b;c;z) + a ₂F₁(a+1,b;c;z) - b ₂F₁(a,b+1;c;z) = 0`.

This is the simplest of the contiguous relations: it contains no shift of the argument, so
it is a *pure* coefficient identity. Writing `A = (a)ₙ`, `A₁ = (a+1)ₙ`, `B = (b)ₙ`,
`B₁ = (b+1)ₙ` and using the two factorisations of the ascending factorial
`a A₁ = (a+n) A` and `b B₁ = (b+n) B`, the numerator
`(b-a) A B + a A₁ B - b A B₁` collapses to `A B [(b-a) + (a+n) - (b+n)] = 0`. Every
`hyp a b c n` carries the same factor `(n!)⁻¹ ((c)ₙ)⁻¹`, so the identity is unconditional
in `c`. -/

/-- The ascending-factorial identity `a (a+1)ₙ = (a+n) (a)ₙ` behind the contiguous
relations in `a`. -/
-- Theorem: `a * (ascPochhammer ℝ n).eval (a+1) = (a+n) * (ascPochhammer ℝ n).eval a`.
lemma mul_ascPochhammer_succ (a : ℝ) (n : ℕ) :
    a * (ascPochhammer ℝ n).eval (a + 1) = (a + n) * (ascPochhammer ℝ n).eval a := by
  rw [← ascPochhammer_succ_eval_left, ascPochhammer_succ_eval]
  ring

/-- The coefficient form of DLMF 15.5.12:
`(b-a) cₙ + a c'ₙ - b c''ₙ = 0`, where `c'`, `c''` are the coefficients of
`₂F₁(a+1,b;c;·)` and `₂F₁(a,b+1;c;·)`. -/
-- Theorem: `(b-a) * hypCoeff a b c n + a * hypCoeff (a+1) b c n
--   - b * hypCoeff a (b+1) c n = 0`.
lemma hypCoeff_contiguous_ab (a b c : ℝ) (n : ℕ) :
    (b - a) * hypCoeff a b c n + a * hypCoeff (a + 1) b c n
      - b * hypCoeff a (b + 1) c n = 0 := by
  have ha := mul_ascPochhammer_succ a n
  have hb := mul_ascPochhammer_succ b n
  unfold hypCoeff ordinaryHypergeometricCoefficient
  linear_combination
    ((n.factorial : ℝ)⁻¹ * ((ascPochhammer ℝ n).eval c)⁻¹) *
      ((ascPochhammer ℝ n).eval b * ha - (ascPochhammer ℝ n).eval a * hb)

/-- **DLMF 15.5.12**: `(b-a) ₂F₁(a,b;c;z) + a ₂F₁(a+1,b;c;z) - b ₂F₁(a,b+1;c;z) = 0`
on `|z| < 1`. -/
-- Theorem: `(b-a) * hyp a b c z + a * hyp (a+1) b c z - b * hyp a (b+1) c z = 0`.
theorem hyp_contiguous_ab {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz : |z| < 1) :
    (b - a) * hyp a b c z + a * hyp (a + 1) b c z - b * hyp a (b + 1) c z = 0 := by
  have h1 := hasSum_hyp (a := a) (b := b) (c := c) hz hc
  have h2 := hasSum_hyp (a := a + 1) (b := b) (c := c) hz hc
  have h3 := hasSum_hyp (a := a) (b := b + 1) (c := c) hz hc
  have hcomb := ((h1.mul_left (b - a)).add (h2.mul_left a)).sub (h3.mul_left b)
  refine (hcomb.congr_fun fun n => ?_).unique hasSum_zero
  have h := hypCoeff_contiguous_ab a b c n
  have hz' : (b - a) * (hypCoeff a b c n * z ^ n) + a * (hypCoeff (a + 1) b c n * z ^ n)
      - b * (hypCoeff a (b + 1) c n * z ^ n) = 0 := by
    rw [show (b - a) * (hypCoeff a b c n * z ^ n) + a * (hypCoeff (a + 1) b c n * z ^ n)
        - b * (hypCoeff a (b + 1) c n * z ^ n)
      = ((b - a) * hypCoeff a b c n + a * hypCoeff (a + 1) b c n
          - b * hypCoeff a (b + 1) c n) * z ^ n from by ring]
    rw [h, zero_mul]
  exact hz'.symm

/-- `hyp` is symmetric in its two numerator parameters, because the hypergeometric series
is. -/
-- Theorem: `hyp a b c z = hyp b a c z`.
theorem hyp_comm (a b c z : ℝ) : hyp a b c z = hyp b a c z := by
  change (ordinaryHypergeometricSeries ℝ a b c).sum z
    = (ordinaryHypergeometricSeries ℝ b a c).sum z
  rw [ordinaryHypergeometricSeries_symm]

/-- **DLMF 15.5.12**, transposed: `(a-b) ₂F₁(a,b;c;z) + b ₂F₁(b+1,a;c;z)
- a ₂F₁(b,a+1;c;z) = 0`, the same relation with `a` and `b` exchanged and `hyp_comm` used to
bring the middle `₂F₁(b,a;c;z)` back to `₂F₁(a,b;c;z)`. -/
-- Theorem: `(a-b) * hyp a b c z + b * hyp (b+1) a c z - a * hyp b (a+1) c z = 0`.
theorem hyp_contiguous_ba {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz : |z| < 1) :
    (a - b) * hyp a b c z + b * hyp (b + 1) a c z - a * hyp b (a + 1) c z = 0 := by
  have h := hyp_contiguous_ab (a := b) (b := a) (c := c) hc hz
  rwa [hyp_comm b a c z] at h

/-! ### The contiguous relation in `a` and `c` (DLMF 15.5.15)

`(c - a - 1) ₂F₁(a,b;c;z) + a ₂F₁(a+1,b;c;z) - (c-1) ₂F₁(a,b;c-1;z) = 0`.

Still a pure coefficient identity, but now the third term has a shifted `c`, so its
coefficient is `(n!)⁻¹ (a)ₙ (b)ₙ ((c-1)ₙ)⁻¹`. The needed ascending-factorial identity is
`(c-1) (c)ₙ = (c-1)ₙ (c+n-1)`, again a consequence of the two factorisations of `(c-1)_{n+1}`.
Multiplying the coefficient identity through by `(c)ₙ (c-1)ₙ` clears the `c` dependence.

The extra hypothesis `c - 1 ∉ -ℕ` is what `₂F₁(a,b;c-1;·)` needs to converge to its power
series; `c ∉ -ℕ` handles the other two terms. -/

/-- The ascending-factorial identity `(c-1) (c)ₙ = (c-1)ₙ (c+n-1)` behind the contiguous
relations in `c`. -/
-- Theorem: `(c-1) * (ascPochhammer ℝ n).eval c
--   = (ascPochhammer ℝ n).eval (c-1) * (c+n-1)`.
lemma mul_ascPochhammer_pred (c : ℝ) (n : ℕ) :
    (c - 1) * (ascPochhammer ℝ n).eval c
      = (ascPochhammer ℝ n).eval (c - 1) * (c + n - 1) := by
  have h1 : (ascPochhammer ℝ (n + 1)).eval (c - 1)
      = (c - 1) * (ascPochhammer ℝ n).eval c := by
    rw [ascPochhammer_succ_eval_left, sub_add_cancel]
  have h2 : (ascPochhammer ℝ (n + 1)).eval (c - 1)
      = (ascPochhammer ℝ n).eval (c - 1) * (c + n - 1) := by
    rw [ascPochhammer_succ_eval]
    ring
  rw [← h1, h2]

/-- The coefficient form of DLMF 15.5.15, under the two nonvanishing conditions that
`c ∉ -ℕ` and `c - 1 ∉ -ℕ` supply. -/
-- Theorem: `(c-a-1) * hypCoeff a b c n + a * hypCoeff (a+1) b c n
--   - (c-1) * hypCoeff a b (c-1) n = 0` when `(c)ₙ ≠ 0` and `(c-1)ₙ ≠ 0`.
lemma hypCoeff_contiguous_c (a b c : ℝ) (n : ℕ)
    (hC : (ascPochhammer ℝ n).eval c ≠ 0)
    (hCm : (ascPochhammer ℝ n).eval (c - 1) ≠ 0) :
    (c - a - 1) * hypCoeff a b c n + a * hypCoeff (a + 1) b c n
      - (c - 1) * hypCoeff a b (c - 1) n = 0 := by
  have ha := mul_ascPochhammer_succ a n
  have hc' := mul_ascPochhammer_pred c n
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  unfold hypCoeff ordinaryHypergeometricCoefficient
  field_simp
  linear_combination
    ((ascPochhammer ℝ n).eval b * (ascPochhammer ℝ n).eval (c - 1) * ha
      - (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b * hc')

/-- **DLMF 15.5.15**: `(c-a-1) ₂F₁(a,b;c;z) + a ₂F₁(a+1,b;c;z)
- (c-1) ₂F₁(a,b;c-1;z) = 0` on `|z| < 1`. -/
-- Theorem: `(c-a-1) * hyp a b c z + a * hyp (a+1) b c z - (c-1) * hyp a b (c-1) z = 0`.
theorem hyp_contiguous_c {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hcm : ∀ n : ℕ, c - 1 ≠ -(n : ℝ)) (hz : |z| < 1) :
    (c - a - 1) * hyp a b c z + a * hyp (a + 1) b c z
      - (c - 1) * hyp a b (c - 1) z = 0 := by
  have h1 := hasSum_hyp (a := a) (b := b) (c := c) hz hc
  have h2 := hasSum_hyp (a := a + 1) (b := b) (c := c) hz hc
  have h3 := hasSum_hyp (a := a) (b := b) (c := c - 1) hz hcm
  have hcomb := ((h1.mul_left (c - a - 1)).add (h2.mul_left a)).sub (h3.mul_left (c - 1))
  refine (hcomb.congr_fun fun n => ?_).unique hasSum_zero
  have hCn : (ascPochhammer ℝ n).eval c ≠ 0 := by
    intro h0
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n c).1 h0
    exact hc k (by linarith)
  have hCmn : (ascPochhammer ℝ n).eval (c - 1) ≠ 0 := by
    intro h0
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n (c - 1)).1 h0
    exact hcm k (by linarith)
  have h := hypCoeff_contiguous_c a b c n hCn hCmn
  have hz' : (c - a - 1) * (hypCoeff a b c n * z ^ n) + a * (hypCoeff (a + 1) b c n * z ^ n)
      - (c - 1) * (hypCoeff a b (c - 1) n * z ^ n) = 0 := by
    rw [show (c - a - 1) * (hypCoeff a b c n * z ^ n)
          + a * (hypCoeff (a + 1) b c n * z ^ n)
          - (c - 1) * (hypCoeff a b (c - 1) n * z ^ n)
      = ((c - a - 1) * hypCoeff a b c n + a * hypCoeff (a + 1) b c n
          - (c - 1) * hypCoeff a b (c - 1) n) * z ^ n from by ring]
    rw [h, zero_mul]
  exact hz'.symm

/-! ### Shifting the argument by one factor of `z`

Several contiguous relations contain `z ₂F₁` rather than `₂F₁`, and so are not pure coefficient
identities. Multiplying a power series by `z` shifts its coefficient sequence:
`z · ∑ₙ gₙ zⁿ = ∑ₙ g_{n-1} zⁿ`, where the `n = 0` coefficient is `0`. `hasSum_mul_z_shift`
packages this, so that a relation carrying a factor `z` can still be checked coefficientwise. -/

/-- Multiplying a power series by its variable shifts the coefficient sequence: if `∑ₙ gₙ zⁿ`
has sum `G`, then `∑ₙ (n = 0 ? 0 : g_{n-1}) zⁿ` has sum `G z`. -/
-- Theorem: `HasSum (fun n => (if n = 0 then 0 else g (n - 1)) * z ^ n) (G * z)`.
lemma hasSum_mul_z_shift {g : ℕ → ℝ} {z G : ℝ}
    (h : HasSum (fun n : ℕ => g n * z ^ n) G) :
    HasSum (fun n : ℕ => (if n = 0 then 0 else g (n - 1)) * z ^ n) (G * z) := by
  have h1 : HasSum (fun n : ℕ => g n * z ^ (n + 1)) (G * z) :=
    (h.mul_right z).congr_fun fun n => by rw [pow_succ, mul_assoc]
  have h2 : HasSum (fun n : ℕ => (if n + 1 = 0 then 0 else g (n + 1 - 1)) * z ^ (n + 1))
      (G * z) :=
    h1.congr_fun fun n => by simp
  have h3 := (hasSum_nat_add_iff 1
    (f := fun n : ℕ => (if n = 0 then 0 else g (n - 1)) * z ^ n)).1 h2
  simpa using h3

/-! ### The contiguous relation in `b` and `c` (DLMF 15.5.13)

`(c - a - b) ₂F₁(a,b;c;z) + a(1 - z) ₂F₁(a+1,b;c;z) - (c - b) ₂F₁(a,b-1;c;z) = 0`.

Unlike (15.5.12) the second term carries a factor `1 - z`, so this is no longer a pure
coefficient identity: the coefficient of `zⁿ` in `z ₂F₁(a+1,b;c;z)` is the coefficient of
`z^{n-1}` in `₂F₁(a+1,b;c;z)`, and `hasSum_mul_z_shift` supplies exactly that shift. Writing
`A = (a)ₙ`, `B = (b)ₙ`, `C = (c)ₙ`, the surviving numerator identity is
`A[(c-a-b)(b+n-1) + (a+n)(b+n-1) - n(c+n-1) - (c-b)(b-1)] = 0`, and the bracket collapses to
`(b+n-1)(c-b+n) - n(c+n-1) - (c-b)(b-1) = 0`. -/

/-- The coefficient identity behind DLMF 15.5.13. For `n = 0` the `z`-shifted term is absent;
for `n = m + 1` the shift contributes `hypCoeff (a+1) b c m`. -/
-- Theorem: `(c-a-b) * hypCoeff a b c n + a * hypCoeff (a+1) b c n
--   - a * (if n = 0 then 0 else hypCoeff (a+1) b c (n-1))
--   - (c-b) * hypCoeff a (b-1) c n = 0` for `c ∉ -ℕ`.
lemma hypCoeff_contiguous_13 (a b c : ℝ) (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (n : ℕ) :
    (c - a - b) * hypCoeff a b c n + a * hypCoeff (a + 1) b c n
      - a * (if n = 0 then 0 else hypCoeff (a + 1) b c (n - 1))
      - (c - b) * hypCoeff a (b - 1) c n = 0 := by
  cases n with
  | zero => simp [hypCoeff, ordinaryHypergeometricCoefficient]; ring
  | succ m =>
    have hfact : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hC1 : (ascPochhammer ℝ (m + 1)).eval c ≠ 0 := by
      intro h0
      obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff (m + 1) c).1 h0
      exact hc k (by linarith)
    have hC : (ascPochhammer ℝ m).eval c ≠ 0 := by
      rw [ascPochhammer_succ_eval] at hC1
      exact (mul_ne_zero_iff.mp hC1).1
    have hcm : c + m ≠ 0 := by
      rw [ascPochhammer_succ_eval] at hC1
      exact (mul_ne_zero_iff.mp hC1).2
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    unfold hypCoeff ordinaryHypergeometricCoefficient
    rw [ascPochhammer_succ_eval_left a m, ascPochhammer_succ_eval m (a + 1),
      ascPochhammer_succ_eval m b, ascPochhammer_succ_eval m c,
      ascPochhammer_succ_eval_left (b - 1) m, sub_add_cancel, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, if_neg (Nat.succ_ne_zero m),
      Nat.add_sub_cancel]
    field_simp
    ring

/-- **DLMF 15.5.13**: `(c-a-b) ₂F₁(a,b;c;z) + a(1-z) ₂F₁(a+1,b;c;z)
- (c-b) ₂F₁(a,b-1;c;z) = 0` on `|z| < 1`. -/
-- Theorem: `(c-a-b) * hyp a b c z + a * (1-z) * hyp (a+1) b c z
--   - (c-b) * hyp a (b-1) c z = 0`.
theorem hyp_contiguous_13 {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz : |z| < 1) :
    (c - a - b) * hyp a b c z + a * (1 - z) * hyp (a + 1) b c z
      - (c - b) * hyp a (b - 1) c z = 0 := by
  have h1 := hasSum_hyp (a := a) (b := b) (c := c) hz hc
  have h2 := hasSum_hyp (a := a + 1) (b := b) (c := c) hz hc
  have h3 := hasSum_hyp (a := a) (b := b - 1) (c := c) hz hc
  have hz2 := hasSum_mul_z_shift h2
  have hcomb := (((h1.mul_left (c - a - b)).add (h2.mul_left a)).sub
    (hz2.mul_left a)).sub (h3.mul_left (c - b))
  have hz0 : (c - a - b) * hyp a b c z + a * hyp (a + 1) b c z
      - a * (hyp (a + 1) b c z * z) - (c - b) * hyp a (b - 1) c z = 0 :=
    (hcomb.congr_fun fun n => by
      have h := hypCoeff_contiguous_13 a b c hc n
      have hz' : (c - a - b) * (hypCoeff a b c n * z ^ n)
          + a * (hypCoeff (a + 1) b c n * z ^ n)
          - a * ((if n = 0 then 0 else hypCoeff (a + 1) b c (n - 1)) * z ^ n)
          - (c - b) * (hypCoeff a (b - 1) c n * z ^ n) = 0 := by
        rw [show (c - a - b) * (hypCoeff a b c n * z ^ n)
              + a * (hypCoeff (a + 1) b c n * z ^ n)
              - a * ((if n = 0 then 0 else hypCoeff (a + 1) b c (n - 1)) * z ^ n)
              - (c - b) * (hypCoeff a (b - 1) c n * z ^ n)
            = ((c - a - b) * hypCoeff a b c n + a * hypCoeff (a + 1) b c n
              - a * (if n = 0 then 0 else hypCoeff (a + 1) b c (n - 1))
              - (c - b) * hypCoeff a (b - 1) c n) * z ^ n from by ring]
        rw [h, zero_mul]
      exact hz'.symm).unique hasSum_zero
  calc (c - a - b) * hyp a b c z + a * (1 - z) * hyp (a + 1) b c z
        - (c - b) * hyp a (b - 1) c z
      = (c - a - b) * hyp a b c z + a * hyp (a + 1) b c z
        - a * (hyp (a + 1) b c z * z) - (c - b) * hyp a (b - 1) c z := by ring
    _ = 0 := hz0

/-! ### The derivative identity in `c` (DLMF 15.5.21)

`c (1 - z) ₂F₁′(a,b;c;z) = (c-a)(c-b) ₂F₁(a,b;c+1;z) + c(a+b-c) ₂F₁(a,b;c;z)`.

Multiplying by `z` lowers the coefficient index and differentiating raises it, so the `zⁿ`
coefficient on the left is `c(n+1) c_{n+1} - c n c_n`, with `c_k := hypCoeff a b c k`. On
the right the shifted-parameter term has coefficient `d_n := c/(c+n) · c_n`, and the
identity reduces to `(a+n)(b+n) - n(c+n) = (c-a)(c-b) + (a+b-c)(c+n)`. -/

/-- `c (c+1)ₙ = (c)ₙ (c+n)`: the ascending factorial with the parameter shifted up, in the
product form that avoids division. -/
-- Theorem: `c * (ascPochhammer ℝ n).eval (c+1) = (ascPochhammer ℝ n).eval c * (c+n)`.
lemma mul_ascPochhammer_eval_add_one (c : ℝ) (n : ℕ) :
    c * (ascPochhammer ℝ n).eval (c + 1)
      = (ascPochhammer ℝ n).eval c * (c + n) := by
  rw [← ascPochhammer_succ_eval_left, ascPochhammer_succ_eval]

/-- The shifted-parameter coefficient ratio `hypCoeff a b (c+1) n = c/(c+n) · hypCoeff a b c n`,
under the nonvanishing conditions `c ≠ 0`, `(c)ₙ ≠ 0`, `c+n ≠ 0` that `c ∉ -ℕ` supplies. -/
-- Theorem: `hypCoeff a b (c+1) n = c/(c+n) * hypCoeff a b c n`.
lemma hypCoeff_succ_c (a b c : ℝ) (hc0 : c ≠ 0) (n : ℕ)
    (hCn : (ascPochhammer ℝ n).eval c ≠ 0) (hcn : c + n ≠ 0) :
    hypCoeff a b (c + 1) n = c / (c + n) * hypCoeff a b c n := by
  have hrel := mul_ascPochhammer_eval_add_one c n
  have hsub : (ascPochhammer ℝ n).eval (c + 1)
      = (ascPochhammer ℝ n).eval c * (c + (n : ℝ)) / c := by
    rw [eq_div_iff hc0, mul_comm]
    exact hrel
  have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  unfold hypCoeff ordinaryHypergeometricCoefficient
  rw [hsub]
  field_simp

/-- The coefficient identity behind DLMF 15.5.21: for every `n`,
`c(n+1) c_{n+1} - c n c_n = (c-a)(c-b) d_n + c(a+b-c) c_n`, where
`d_n = hypCoeff a b (c+1) n`. -/
-- Theorem: `c * ((n+1) * hypCoeff a b c (n+1)) - c * (n * hypCoeff a b c n)
--   = (c-a)*(c-b)*hypCoeff a b (c+1) n + c*(a+b-c)*hypCoeff a b c n`.
lemma hypCoeff_contiguous_21 (a b c : ℝ) (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (n : ℕ) :
    c * (((n : ℝ) + 1) * hypCoeff a b c (n + 1))
      - c * ((n : ℝ) * hypCoeff a b c n)
      = (c - a) * (c - b) * hypCoeff a b (c + 1) n
        + c * (a + b - c) * hypCoeff a b c n := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  rcases n with _ | m
  · simp only [Nat.cast_zero, zero_add, zero_mul]
    unfold hypCoeff ordinaryHypergeometricCoefficient
    simp [ascPochhammer_zero, ascPochhammer_one]
    field_simp
    ring
  · have hCm : (ascPochhammer ℝ (m + 1)).eval c ≠ 0 := by
      intro h0
      obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff (m + 1) c).1 h0
      exact hc k (by linarith)
    have hcm : c + ((m + 1 : ℕ) : ℝ) ≠ 0 := by
      intro h0
      exact hc (m + 1) (by linarith)
    have hcm' : ((m + 1 : ℕ) : ℝ) + c ≠ 0 := by
      rw [add_comm]
      exact hcm
    have hK1 : ((m + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    have hcoef := hypCoeff_succ_c a b c hc0 (m + 1) hCm hcm
    rw [hypCoeff_succ a b c (m + 1), hcoef]
    field_simp
    ring

/-- **DLMF 15.5.21**: `c (1 - z) ₂F₁′(a,b;c;z) = (c-a)(c-b) ₂F₁(a,b;c+1;z)
+ c(a+b-c) ₂F₁(a,b;c;z)` on `|z| < 1`. -/
-- Theorem: `c * (1 - z) * deriv (fun w => hyp a b c w) z
--   = (c-a)*(c-b)*hyp a b (c+1) z + c*(a+b-c)*hyp a b c z`.
theorem hyp_contiguous_21 {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hc1 : ∀ n : ℕ, c + 1 ≠ -(n : ℝ)) (hz : |z| < 1) :
    c * (1 - z) * deriv (fun w => hyp a b c w) z
      = (c - a) * (c - b) * hyp a b (c + 1) z + c * (a + b - c) * hyp a b c z := by
  have hderiv := hasSum_deriv_hyp (a := a) (b := b) (c := c) hc hz
  have hshift := hasSum_mul_z_shift hderiv
  have hshift' : HasSum (fun n : ℕ => ((n : ℝ) * hypCoeff a b c n) * z ^ n)
      (deriv (fun w => hyp a b c w) z * z) :=
    hshift.congr_fun fun n => by
      cases n with
      | zero => simp
      | succ m => simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]; push_cast; ring
  have hL := (hderiv.mul_left c).sub (hshift'.mul_left c)
  have hR1 := hasSum_hyp (a := a) (b := b) (c := c + 1) hz hc1
  have hR2 := hasSum_hyp (a := a) (b := b) (c := c) hz hc
  have hR := (hR1.mul_left ((c - a) * (c - b))).add (hR2.mul_left (c * (a + b - c)))
  have hR' : HasSum
      (fun n : ℕ => c * (((n : ℝ) + 1) * hypCoeff a b c (n + 1) * z ^ n)
        - c * (((n : ℝ) * hypCoeff a b c n) * z ^ n))
      ((c - a) * (c - b) * hyp a b (c + 1) z + c * (a + b - c) * hyp a b c z) :=
    hR.congr_fun fun n => by
    have h := hypCoeff_contiguous_21 a b c hc n
    rw [show c * (((n : ℝ) + 1) * hypCoeff a b c (n + 1) * z ^ n)
          - c * (((n : ℝ) * hypCoeff a b c n) * z ^ n)
        = (c * (((n : ℝ) + 1) * hypCoeff a b c (n + 1))
            - c * ((n : ℝ) * hypCoeff a b c n)) * z ^ n from by ring]
    rw [show (c - a) * (c - b) * (hypCoeff a b (c + 1) n * z ^ n)
          + c * (a + b - c) * (hypCoeff a b c n * z ^ n)
        = ((c - a) * (c - b) * hypCoeff a b (c + 1) n
            + c * (a + b - c) * hypCoeff a b c n) * z ^ n from by ring]
    rw [h]
  calc c * (1 - z) * deriv (fun w => hyp a b c w) z
      = c * deriv (fun w => hyp a b c w) z
        - c * (deriv (fun w => hyp a b c w) z * z) := by ring
    _ = (c - a) * (c - b) * hyp a b (c + 1) z + c * (a + b - c) * hyp a b c z :=
        hL.unique hR'

end

end Pconstructible
