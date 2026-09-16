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
-- `OrdinaryHypergeometric` supplies `ordinaryHypergeometric` and its power series;
-- `Binomial` the series for `(1 + x) ^ a`, which is what the elementary cases reduce to.
import Pptc.Basic
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Pptc.Hypergeometric.Basic

The shared API for the Gauss hypergeometric function `₂F₁(a, b; c; z)` over the reals,
together with its elementary closed forms.

Everything downstream in the hypergeometric programme codes against the names declared
here, so the interface is deliberately small and fixed: an abbreviation `hyp`, the
coefficient `hypCoeff` and its two structural lemmas `hyp_eq_tsum_coeff` and
`hypCoeff_succ`, the summability statement `hasSum_hyp`, and the identification lemma
`hyp_eq_of_hasSum` that turns a coefficient computation into an identity for `hyp`.

## The junk-value trap

Mathlib's `ordinaryHypergeometric` is the sum of its power series and *nothing else*:
outside the disc of convergence the `tsum` silently returns `0`, and there is no
analytic continuation. Every statement below therefore carries `|z| < 1` (or is an
algebraic identity about the coefficients). For the same reason every statement about
`c` carries `∀ n, c ≠ -n`: a nonpositive integer `c` makes Mathlib's coefficients junk.

## Why the elementary cases are coefficient computations

`hyp_eq_of_hasSum` says that a function agreeing with the hypergeometric power series on
the open unit disc *is* `hyp`. So each elementary closed form (H1) follows by exhibiting
the closed form's own power series (`Real.one_add_rpow_hasFPowerSeriesOnBall_zero`, the
logarithm series, …) and matching coefficients against `hypCoeff` — no fresh analytic
argument on the hypergeometric side.
-/

open scoped Topology ENNReal

namespace Pconstructible

noncomputable section

/-- The Gauss hypergeometric function `₂F₁(a, b; c; z)` with real parameters and real
argument. An abbreviation for `ordinaryHypergeometric (𝕂 := ℝ)` so that statements
about it stay short; it is meaningless outside `|z| < 1` (see the module docstring). -/
abbrev hyp (a b c z : ℝ) : ℝ := ordinaryHypergeometric (𝕂 := ℝ) a b c z

/-- The `n`-th coefficient of the hypergeometric series for `hyp a b c`:
`(a)ₙ (b)ₙ / ((c)ₙ n!)`, i.e. Mathlib's `ordinaryHypergeometricCoefficient` over `ℝ`. -/
abbrev hypCoeff (a b c : ℝ) (n : ℕ) : ℝ :=
  ordinaryHypergeometricCoefficient (𝕂 := ℝ) a b c n

/-- `hyp a b c z` is the sum of its power series. This is `ordinaryHypergeometric_eq_tsum`
with the scalar action on `ℝ` written as multiplication. -/
-- Theorem: `₂F₁(a,b;c;z) = ∑ₙ hypCoeff a b c n * z ^ n` (as a `tsum`).
theorem hyp_eq_tsum_coeff (a b c z : ℝ) :
    hyp a b c z = ∑' n : ℕ, hypCoeff a b c n * z ^ n := by
  change (ordinaryHypergeometricSeries ℝ a b c).sum z = ∑' n : ℕ, hypCoeff a b c n * z ^ n
  simp only [FormalMultilinearSeries.sum, ordinaryHypergeometricSeries_apply_eq', smul_eq_mul]

/-- The series defining `hyp` converges to it on the open unit disc, whenever `c` is not a
nonpositive integer.

The radius of `ordinaryHypergeometricSeries` is `1` when none of `a`, `b`, `c` is a
nonpositive integer and `⊤` as soon as `a` or `b` is one (the series is then a
polynomial), so the assumption on `c` alone bounds the radius below by `1`. That is all
`|z| < 1` needs. -/
-- Theorem: for `|z| < 1` and `c` not a nonpositive integer, the hypergeometric series
-- `∑ₙ hypCoeff a b c n * z ^ n` has sum `hyp a b c z`.
theorem hasSum_hyp {a b c z : ℝ} (hz : |z| < 1) (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    HasSum (fun n : ℕ => hypCoeff a b c n * z ^ n) (hyp a b c z) := by
  have hrad : (1 : ℝ≥0∞) ≤ (ordinaryHypergeometricSeries ℝ a b c).radius := by
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
  have hz1 : (‖z‖ₑ : ℝ≥0∞) < 1 := by
    rw [enorm_eq_nnnorm]
    simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact hz
  have hmem : z ∈ Metric.eball (0 : ℝ) (ordinaryHypergeometricSeries ℝ a b c).radius := by
    rw [mem_eball_zero_iff]
    exact lt_of_lt_of_le hz1 hrad
  have h := (ordinaryHypergeometricSeries ℝ a b c).hasSum hmem
  simpa only [hyp_eq_tsum_coeff, FormalMultilinearSeries.sum,
    ordinaryHypergeometricSeries_apply_eq', smul_eq_mul, hypCoeff] using h

/-- The identification lemma for `₂F₁`: a function that agrees with the hypergeometric
power series on the open unit disc is `hyp`.

This is the workhorse of H1. To prove `f z = hyp a b c z` it suffices to produce a
`HasSum` of `fun n => hypCoeff a b c n * z ^ n` against `f z`; how the closed form's own
power series was obtained is irrelevant here. -/
-- Theorem: if `f` has the hypergeometric power series on `|z| < 1` (and `c ∉ -ℕ`), then
-- `f z = hyp a b c z` there.
theorem hyp_eq_of_hasSum {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    {f : ℝ → ℝ} (hf : ∀ ⦃z : ℝ⦄, |z| < 1 → HasSum (fun n : ℕ => hypCoeff a b c n * z ^ n) (f z)) :
    ∀ ⦃z : ℝ⦄, |z| < 1 → f z = hyp a b c z :=
  fun _ hz => (hf hz).unique (hasSum_hyp hz hc)

/-- The ratio of consecutive hypergeometric coefficients, the single fact that most
coefficient-level proofs reduce to.

The identity is unconditional: when a denominator vanishes both sides are `0`, because
`(c)ₙ = 0` forces `(c)_{n+1} = 0` and hence `hypCoeff (n + 1) = 0` as well. -/
-- Theorem: `hypCoeff a b c (n+1) = hypCoeff a b c n * (a+n)(b+n)/((c+n)(n+1))`.
theorem hypCoeff_succ (a b c : ℝ) (n : ℕ) :
    hypCoeff a b c (n + 1) = hypCoeff a b c n * ((a + n) * (b + n) / ((c + n) * (n + 1))) := by
  unfold hypCoeff ordinaryHypergeometricCoefficient
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  by_cases hR : (ascPochhammer ℝ n).eval c = 0
  · -- `(c)ₙ = 0` makes both sides vanish.
    simp [hR]
  · by_cases hcn : c + n = 0
    · -- `c + n = 0` makes `(c)_{n+1} = 0`, and the RHS denominator vanish.
      simp [hcn]
    · have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hRcn : (ascPochhammer ℝ n).eval c * (c + n) ≠ 0 := mul_ne_zero hR hcn
      field_simp

/-! ### Elementary closed forms (H1)

The four classical reductions of `₂F₁` to elementary functions. Each is proved through
`hyp_eq_of_hasSum`: exhibit the closed form's own power series (whose coefficients come
from `binomialSeries`/`ofScalars`, or from the logarithm, arctangent and arcsine series),
then match coefficients against `hypCoeff`. The side conditions (`b ∉ -ℕ` and the like)
are exactly what makes Mathlib's `(b)ₙ⁻¹` well behaved; see the junk-value trap in the
module docstring. -/

/-- The `n`-th binomial coefficient `Ring.choose (a + n - 1) n = (a)ₙ / n!`, the
coefficient in `(1 - x) ^ (-a) = ∑ₙ (a)ₙ/n! xⁿ`. Used to identify the `(1 - x) ^ (-a)`
power series with the `₂F₁(a, b; b)` series. -/
-- Theorem: `Ring.choose (a+n-1) n = (a)ₙ / n!`.
lemma ring_choose_eq_ascPochhammer (a : ℝ) (n : ℕ) :
    Ring.choose (a + n - 1) n = (ascPochhammer ℝ n).eval a * (n.factorial : ℝ)⁻¹ := by
  rw [Ring.choose_eq_smul, smul_eq_mul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]
  have harg : (a + (n : ℝ) - 1) - (n : ℝ) + 1 = a := by ring
  rw [harg]
  ring

/-- H1, first case: `₂F₁(a, b; b; z) = (1 - z) ^ (-a)` for `|z| < 1`. The `(b)ₙ` factors
cancel, reducing the hypergeometric series to the binomial series for `(1 - z) ^ (-a)`.

The hypothesis `b ∉ -ℕ` cannot be dropped: if `b` is a nonpositive integer then
Mathlib's `((b)ₙ)⁻¹` vanishes for large `n`, so the hypergeometric series is *not* the full
binomial series (the junk-value trap). -/
-- Theorem: `₂F₁(a, b; b; z) = (1 - z) ^ (-a)`.
theorem hyp_self_eq_rpow {a b z : ℝ} (hb : ∀ n : ℕ, b ≠ -(n : ℝ)) (hz : |z| < 1) :
    hyp a b b z = (1 - z) ^ (-a) := by
  have hban : ∀ n : ℕ, (ascPochhammer ℝ n).eval b ≠ 0 := by
    intro n h0
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n b).1 h0
    exact hb k (by linarith)
  refine (hyp_eq_of_hasSum (c := b) hb (f := fun w => (1 - w) ^ (-a)) ?_ hz).symm
  intro w hw
  have hmem : w ∈ Metric.eball (0 : ℝ) (1 : ℝ≥0∞) := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact hw
  have hbase := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum hmem
  have hterm : ∀ n : ℕ,
      (FormalMultilinearSeries.ofScalars ℝ fun k => Ring.choose (a + k - 1) k) n (fun _ => w)
        = hypCoeff a b b n * w ^ n := by
    intro n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    congr 1
    rw [ring_choose_eq_ascPochhammer]
    unfold hypCoeff ordinaryHypergeometricCoefficient
    rw [mul_inv_cancel_right₀ (hban n)]
    ring
  have hsum : (1 / (1 - w) ^ a) = (1 - w) ^ (-a) := by
    rw [one_div, ← Real.rpow_neg]
    linarith [(abs_lt.mp hw).2]
  rw [zero_add, hsum] at hbase
  exact hbase.congr_fun fun n => (hterm n).symm

/-- The coefficient of `₂F₁(1, 1; 2; ·)` is `1/(n+1)`: the two ascending factorials
`(1)ₙ = n!` cancel against the `n!` in the coefficient, and `(2)ₙ = (n+1)!`, leaving
`n!/(n+1)! = 1/(n+1)`. -/
-- Theorem: `hypCoeff 1 1 2 n = 1 / (n + 1)`.
lemma hypCoeff_one_one_two (n : ℕ) : hypCoeff 1 1 2 n = 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num [hypCoeff, ordinaryHypergeometricCoefficient]
  | succ n ih =>
    rw [hypCoeff_succ, ih]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- The coefficient of `₂F₁(1/2, 1; 3/2; ·)` is `1/(2n+1)`: `(1/2)ₙ/(3/2)ₙ = 1/(2n+1)`
and the `(1)ₙ = n!` cancels the `n!` in the coefficient. -/
-- Theorem: `hypCoeff (1/2) 1 (3/2) n = 1 / (2 n + 1)`.
lemma hypCoeff_half_one_three_half (n : ℕ) :
    hypCoeff (1 / 2) 1 (3 / 2) n = 1 / (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => norm_num [hypCoeff, ordinaryHypergeometricCoefficient]
  | succ n ih =>
    rw [hypCoeff_succ, ih]
    have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- H1, second case: `₂F₁(1, 1; 2; z) = -log(1 - z)/z` on `0 < |z| < 1`.

The coefficient identity `(1)ₙ²/((2)ₙ n!) = 1/(n+1)` turns the hypergeometric series into
`∑ₙ zⁿ/(n+1)`, which is the logarithm series `∑ₙ z^{n+1}/(n+1) = -log(1 - z)` divided by
`z`. The hypothesis `z ≠ 0` is essential: at `z = 0` the right-hand side is the junk
`0/0 = 0` while the left-hand side is `1`. Hence pointwise uniqueness rather than the
function-valued `hyp_eq_of_hasSum`. -/
-- Theorem: `₂F₁(1, 1; 2; z) = -log(1 - z) / z` for `z ≠ 0`, `|z| < 1`.
theorem hyp_one_one_two {z : ℝ} (hz0 : z ≠ 0) (hz : |z| < 1) :
    hyp 1 1 2 z = -Real.log (1 - z) / z := by
  have hc : ∀ n : ℕ, (2 : ℝ) ≠ -(n : ℝ) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsrc := (Real.hasSum_pow_div_log_of_abs_lt_one hz).div_const z
  refine (hasSum_hyp hz hc).unique (hsrc.congr_fun ?_)
  intro n
  rw [hypCoeff_one_one_two n, div_div, pow_succ]
  field_simp

/-- H1, third case: `₂F₁(1/2, 1; 3/2; -z²) = arctan z / z` on `0 < |z| < 1`.

Here `(1/2)ₙ/(3/2)ₙ = 1/(2n+1)`, so the series is `∑ₙ (-z²)ⁿ/(2n+1)`, and
`(-z²)ⁿ = (-1)ⁿ z^{2n}` makes this the arctangent series `∑ₙ (-1)ⁿ z^{2n+1}/(2n+1)`
divided by `z`. Again `z ≠ 0`, by the same `0/0` junk argument as in case B. -/
-- Theorem: `₂F₁(1/2, 1; 3/2; -z²) = arctan z / z` for `z ≠ 0`, `|z| < 1`.
theorem hyp_half_one_three_half {z : ℝ} (hz0 : z ≠ 0) (hz : |z| < 1) :
    hyp (1 / 2) 1 (3 / 2) (-(z ^ 2)) = Real.arctan z / z := by
  have hc : ∀ n : ℕ, (3 / 2 : ℝ) ≠ -(n : ℝ) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hzsq : |(-(z ^ 2))| < 1 := by
    have h := abs_lt.mp hz
    rw [abs_neg, abs_of_nonneg (sq_nonneg z)]
    nlinarith [h.1, h.2]
  have hx : ‖z‖ < 1 := by simpa using hz
  have hsrc := (Real.hasSum_arctan hx).div_const z
  refine (hasSum_hyp (a := 1 / 2) (b := 1) (c := 3 / 2) (z := -(z ^ 2)) hzsq hc).unique
    (hsrc.congr_fun ?_)
  intro n
  rw [hypCoeff_half_one_three_half n, neg_pow, div_div, ← pow_mul, pow_succ]
  push_cast
  field_simp

/-! ### PConstructible corollaries

Each closed form expresses `hyp` as an arithmetic combination of `log`, `arctan`, `arcsin`
and `rpow`, all of which `Pptc.Basic` already knows to be constructible. The hypotheses
`PConstructible z` and the domain restrictions (`|z| < 1`, `z ≠ 0`, `b ∉ -ℕ`) are exactly
the side conditions of the underlying closure lemmas, so these are registered as
conditional `pconstructible` rules. -/

set_option linter.unusedVariables false in
/-- The `(1 - z) ^ (-a)` closed form (H1 A) is P-constructible. -/
-- Theorem: `hyp a b b z` is P-constructible when `a`, `b`, `z` are and `b ∉ -ℕ`, `|z| < 1`.
@[pconstructible_cond]
theorem hyp_self_Pconstructible {a b z : ℝ} (ha : PConstructible a) (hb : PConstructible b)
    (hz : PConstructible z) (hbne : ∀ n : ℕ, b ≠ -(n : ℝ)) (hzabs : |z| < 1) :
    PConstructible (hyp a b b z) := by
  rw [hyp_self_eq_rpow hbne hzabs]
  have hpos : 0 < 1 - z := by linarith [(abs_lt.mp hzabs).2]
  exact rpow_Pconstructible (PConstructible.sub PConstructible.base_one hz)
    (neg_Pconstructible ha) hpos

/-- The `-log(1 - z)/z` closed form (H1 B) is P-constructible. -/
-- Theorem: `hyp 1 1 2 z` is P-constructible for P-constructible `z ≠ 0` with `|z| < 1`.
@[pconstructible_cond]
theorem hyp_one_one_two_Pconstructible {z : ℝ} (hz : PConstructible z) (hz0 : z ≠ 0)
    (hzabs : |z| < 1) : PConstructible (hyp 1 1 2 z) := by
  rw [hyp_one_one_two hz0 hzabs]
  have hpos : 0 < 1 - z := by linarith [(abs_lt.mp hzabs).2]
  exact PConstructible.div
    (neg_Pconstructible (log_Pconstructible (PConstructible.sub PConstructible.base_one hz) hpos))
    hz

/-- The `arctan z / z` closed form (H1 C) is P-constructible. -/
-- Theorem: `hyp (1/2) 1 (3/2) (-(z²))` is P-constructible for P-constructible `z ≠ 0`,
-- `|z| < 1`.
@[pconstructible_cond]
theorem hyp_half_one_three_half_Pconstructible {z : ℝ} (hz : PConstructible z) (hz0 : z ≠ 0)
    (hzabs : |z| < 1) : PConstructible (hyp (1 / 2) 1 (3 / 2) (-(z ^ 2))) := by
  rw [hyp_half_one_three_half hz0 hzabs]
  exact PConstructible.div (arctan_Pconstructible hz) hz

/-! ### H1, fourth case: `₂F₁(1/2, 1/2; 3/2; z²) = arcsin z / z`

Mathlib has no power series for `Real.arcsin`, so the closed form is not an immediate
instance of `hyp_eq_of_hasSum`. It is obtained instead by expanding
`1/√(1 - t²) = (1 - t²)^(-1/2)` with the binomial series
(`Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`) and integrating term by term
(`intervalIntegral.hasSum_integral_of_dominated_convergence`), which produces the classical
series `arcsin z = ∑ₙ C(2n,n)/(4ⁿ(2n+1)) z^{2n+1}`. Matching coefficients with
`hypCoeff` is then the coefficient identity proved first below. -/

/-- The central binomial coefficient in Pochhammer form: `(1/2)ₙ = C(2n,n) n! / 4ⁿ`.
This is what identifies the binomial-series coefficients of `1/√(1 - t²)` with the
coefficients of the arcsine series. -/
-- Theorem: `(ascPochhammer ℝ n).eval (1/2) = (Nat.choose (2*n) n : ℝ) * n! / 4^n`.
lemma ascPochhammer_one_div_two (n : ℕ) :
    (ascPochhammer ℝ n).eval (1 / 2) =
      (Nat.choose (2 * n) n : ℝ) * (n.factorial : ℝ) / 4 ^ n := by
  induction n with
  | zero => norm_num [ascPochhammer]
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ, pow_succ]
    have hrec := Nat.succ_mul_centralBinom_succ n
    simp only [Nat.centralBinom_eq_two_mul_choose] at hrec
    have hcast : ((n : ℝ) + 1) * (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
        = 2 * (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) := by
      exact_mod_cast hrec
    push_cast
    field_simp
    nlinarith [hcast]

/-- The coefficient of `₂F₁(1/2, 1/2; 3/2; ·)` is `C(2n,n)/(4ⁿ(2n+1))`: the two ascending
factorials `(1/2)ₙ` cancel one of the `(3/2)ₙ` factors, leaving `4ⁿ` against the central
binomial coefficient. Equivalently this is the `z^{2n+1}` coefficient of `arcsin`, divided
by `z^{2n}`. -/
-- Theorem: `hypCoeff (1/2) (1/2) (3/2) n = C(2n,n) / (4^n * (2n+1))`.
lemma hypCoeff_half_half_three_half (n : ℕ) :
    hypCoeff (1 / 2) (1 / 2) (3 / 2) n =
      (Nat.choose (2 * n) n : ℝ) / (4 ^ n * (2 * (n : ℝ) + 1)) := by
  induction n with
  | zero => norm_num [hypCoeff, ordinaryHypergeometricCoefficient]
  | succ n ih =>
    rw [hypCoeff_succ, ih, pow_succ]
    have hrec := Nat.succ_mul_centralBinom_succ n
    simp only [Nat.centralBinom_eq_two_mul_choose] at hrec
    have hcast : ((n : ℝ) + 1) * (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
        = 2 * (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) := by
      exact_mod_cast hrec
    push_cast
    field_simp
    nlinarith [hcast]

/-- The binomial series for `1/√(1 - t²)`: the coefficients `(1/2)ₙ/n!` are the central
binomial coefficients `C(2n,n)/4ⁿ`. This is the series that gets integrated term by term to
produce the arcsine series. -/
-- Theorem: `∑ₙ C(2n,n)/4ⁿ t^{2n} = 1/√(1 - t²)` for `|t| < 1`.
lemma hasSum_inv_sqrt_one_sub_sq {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ => (Nat.choose (2 * n) n : ℝ) / 4 ^ n * t ^ (2 * n))
      (1 / (1 - t ^ 2) ^ (1 / 2 : ℝ)) := by
  have ht2 : |t ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg t)]
    nlinarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
  have hmem : t ^ 2 ∈ Metric.eball (0 : ℝ) (1 : ℝ≥0∞) := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact ht2
  have hbase := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2)).hasSum hmem
  rw [zero_add] at hbase
  refine hbase.congr_fun ?_
  intro n
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, ← pow_mul,
    ring_choose_eq_ascPochhammer, ascPochhammer_one_div_two]
  have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- The arcsine power series, obtained by integrating the binomial series for
`1/√(1 - t²)` term by term between `0` and `z`:
`arcsin z = ∑ₙ C(2n,n)/(4ⁿ(2n+1)) z^{2n+1}` for `|z| < 1`.

The dominating series is the same binomial series evaluated at some `R` with
`|z| < R < 1`, which is summable because `1/√(1 - R²)` is finite. -/
-- Theorem: for `|z| < 1`,
-- `HasSum (fun n => hypCoeff (1/2) (1/2) (3/2) n * z^(2n+1)) (Real.arcsin z)`.
lemma hasSum_arcsin {z : ℝ} (hz : |z| < 1) :
    HasSum (fun n : ℕ => hypCoeff (1 / 2) (1 / 2) (3 / 2) n * z ^ (2 * n + 1))
      (Real.arcsin z) := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg z) hzR
  have hRlt : |R| < 1 := by rw [abs_of_pos hRpos]; exact hR1
  have hbound_summ : Summable fun n : ℕ => (Nat.choose (2 * n) n : ℝ) / 4 ^ n * R ^ (2 * n) :=
    (hasSum_inv_sqrt_one_sub_sq hRlt).summable
  -- Every point of the interval of integration has modulus at most `|z|`.
  have hmem_abs : ∀ t ∈ Set.uIcc (0 : ℝ) z, |t| ≤ |z| := by
    intro t ht
    simpa [Real.dist_eq] using Real.dist_left_le_of_mem_uIcc ht
  have hmain : HasSum (fun n : ℕ => ∫ t in (0 : ℝ)..z,
        (Nat.choose (2 * n) n : ℝ) / 4 ^ n * t ^ (2 * n))
      (∫ t in (0 : ℝ)..z, 1 / (1 - t ^ 2) ^ (1 / 2 : ℝ)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun n (_ : ℝ) => (Nat.choose (2 * n) n : ℝ) / 4 ^ n * R ^ (2 * n))
    · intro n
      exact (continuous_const.mul (continuous_id.pow (2 * n))).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have htabs : |t| ≤ R := le_trans (hmem_abs t (Set.uIoc_subset_uIcc ht)) hzR.le
      have hc : (0 : ℝ) ≤ (Nat.choose (2 * n) n : ℝ) / 4 ^ n := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) htabs (2 * n)) hc
    · refine Filter.Eventually.of_forall (fun _ _ => hbound_summ)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun t ht => ?_)
      exact hasSum_inv_sqrt_one_sub_sq
        (lt_of_le_of_lt (hmem_abs t (Set.uIoc_subset_uIcc ht)) hz)
  have hpow : ∀ n : ℕ, (∫ t in (0 : ℝ)..z,
        (Nat.choose (2 * n) n : ℝ) / 4 ^ n * t ^ (2 * n))
      = (Nat.choose (2 * n) n : ℝ) / 4 ^ n * z ^ (2 * n + 1) / (2 * n + 1) := by
    intro n
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have harcsin : (∫ t in (0 : ℝ)..z, 1 / (1 - t ^ 2) ^ (1 / 2 : ℝ)) = Real.arcsin z := by
    have hEq : Set.EqOn (fun t : ℝ => 1 / (1 - t ^ 2) ^ (1 / 2 : ℝ)) (deriv Real.arcsin)
        (Set.uIcc (0 : ℝ) z) := by
      intro x _
      simp only [Real.deriv_arcsin, Real.sqrt_eq_rpow]
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) z, DifferentiableAt ℝ Real.arcsin x := by
      intro x hx
      have hxabs : |x| ≤ |z| := hmem_abs x hx
      have hx1 : x ≠ 1 := by
        intro h; rw [h] at hxabs; norm_num at hxabs; linarith [hz]
      have hx2 : x ≠ -1 := by
        intro h; rw [h] at hxabs; norm_num at hxabs; linarith [hz]
      exact (Real.hasDerivAt_arcsin hx2 hx1).differentiableAt
    have hint : IntervalIntegrable (deriv Real.arcsin) MeasureTheory.volume 0 z := by
      rw [Real.deriv_arcsin]
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div
      · exact continuousOn_const
      · exact Real.continuous_sqrt.comp_continuousOn
          (continuousOn_const.sub (continuousOn_id.pow 2))
      · intro x hx
        have hxlt : |x| < 1 := lt_of_le_of_lt (hmem_abs x hx) hz
        exact (Real.sqrt_pos.2 (by nlinarith [(abs_lt.mp hxlt).1, (abs_lt.mp hxlt).2])).ne'
    calc (∫ t in (0 : ℝ)..z, 1 / (1 - t ^ 2) ^ (1 / 2 : ℝ))
        = ∫ t in (0 : ℝ)..z, deriv Real.arcsin t := intervalIntegral.integral_congr hEq
      _ = Real.arcsin z - Real.arcsin 0 := intervalIntegral.integral_deriv_eq_sub hderiv hint
      _ = Real.arcsin z := by rw [Real.arcsin_zero, sub_zero]
  rw [harcsin] at hmain
  refine hmain.congr_fun (fun n => ?_)
  rw [hpow n, hypCoeff_half_half_three_half]
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- H1, fourth case: `₂F₁(1/2, 1/2; 3/2; z²) = arcsin z / z` on `0 < |z| < 1`.

The coefficient identity `hypCoeff (1/2) (1/2) (3/2) n = C(2n,n)/(4ⁿ(2n+1))` matches the
arcsine series `hasSum_arcsin` term by term. The hypothesis `z ≠ 0` is essential: at `z = 0`
the right-hand side is the junk `0/0 = 0` while the left-hand side is `1`, so the identity
is proved pointwise by `HasSum.unique` rather than through the function-valued
`hyp_eq_of_hasSum`. -/
-- Theorem: `₂F₁(1/2, 1/2; 3/2; z²) = arcsin z / z` for `z ≠ 0`, `|z| < 1`.
theorem hyp_half_half_three_half {z : ℝ} (hz0 : z ≠ 0) (hz : |z| < 1) :
    hyp (1 / 2) (1 / 2) (3 / 2) (z ^ 2) = Real.arcsin z / z := by
  have hc : ∀ n : ℕ, (3 / 2 : ℝ) ≠ -(n : ℝ) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hzsq : |z ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg z)]
    nlinarith [(abs_lt.mp hz).1, (abs_lt.mp hz).2]
  have hsrc := (hasSum_arcsin hz).div_const z
  refine (hasSum_hyp (a := 1 / 2) (b := 1 / 2) (c := 3 / 2) (z := z ^ 2) hzsq hc).unique
    (hsrc.congr_fun ?_)
  intro n
  rw [← pow_mul, pow_succ]
  field_simp

/-- The `arcsin z / z` closed form (H1 D) is P-constructible. -/
-- Theorem: `hyp (1/2) (1/2) (3/2) (z²)` is P-constructible for P-constructible `z ≠ 0`,
-- `|z| < 1`.
@[pconstructible_cond]
theorem hyp_half_half_three_half_Pconstructible {z : ℝ} (hz : PConstructible z) (hz0 : z ≠ 0)
    (hzabs : |z| < 1) : PConstructible (hyp (1 / 2) (1 / 2) (3 / 2) (z ^ 2)) := by
  rw [hyp_half_half_three_half hz0 hzabs]
  exact PConstructible.div (arcsin_Pconstructible hz) hz

end

end Pconstructible
