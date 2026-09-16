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
-- `Pptc.Hypergeometric.Basic` supplies `hyp`, `hypCoeff`, `hasSum_hyp` and the
-- identification lemma `hyp_self_eq_rpow`. `Gamma.Beta` supplies the Beta integral
-- `Complex.betaIntegral` and its Gamma evaluation; `Pow.Real` / `Integrability.Basic`
-- the real-power integral and its integrability; `DominatedConvergence` the termwise
-- integration lemma used to pass from the series to the integral.
import Pptc.Hypergeometric.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Pptc.Hypergeometric.Euler

The Euler integral representation of the Gauss hypergeometric function,

`₂F₁(a, b; c; z) = Γ(c) / (Γ(b) Γ(c−b)) ∫₀¹ t^(b−1) (1−t)^(c−b−1) (1−z t)^(−a) dt`
for `c > b > 0` and `|z| < 1`,

together with the real Beta integral it rests on.

## The Beta integral

Mathlib states the Beta function only over the complex numbers
(`Complex.betaIntegral`), where the corresponding Gamma identity is
`Complex.betaIntegral_eq_Gamma_mul_div`. The first lemma below transports that identity
back to the real interval integral `∫ x in 0..1, x^(p−1) (1−x)^(q−1)`, which is what the
term-by-term integration of the hypergeometric series needs.

## The interchange

`(1 − z t)^(−a)` is expanded with the binomial (equivalently, `hyp a b b`) series. The
`n`-th integrated term is `hypCoeff a b b n * z ^ n * B(b + n, c − b)`, and the Beta
identity `(b)ₙ / (c)ₙ = Γ(c)/(Γ(b) Γ(c−b)) * B(b + n, c − b)` converts it into
`hypCoeff a b c n * z ^ n` divided by the prefactor `Γ(c)/(Γ(b) Γ(c−b))`. The
interchange is justified by dominated convergence with the bound
`|hypCoeff a b b n| ρ ^ n t^(b−1)(1 − t)^(c−b−1)`, where `|z| < ρ < 1`.
-/

open scoped Topology ENNReal

namespace Pconstructible

noncomputable section

/-! ### The real Beta integral

The Beta integral is first extracted from its complex counterpart, then used to evaluate
the monomial factors `∫₀¹ t^(n+b−1) (1 − t)^(c−b−1)` that appear after the interchange. -/

/-- The real Beta integral: `∫₀¹ x^(p−1) (1−x)^(q−1) dx = Γ p Γ q / Γ(p + q)` for
`p, q > 0`.

Mathlib's `Complex.betaIntegral` integrates `(x : ℂ)^(u−1) (1−x : ℂ)^(v−1)` over `0..1`,
and `Complex.betaIntegral_eq_Gamma_mul_div` evaluates it. On `(0, 1)` the complex
integrand is the coercion of the real one (`Complex.ofReal_cpow`), so the real interval
integral is the real part of the complex Beta integral. -/
-- Theorem: `∫₀¹ x^(p-1) (1-x)^(q-1) = Γ p Γ q / Γ(p+q)` for `p, q > 0`.
theorem integral_rpow_mul_one_sub_rpow (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ∫ x in (0 : ℝ)..1, x ^ (p - 1) * (1 - x) ^ (q - 1) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have hcomplex : Complex.betaIntegral (p : ℂ) (q : ℂ) =
      ((Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div (p : ℂ) (q : ℂ) (by simpa using hp)
      (by simpa using hq)]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, ← Complex.ofReal_add, Complex.Gamma_ofReal]
  have hreal : ((∫ x in (0 : ℝ)..1, x ^ (p - 1) * (1 - x) ^ (q - 1) : ℝ) : ℂ) =
      Complex.betaIntegral (p : ℂ) (q : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    unfold Complex.betaIntegral
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hx0 : (0 : ℝ) ≤ x := hx.1.le
    have hx1 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
    rw [show (p : ℂ) - 1 = ((p - 1 : ℝ) : ℂ) by push_cast; ring,
      show (q : ℂ) - 1 = ((q - 1 : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hx0 (p - 1), ← Complex.ofReal_cpow hx1 (q - 1),
      ← Complex.ofReal_mul]
  exact Complex.ofReal_inj.mp (hreal.trans hcomplex)

/-! ### Integrability of the Beta weight

`t ↦ t^(b−1) (1 − t)^(c−b−1)` is interval integrable on `0..1` exactly when `b > 0` and
`c − b > 0`. The singularities at the two endpoints are separated by splitting at `1/2`:
on the left, `t^(b−1)` is controlled by `intervalIntegrable_rpow'` and the other factor is
continuous; on the right the roles are exchanged, using `1 − t` as the variable. -/

/-- `t ↦ t^(b−1) (1 − t)^(c−b−1)` is interval integrable on `[0, 1]` for `c > b > 0`. -/
-- Theorem: `IntervalIntegrable (fun t => t^(b-1) * (1-t)^(c-b-1)) volume 0 1` for `0 < b < c`.
theorem intervalIntegrable_weight (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    IntervalIntegrable (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1))
      MeasureTheory.volume 0 1 := by
  have hleft : IntervalIntegrable
      (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1)) MeasureTheory.volume 0 (1 / 2) := by
    have h1 : IntervalIntegrable (fun t : ℝ => t ^ (b - 1)) MeasureTheory.volume 0 (1 / 2) :=
      intervalIntegral.intervalIntegrable_rpow' (r := b - 1) (by linarith) (a := 0) (b := 1 / 2)
    have h2 : ContinuousOn (fun t : ℝ => (1 - t) ^ (c - b - 1))
        (Set.uIcc (0 : ℝ) (1 / 2)) := by
      refine (continuousOn_const.sub continuousOn_id).rpow_const fun x hx => Or.inl ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
      change (1 : ℝ) - x ≠ 0
      exact ne_of_gt (by linarith [hx.2] : (0 : ℝ) < 1 - x)
    exact h1.mul_continuousOn h2
  have hright : IntervalIntegrable
      (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1)) MeasureTheory.volume (1 / 2) 1 := by
    have h2 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (c - b - 1))
        MeasureTheory.volume (1 / 2) 1 := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (r := c - b - 1) (by linarith)
        (a := 0) (b := 1 / 2)).comp_sub_left 1
      simpa [show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num] using h.symm
    have h1 : ContinuousOn (fun t : ℝ => t ^ (b - 1)) (Set.uIcc ((1 : ℝ) / 2) 1) := by
      refine continuousOn_id.rpow_const fun x hx => Or.inl ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 1)] at hx
      change x ≠ 0
      exact ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)
    exact h2.continuousOn_mul h1
  exact hleft.trans hright

/-! ### Gamma and Pochhammer

`(b)ₙ = Γ(b + n)/Γ(b)` is the identity that converts the Beta integral `B(b + n, c − b)`
into the ratio of Pochhammer symbols appearing in the hypergeometric coefficient. -/

/-- The ascending Pochhammer symbol is the ratio of Gamma functions:
`Γ(b + n) = (b)ₙ Γ(b)`. Proved by the recurrence `Γ(s + 1) = s Γ(s)`. -/
-- Theorem: `Real.Gamma (s + n) = (ascPochhammer ℝ n).eval s * Real.Gamma s` for `0 < s`.
theorem Gamma_add_nat (s : ℝ) (hs : 0 < s) (n : ℕ) :
    Real.Gamma (s + (n : ℝ)) = (ascPochhammer ℝ n).eval s * Real.Gamma s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn : s + (n : ℝ) ≠ 0 := by positivity
    rw [show s + ((n + 1 : ℕ) : ℝ) = (s + (n : ℝ)) + 1 by push_cast; ring,
      Real.Gamma_add_one hsn, ih, ascPochhammer_succ_eval]
    ring

/-- When `c = b` the hypergeometric coefficient reduces to the binomial one,
`hypCoeff a b b n = (a)ₙ / n!`. The hypothesis `b ∉ -ℕ` makes `(b)ₙ` invertible. -/
-- Theorem: `hypCoeff a b b n = (ascPochhammer ℝ n).eval a / n!` for `b ∉ -ℕ`.
theorem hypCoeff_self (a b : ℝ) (hb : ∀ n : ℕ, b ≠ -(n : ℝ)) (n : ℕ) :
    hypCoeff a b b n = (ascPochhammer ℝ n).eval a / (n.factorial : ℝ) := by
  have hb' : (ascPochhammer ℝ n).eval b ≠ 0 := by
    intro h0
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n b).1 h0
    exact hb k (by linarith)
  unfold hypCoeff ordinaryHypergeometricCoefficient
  rw [mul_inv_cancel_right₀ hb', div_eq_mul_inv]
  ring

/-- A positive `b` is never a nonpositive integer, the form of the side condition needed by
`hasSum_hyp` and `hyp_self_eq_rpow`. -/
theorem ne_neg_nat_of_pos {b : ℝ} (hb : 0 < b) : ∀ n : ℕ, b ≠ -(n : ℝ) := by
  intro n h
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-! ### The term-by-term integral

After expanding `(1 − z t)^(−a)` with the `hyp a b b` series, the `n`-th term is
`hypCoeff a b b n · (z t)ⁿ · t^(b−1)(1−t)^(c−b−1)`. Its integral is the Beta value
`B(b+n, c−b)`, and `(b)ₙ/(c)ₙ Γ(c−b) = Γ(b+n)Γ(c−b)/Γ(c+n)` converts that into
`hypCoeff a b c n · zⁿ` divided by the prefactor `Γ(c)/(Γ(b)Γ(c−b))`. -/

/-- The integral of the `n`-th term of the expanded integrand:
`∫₀¹ hypCoeff a b b n (z t)ⁿ t^(b−1)(1−t)^(c−b−1) dt = hypCoeff a b c n zⁿ / P`,
where `P = Γ(c)/(Γ(b) Γ(c−b))`. -/
-- Theorem: the `n`-th term integral equals `hypCoeff a b c n * z^n / P`.
theorem integral_term (a b c z : ℝ) (hb : 0 < b) (hbc : b < c) (n : ℕ) :
    ∫ t in (0 : ℝ)..1, hypCoeff a b b n * (z * t) ^ n *
        (t ^ (b - 1) * (1 - t) ^ (c - b - 1)) =
      hypCoeff a b c n * z ^ n /
        (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) := by
  have hbne : ∀ m : ℕ, b ≠ -(m : ℝ) := ne_neg_nat_of_pos hb
  have hcpos : 0 < c := lt_trans hb hbc
  have hcn : (ascPochhammer ℝ n).eval c ≠ 0 := by
    intro h0
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n c).1 h0
    exact hcpos.ne' (by linarith)
  have hbn : (ascPochhammer ℝ n).eval b ≠ 0 := by
    intro h0
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n b).1 h0
    exact hbne k (by linarith)
  have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hGb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hGc : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hcpos).ne'
  have hGcb : Real.Gamma (c - b) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hcongr : (fun t : ℝ => hypCoeff a b b n * (z * t) ^ n *
        (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))
      = fun t : ℝ => (hypCoeff a b b n * z ^ n) *
        (t ^ n * (t ^ (b - 1) * (1 - t) ^ (c - b - 1))) := by
    funext t
    rw [mul_pow]
    ring
  have hinner : ∫ t in (0 : ℝ)..1, t ^ n * (t ^ (b - 1) * (1 - t) ^ (c - b - 1))
      = ∫ t in (0 : ℝ)..1, t ^ ((n : ℝ) + b - 1) * (1 - t) ^ (c - b - 1) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht0 : (0 : ℝ) < t := ht.1
    rw [(Real.rpow_natCast t n).symm, ← mul_assoc, ← Real.rpow_add ht0,
      show (n : ℝ) + (b - 1) = (n : ℝ) + b - 1 by ring]
  rw [hcongr, intervalIntegral.integral_const_mul, hinner,
    integral_rpow_mul_one_sub_rpow ((n : ℝ) + b) (c - b) (by positivity) (by linarith),
    show (n : ℝ) + b = b + n by ring, show (b + (n : ℝ)) + (c - b) = c + (n : ℝ) by ring,
    Gamma_add_nat b hb n, Gamma_add_nat c hcpos n, hypCoeff_self a b hbne n]
  simp only [hypCoeff, ordinaryHypergeometricCoefficient]
  field_simp

/-! ### The Euler integral representation

`(1 − z t)^(−a)` is expanded with `hasSum_hyp` at the `hyp a b b` series. Dominated
convergence (`intervalIntegral.hasSum_integral_of_dominated_convergence`) with the bound
`|hypCoeff a b b n| ρⁿ t^(b−1)(1−t)^(c−b−1)`, where `|z| < ρ < 1`, justifies the termwise
integration. Each term integral is `integral_term`, and the resulting series is exactly
the hypergeometric series for `hyp a b c z`, so `HasSum.unique` identifies the prefactor
times the integral with `hyp a b c z`. -/

/-- **Euler's integral representation of the Gauss hypergeometric function**:
for `c > b > 0` and `|z| < 1`,

`₂F₁(a, b; c; z) = Γ(c)/(Γ(b) Γ(c−b)) ∫₀¹ t^(b−1)(1−t)^(c−b−1)(1−z t)^(−a) dt`.

The conditions `b > 0` and `c > b` are exactly what makes the Beta integral converge at
the two endpoints; `|z| < 1` keeps `1 − z t > 0` on `[0, 1]`, so the integrand is finite. -/
-- Theorem: Euler's integral representation of `₂F₁`.
theorem hyp_eq_integral {a b c z : ℝ} (hb : 0 < b) (hbc : b < c) (hz : |z| < 1)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    hyp a b c z = Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) *
      ∫ t in (0 : ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - z * t) ^ (-a) := by
  have hbne : ∀ m : ℕ, b ≠ -(m : ℝ) := ne_neg_nat_of_pos hb
  have hcpos : 0 < c := lt_trans hb hbc
  have hPne : Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) ≠ 0 :=
    div_ne_zero (Real.Gamma_pos_of_pos hcpos).ne'
      (mul_ne_zero (Real.Gamma_pos_of_pos hb).ne' (Real.Gamma_pos_of_pos (by linarith)).ne')
  -- A radius `ρ` with `|z| < ρ < 1` for the uniform geometric bound.
  obtain ⟨ρ, hzρ, hρ1⟩ := exists_between hz
  have hρpos : 0 < ρ := lt_of_le_of_lt (abs_nonneg z) hzρ
  have hρabs : |ρ| < 1 := by rw [abs_of_pos hρpos]; exact hρ1
  have hgeom : Summable (fun n : ℕ => |hypCoeff a b b n| * ρ ^ n) := by
    have h := (hasSum_hyp (a := a) (b := b) (c := b) (z := ρ) hρabs hbne).summable.abs
    simpa only [abs_mul, abs_pow, abs_of_pos hρpos] using h
  -- Termwise integration, dominated by `|hypCoeff a b b n| ρⁿ t^(b−1)(1−t)^(c−b−1)`.
  have hmain : HasSum (fun n : ℕ => ∫ t in (0 : ℝ)..1,
        hypCoeff a b b n * (z * t) ^ n * (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))
      (∫ t in (0 : ℝ)..1, (1 - z * t) ^ (-a) * (t ^ (b - 1) * (1 - t) ^ (c - b - 1))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
      (bound := fun n t => |hypCoeff a b b n| * ρ ^ n *
        (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))
    · intro n
      exact (by fun_prop : Measurable (fun t : ℝ => hypCoeff a b b n * (z * t) ^ n *
        (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht0 : (0 : ℝ) < t := ht.1
      have hg_nonneg : 0 ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) :=
        mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg (by linarith [ht.2]) _)
      have hzt : |z * t| ≤ ρ := by
        rw [abs_mul, abs_of_pos ht0]
        calc |z| * t ≤ |z| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg z)
          _ = |z| := mul_one _
          _ ≤ ρ := hzρ.le
      have hpow : |z * t| ^ n ≤ ρ ^ n := pow_le_pow_left₀ (abs_nonneg _) hzt n
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hg_nonneg, abs_pow]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) hg_nonneg
    · refine Filter.Eventually.of_forall fun t _ => ?_
      exact hgeom.mul_right (t ^ (b - 1) * (1 - t) ^ (c - b - 1))
    · have hfun : (fun t : ℝ => ∑' n : ℕ, |hypCoeff a b b n| * ρ ^ n *
            (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))
          = fun t : ℝ => (∑' n : ℕ, |hypCoeff a b b n| * ρ ^ n) *
            (t ^ (b - 1) * (1 - t) ^ (c - b - 1)) := by
        funext t
        rw [tsum_mul_right]
      rw [hfun]
      exact (intervalIntegrable_weight b c hb hbc).const_mul _
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht0 : (0 : ℝ) < t := ht.1
      have hzt : |z * t| < 1 := by
        rw [abs_mul, abs_of_pos ht0]
        calc |z| * t ≤ |z| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg z)
          _ = |z| := mul_one _
          _ < 1 := hz
      have h := hasSum_hyp (a := a) (b := b) (c := b) (z := z * t) hzt hbne
      rw [hyp_self_eq_rpow hbne hzt] at h
      exact h.mul_right (t ^ (b - 1) * (1 - t) ^ (c - b - 1))
  -- Replace each term integral by `hypCoeff a b c n zⁿ / P`.
  have hmain' : HasSum (fun n : ℕ => hypCoeff a b c n * z ^ n /
        (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))))
      (∫ t in (0 : ℝ)..1, (1 - z * t) ^ (-a) * (t ^ (b - 1) * (1 - t) ^ (c - b - 1))) :=
    hmain.congr_fun fun n => (integral_term a b c z hb hbc n).symm
  have hscaled := hmain'.mul_right (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)))
  have hscale : (fun n : ℕ => (hypCoeff a b c n * z ^ n /
        (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)))) *
        (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))))
      = fun n : ℕ => hypCoeff a b c n * z ^ n := by
    funext n
    exact div_mul_cancel₀ _ hPne
  rw [hscale] at hscaled
  have huniq := (hasSum_hyp (a := a) (b := b) (c := c) (z := z) hz hc).unique hscaled
  have hint : (∫ t in (0 : ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - z * t) ^ (-a))
      = ∫ t in (0 : ℝ)..1, (1 - z * t) ^ (-a) * (t ^ (b - 1) * (1 - t) ^ (c - b - 1)) :=
    intervalIntegral.integral_congr fun t _ => by ring
  rw [hint]
  exact huniq.trans (mul_comm _ _)

end

end Pconstructible
