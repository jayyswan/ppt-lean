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
import Pptc.Hypergeometric.Graphs
import Pptc.Hypergeometric.EllipticClass

/-! # Pptc.Hypergeometric.GraphsClass

The contiguous class of the H6 graph families (L5b of
`PLAN-hypergeometric-00-overview`).

`Graphs.lean` proves the V4 identity

`∫₀^X √(1 + b² xᵐ) dx = X · ₂F₁(−½, 1/m; 1 + 1/m; −b² Xᵐ)`  (`m = 2n − 2`),

and that the resulting ₂F₁ value is P-constructible for `n ∈ {2,…,6}`. Differentiating the
identity at its upper limit produces the *derivative* of the same ₂F₁ at the same argument,
and that is the second seed the contiguous machinery of `EllipticClass.lean` needs.

The file is organised as:

* Step 1 — `deriv_graphFamily_Pconstructible`: the derivative of the H6 ₂F₁ is
  P-constructible, obtained from the fundamental theorem of calculus;
* Step 2 — the immediate contiguous neighbours of the base parameter triple;
* Step 3 — `hyp_graphFamily_class_Pconstructible`: the full class
  `₂F₁(−½+i, 1/m+j; 1+1/m+k; w)` for `i, j : ℤ`, `k : ℕ`, by strong induction.
-/

open scoped Topology ENNReal

namespace Pconstructible

noncomputable section

/-! ### Step 1: the derivative of the H6 family

Write `G(X) = X · ₂F₁(−½, 1/m; 1+1/m; −b²Xᵐ)`. The V4 identity says `G(X)` is the integral
of `√(1 + b²xᵐ)`, whose derivative at the upper limit is `√(1 + b²Xᵐ)`. On the other hand
the product and chain rules give

`G′(X) = F(−b²Xᵐ) + X · F′(−b²Xᵐ) · (−b² m Xᵐ⁻¹)`,

so equating the two and using `X · Xᵐ⁻¹ = Xᵐ` solves for

`F′(−b²Xᵐ) = (F(−b²Xᵐ) − √(1 + b²Xᵐ)) / (b² m Xᵐ)`.

Both numerator and denominator are P-constructible (`F` by
`hyp_neg_half_arcLength_Pconstructible`), which is the content of the theorem below. -/

/-- The hypergeometric function of the H6 parameters is differentiable where its series
converges. This reads differentiability off the power series `ordinaryHypergeometricSeries`,
whose radius is at least `1` when `c ∉ -ℕ`. -/
-- Theorem: `hyp a b c` is differentiable at `z` for `|z| < 1`, `c ∉ -ℕ`.
lemma differentiableAt_hyp {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz : |z| < 1) :
    DifferentiableAt ℝ (fun w => hyp a b c w) z := by
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
  exact ((ordinaryHypergeometricSeries ℝ a b c).hasFPowerSeriesOnBall hpos).differentiableOn
    |>.differentiableAt (Metric.isOpen_eball.mem_nhds hmem)

/-- **Step 1 (L5b), general form.** Fix the graph data `b ≠ 0`, `X > 0` and the exponent
`m > 0`, and let `w = −b²Xᵐ`. If the ₂F₁ value at `w` is P-constructible, so is its
derivative at `w`. Solving the differentiated V4 identity for the derivative expresses it as
`(F(w) − √(1 + b²Xᵐ))/(b² m Xᵐ)`, and every ingredient of that expression is
P-constructible. -/
-- Theorem: for `m > 0`, `w = -(b²Xᵐ)`: `PConstructible (hyp (-1/2)(1/m)(1+1/m) w)` implies
-- `PConstructible (deriv (hyp (-1/2)(1/m)(1+1/m)) w)`.
theorem deriv_graphFamily_Pconstructible {m : ℕ} (hm : 0 < m) {b X w : ℝ}
    (hb : PConstructible b) (hb0 : b ≠ 0) (hXP : PConstructible X) (hX0 : 0 < X)
    (hw : w = -(b ^ 2 * X ^ m)) (hsmall : |w| < 1)
    (hseed : PConstructible (hyp (-(1 / 2)) (1 / (m : ℝ)) (1 + 1 / (m : ℝ)) w)) :
    PConstructible
      (deriv (fun u => hyp (-(1 / 2)) (1 / (m : ℝ)) (1 + 1 / (m : ℝ)) u) w) := by
  subst w
  set a : ℝ := -(1 / 2) with ha
  set p : ℝ := 1 / (m : ℝ) with hp
  set q : ℝ := 1 + p with hq
  have hc : ∀ k : ℕ, q ≠ -(k : ℝ) := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hqpos : 0 < q := by rw [hq, hp]; positivity
    linarith
  have hz : |-(b ^ 2 * X ^ m)| < 1 := hsmall
  have hdiff : DifferentiableAt ℝ (fun u => hyp a p q u) (-(b ^ 2 * X ^ m)) :=
    differentiableAt_hyp hc hz
  -- The derivative of `Y ↦ -(b² Yᵐ)` at `X`.
  have hwderiv : HasDerivAt (fun Y : ℝ => -(b ^ 2 * Y ^ m))
      (-(b ^ 2 * (m : ℝ) * X ^ (m - 1))) X := by
    have hpow : HasDerivAt (fun Y : ℝ => Y ^ m) ((m : ℝ) * X ^ (m - 1)) X :=
      hasDerivAt_pow m X
    have h := (hpow.const_mul (b ^ 2)).neg
    rw [show (-fun y : ℝ => b ^ 2 * y ^ m) = fun Y : ℝ => -(b ^ 2 * Y ^ m) from by
      ext y; rfl] at h
    rw [show -(b ^ 2 * ((m : ℝ) * X ^ (m - 1))) = -(b ^ 2 * (m : ℝ) * X ^ (m - 1)) from by
      ring] at h
    exact h
  have hcomp : HasDerivAt (fun Y : ℝ => hyp a p q (-(b ^ 2 * Y ^ m)))
      (deriv (fun u => hyp a p q u) (-(b ^ 2 * X ^ m))
        * (-(b ^ 2 * (m : ℝ) * X ^ (m - 1)))) X :=
    hdiff.hasDerivAt.comp X hwderiv
  have hG2 : HasDerivAt (fun Y : ℝ => Y * hyp a p q (-(b ^ 2 * Y ^ m)))
      (hyp a p q (-(b ^ 2 * X ^ m)) + X * (deriv (fun u => hyp a p q u) (-(b ^ 2 * X ^ m))
        * (-(b ^ 2 * (m : ℝ) * X ^ (m - 1))))) X := by
    have h := (hasDerivAt_id X).mul hcomp
    rw [show (id * fun Y : ℝ => hyp a p q (-(b ^ 2 * Y ^ m)))
        = (fun Y : ℝ => Y * hyp a p q (-(b ^ 2 * Y ^ m))) from by ext Y; rfl] at h
    simpa using h
  -- The fundamental theorem of calculus for the integral of the speed.
  have hcont : Continuous fun x : ℝ => Real.sqrt (1 + b ^ 2 * x ^ m) := by fun_prop
  have hInt : IntervalIntegrable (fun x : ℝ => Real.sqrt (1 + b ^ 2 * x ^ m))
      MeasureTheory.volume 0 X := hcont.intervalIntegrable 0 X
  have hFTC := intervalIntegral.integral_hasStrictDerivAt_right hInt
    (hcont.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 X)) hcont.continuousAt
  -- The identity holds on a neighbourhood of `X`.
  have hYpos : ∀ᶠ Y in 𝓝 X, (0 : ℝ) < Y := isOpen_Ioi.mem_nhds hX0
  have hsX : |b ^ 2 * X ^ m| < 1 := by simpa only [abs_neg] using hsmall
  have hYsmall : ∀ᶠ Y in 𝓝 X, |b ^ 2 * Y ^ m| < 1 := by
    have hcont' : ContinuousAt (fun Y : ℝ => |b ^ 2 * Y ^ m|) X := by fun_prop
    exact hcont'.tendsto.eventually (Iio_mem_nhds hsX)
  have heq : (fun Y : ℝ => ∫ x in (0 : ℝ)..Y, Real.sqrt (1 + b ^ 2 * x ^ m))
      =ᶠ[𝓝 X] (fun Y : ℝ => Y * hyp a p q (-(b ^ 2 * Y ^ m))) := by
    filter_upwards [hYpos, hYsmall] with Y hY hYs
    rw [ha, hq, hp]
    exact integral_sqrt_one_add_sq_mul_pow (m := m) hm (b := b) (X := Y) hY.le hYs
  have hG1 : HasDerivAt (fun Y : ℝ => Y * hyp a p q (-(b ^ 2 * Y ^ m)))
      (Real.sqrt (1 + b ^ 2 * X ^ m)) X :=
    hFTC.hasDerivAt.congr_of_eventuallyEq heq.symm
  -- Equate the two derivatives and solve.
  have hkey : Real.sqrt (1 + b ^ 2 * X ^ m)
      = hyp a p q (-(b ^ 2 * X ^ m)) + X * (deriv (fun u => hyp a p q u) (-(b ^ 2 * X ^ m))
        * (-(b ^ 2 * (m : ℝ) * X ^ (m - 1)))) := hG1.unique hG2
  have hpow : X * X ^ (m - 1) = X ^ m := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [show m' + 1 - 1 = m' by omega, pow_succ']
  have hden : b ^ 2 * (m : ℝ) * X ^ m ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hb0) ?_) (pow_ne_zero m (ne_of_gt hX0))
    exact_mod_cast (ne_of_gt hm : m ≠ 0)
  have hcollect : X * (deriv (fun u => hyp a p q u) (-(b ^ 2 * X ^ m))
      * (-(b ^ 2 * (m : ℝ) * X ^ (m - 1))))
      = -(deriv (fun u => hyp a p q u) (-(b ^ 2 * X ^ m)) * (b ^ 2 * (m : ℝ) * X ^ m)) := by
    rw [← hpow]; ring
  have hkey' : hyp a p q (-(b ^ 2 * X ^ m)) - Real.sqrt (1 + b ^ 2 * X ^ m)
      = deriv (fun u => hyp a p q u) (-(b ^ 2 * X ^ m)) * (b ^ 2 * (m : ℝ) * X ^ m) := by
    rw [hkey, hcollect]; ring
  have hderiv_eq : deriv (fun u => hyp a p q u) (-(b ^ 2 * X ^ m))
      = (hyp a p q (-(b ^ 2 * X ^ m)) - Real.sqrt (1 + b ^ 2 * X ^ m))
        / (b ^ 2 * (m : ℝ) * X ^ m) := by
    rw [eq_div_iff hden]
    linarith [hkey']
  -- P-constructibility of the two sides of the solved derivative.
  have hroot : PConstructible (Real.sqrt (1 + b ^ 2 * X ^ m)) :=
    sqrt_Pconstructible (PConstructible.add PConstructible.base_one
      (PConstructible.mul (sq_Pconstructible hb) (pow_Pconstructible hXP m)))
  have hnum : PConstructible (hyp a p q (-(b ^ 2 * X ^ m)) - Real.sqrt (1 + b ^ 2 * X ^ m)) :=
    PConstructible.sub hseed hroot
  have hdenP : PConstructible (b ^ 2 * (m : ℝ) * X ^ m) :=
    PConstructible.mul (PConstructible.mul (sq_Pconstructible hb) (nat_Pconstructible m))
      (pow_Pconstructible hXP m)
  rw [hderiv_eq]
  exact PConstructible.div hnum hdenP

/-- **Step 1 (L5b), H6 form.** The derivative of the H6 ₂F₁ at the graph argument
`w = −b²X^{2n−2}` is P-constructible for `n ∈ {2,…,6}`. This is the general form above
instantiated with the seed produced by `hyp_neg_half_arcLength_Pconstructible`. -/
-- Theorem: `PConstructible (deriv (hyp (-1/2) (1/(2n-2)) (1+1/(2n-2))) (-(b²X^(2n-2))))`.
@[pconstructible_cond]
theorem deriv_graphFamily_H6_Pconstructible {n : ℕ} (hn : 2 ≤ n) (hn6 : n ≤ 6) {b X : ℝ}
    (hb : PConstructible b) (hb0 : b ≠ 0) (hXP : PConstructible X) (hX0 : 0 < X)
    (hsmall : |b ^ 2 * X ^ (2 * n - 2)| < 1) :
    PConstructible
      (deriv (fun u => hyp (-(1 / 2)) (1 / ((2 * n - 2 : ℕ) : ℝ))
        (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) u) (-(b ^ 2 * X ^ (2 * n - 2)))) := by
  refine deriv_graphFamily_Pconstructible (m := 2 * n - 2) (by omega) (b := b) (X := X)
    (w := -(b ^ 2 * X ^ (2 * n - 2))) hb hb0 hXP hX0 rfl (by simpa only [abs_neg] using hsmall) ?_
  simpa only using hyp_neg_half_arcLength_Pconstructible hn hn6 hb hXP hX0 hsmall

/-! ### Step 2: the immediate contiguous neighbours

The shifts of `EllipticClass.lean` move one parameter at a time at the cost of a factor of `w`
and one derivative. With the derivative seed of Step 1 in hand, the five neighbours
`F(a−1,b,c)`, `F(a+1,b,c)`, `F(a,b−1,c)`, `F(a,b+1,c)` and `F(a,b,c+1)` are all
P-constructible. The `b`-down relation is not in `EllipticClass.lean`; it is `hyp_shift_a_down`
with the two numerators exchanged. -/

/-- **DLMF 15.5.20a for `b`**: on `|z| < 1`, for `a ≠ 0`, `c ∉ -ℕ` and `c ≠ b`,
`₂F₁(a,b-1;c;z) = (z(1-z) ₂F₁′(a,b;c;z) - (b-c+az) ₂F₁(a,b;c;z)) / (c-b)`.

This is `hyp_shift_a_down` at the exchanged parameters `(b, a)`, transported back through
`hyp_comm`. -/
-- Theorem: `hyp a (b-1) c z = (z*(1-z)*deriv (hyp a b c) z - (b-c+a*z)*hyp a b c z)/(c-b)`.
theorem hyp_shift_b_down {a b c z : ℝ} (ha : a ≠ 0) (hcb : c - b ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz : |z| < 1) :
    hyp a (b - 1) c z = (z * (1 - z) * deriv (fun w => hyp a b c w) z
      - (b - c + a * z) * hyp a b c z) / (c - b) := by
  have h := hyp_shift_a_down (a := b) (b := a) (c := c) ha hcb hc hz
  rw [hyp_comm (b - 1) a c z, hyp_comm b a c z] at h
  have hfun : (fun w => hyp b a c w) = (fun w => hyp a b c w) := by
    funext w; exact hyp_comm b a c w
  rwa [hfun] at h

/-- **Step 2 (L5b), general form.** If `F(a,b;c;w)` and its derivative at `w` are
P-constructible, then so are the five contiguous neighbours obtained by moving one
parameter by `±1` (the denominator only upwards). Every nonzero side condition is carried
explicitly, so this is usable at any non-degenerate parameter triple. -/
-- Theorem: the five neighbours `F(a±1,b,c)`, `F(a,b±1,c)`, `F(a,b,c+1)` are P-constructible.
theorem hyp_contiguous_neighbours_Pconstructible {a b c w : ℝ}
    (haP : PConstructible a) (hbP : PConstructible b) (hcP : PConstructible c)
    (hwP : PConstructible w) (ha : a ≠ 0) (hb : b ≠ 0) (hca : c - a ≠ 0) (hcb : c - b ≠ 0)
    (hc : ∀ k : ℕ, c ≠ -(k : ℝ)) (hc1 : ∀ k : ℕ, c + 1 ≠ -(k : ℝ))
    (hw : |w| < 1)
    (hF : PConstructible (hyp a b c w))
    (hF' : PConstructible (deriv (fun u => hyp a b c u) w)) :
    PConstructible (hyp (a - 1) b c w) ∧ PConstructible (hyp (a + 1) b c w) ∧
      PConstructible (hyp a (b - 1) c w) ∧ PConstructible (hyp a (b + 1) c w) ∧
      PConstructible (hyp a b (c + 1) w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hyp_shift_a_down (a := a) (b := b) (c := c) hb hca hc hw]
    pconstructible
  · rw [hyp_shift_a (a := a) (b := b) (c := c) ha hc hw]
    pconstructible
  · rw [hyp_shift_b_down (a := a) (b := b) (c := c) ha hcb hc hw]
    pconstructible
  · rw [hyp_shift_b (a := a) (b := b) (c := c) hb hc hw]
    pconstructible
  · rw [hyp_shift_c_up (a := a) (b := b) (c := c) hc hc1 hca hcb hw]
    pconstructible

/-- **Step 2 (L5b), H6 form.** For the H6 graph data `b ≠ 0`, `X > 0`, `n ∈ {2,…,6}`, the
five contiguous neighbours of the base value
`₂F₁(−½, 1/(2n−2); 1+1/(2n−2); −b²X^{2n−2})` are P-constructible. The seeds are the arc
length (`hyp_neg_half_arcLength_Pconstructible`) and its derivative
(`deriv_graphFamily_H6_Pconstructible`). -/
-- Theorem: the five H6 neighbours are P-constructible.
@[pconstructible_cond]
theorem hyp_graphFamily_neighbours_Pconstructible {n : ℕ} (hn : 2 ≤ n) (hn6 : n ≤ 6)
    {b X : ℝ} (hb : PConstructible b) (hb0 : b ≠ 0) (hXP : PConstructible X) (hX0 : 0 < X)
    (hsmall : |b ^ 2 * X ^ (2 * n - 2)| < 1) :
    PConstructible (hyp (-(1 / 2) - 1) (1 / ((2 * n - 2 : ℕ) : ℝ))
        (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) (-(b ^ 2 * X ^ (2 * n - 2)))) ∧
      PConstructible (hyp (-(1 / 2) + 1) (1 / ((2 * n - 2 : ℕ) : ℝ))
        (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) (-(b ^ 2 * X ^ (2 * n - 2)))) ∧
      PConstructible (hyp (-(1 / 2)) (1 / ((2 * n - 2 : ℕ) : ℝ) - 1)
        (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) (-(b ^ 2 * X ^ (2 * n - 2)))) ∧
      PConstructible (hyp (-(1 / 2)) (1 / ((2 * n - 2 : ℕ) : ℝ) + 1)
        (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) (-(b ^ 2 * X ^ (2 * n - 2)))) ∧
      PConstructible (hyp (-(1 / 2)) (1 / ((2 * n - 2 : ℕ) : ℝ))
        (1 + 1 / ((2 * n - 2 : ℕ) : ℝ) + 1) (-(b ^ 2 * X ^ (2 * n - 2)))) := by
  have hMpos : (0 : ℝ) < ((2 * n - 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * n - 2)
  have hca : (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) - (-(1 / 2)) ≠ 0 := by
    have h : 0 < 1 / ((2 * n - 2 : ℕ) : ℝ) := one_div_pos.mpr hMpos
    intro h0; linarith
  have hcb : (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) - 1 / ((2 * n - 2 : ℕ) : ℝ) ≠ 0 := by
    have h : (1 : ℝ) + 1 / ((2 * n - 2 : ℕ) : ℝ) - 1 / ((2 * n - 2 : ℕ) : ℝ) = 1 := by ring
    rw [h]; norm_num
  have hbne : 1 / ((2 * n - 2 : ℕ) : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hMpos)
  have hcpos : 0 < 1 + 1 / ((2 * n - 2 : ℕ) : ℝ) := by positivity
  have hcne : ∀ k : ℕ, (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) ≠ -(k : ℝ) := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hc1ne : ∀ k : ℕ, (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) + 1 ≠ -(k : ℝ) := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact hyp_contiguous_neighbours_Pconstructible (a := -(1 / 2))
    (b := 1 / ((2 * n - 2 : ℕ) : ℝ)) (c := 1 + 1 / ((2 * n - 2 : ℕ) : ℝ))
    (w := -(b ^ 2 * X ^ (2 * n - 2))) (by pconstructible)
    (PConstructible.div PConstructible.base_one (nat_Pconstructible (2 * n - 2)))
    (PConstructible.add PConstructible.base_one
      (PConstructible.div PConstructible.base_one (nat_Pconstructible (2 * n - 2))))
    (by pconstructible) (by norm_num) hbne hca hcb hcne hc1ne
    (by simpa only [abs_neg] using hsmall)
    (hyp_neg_half_arcLength_Pconstructible hn hn6 hb hXP hX0 hsmall)
    (deriv_graphFamily_H6_Pconstructible hn hn6 hb hb0 hXP hX0 hsmall)

/-! ### Step 3: the `k = 0` class of the H6 family

The five neighbours of Step 2 supply two consecutive seeds of the `a`-direction at the levels
`b₀ = 1/m` and `b₀ - 1` (`m = 2n - 2`); the three-term recurrences `hyp_three_term_a` /
`hyp_three_term_b` then propagate them over all of `ℤ²`. Two degeneracies need care:

* the target carries no `b ≠ 0`, so `b = 0` is handled separately (`w = 0`, all values `1`);
* at `b = b₀ + 2 = c₀ + 1` the recurrence coefficient `c - b + 1` vanishes, so that level is
  reached from `hyp_shift_b` at `b = c₀` instead, its derivative supplied by `hyp_shift_a_down`.

Only `w ≠ 0` (equivalently `b ≠ 0`) is used in the main branch, to read off the derivative at
the mixed seed `(a₀, b₀ - 1)`. -/

/-- `hyp a b c 0 = 1`: evaluating the hypergeometric series at the origin. -/
lemma hyp_at_zero (a b c : ℝ) : hyp a b c 0 = 1 := by
  rw [hyp_eq_tsum_coeff, tsum_eq_single 0 (fun k hk => by rw [zero_pow hk, mul_zero])]
  simp [hypCoeff, ordinaryHypergeometricCoefficient]

-- Theorem: for `n ∈ {3,…,6}`, P-constructible `b, X` with `X > 0` and `|b²X^(2n-2)| < 1`,
-- the H6 ₂F₁ is P-constructible at every `(-1/2 + i, 1/(2n-2) + j; 1 + 1/(2n-2))`.
set_option maxHeartbeats 1000000 in
-- The two strong inductions below carry a very large local context; the default 200000 is
-- not enough (the proof failed with a deterministic `whnf` timeout).
@[pconstructible_cond]
theorem hyp_graphFamily_level_zero_Pconstructible {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≤ 6)
    {b X : ℝ} (hb : PConstructible b) (hX : PConstructible X) (hXpos : 0 < X)
    (hsmall : |b ^ 2 * X ^ (2 * n - 2)| < 1) {i j : ℤ} :
    PConstructible (hyp (-(1 / 2) + i) (1 / ((2 * n - 2 : ℕ) : ℝ) + j)
      (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) (-(b ^ 2 * X ^ (2 * n - 2)))) := by
  by_cases hbzero : b = 0
  · subst hbzero
    have h0 : -(0 ^ 2 * X ^ (2 * n - 2)) = 0 := by ring
    rw [h0, hyp_at_zero]
    exact PConstructible.base_one
  · set M : ℕ := 2 * n - 2 with hM
    set a₀ : ℝ := -(1/2) with ha₀
    set b₀ : ℝ := 1 / ((M : ℝ)) with hb₀
    set c₀ : ℝ := 1 + 1 / ((M : ℝ)) with hc₀
    set w : ℝ := -(b ^ 2 * X ^ M) with hw_def
    have ha₀E : a₀ = -(1 / 2) := ha₀
    have hb₀E : b₀ = 1 / ((2 * n - 2 : ℕ) : ℝ) := by rw [hb₀, hM]
    have hc₀E : c₀ = 1 + 1 / ((2 * n - 2 : ℕ) : ℝ) := by rw [hc₀, hM]
    have hwE : w = -(b ^ 2 * X ^ (2 * n - 2)) := by rw [hw_def, hM]
    have hMP : PConstructible (M : ℝ) := nat_Pconstructible M
    have ha₀P : PConstructible a₀ := by rw [ha₀E]; pconstructible
    have hb₀P : PConstructible b₀ := by rw [hb₀E]; pconstructible
    have hc₀P : PConstructible c₀ := by rw [hc₀E]; pconstructible
    have hwP : PConstructible w := by rw [hwE]; pconstructible
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hb₀pos : 0 < b₀ := by rw [hb₀E]; positivity
    have hb₀lt1 : b₀ < 1 := by
      rw [hb₀E, div_lt_one hMpos]
      exact_mod_cast (by omega : 1 < M)
    have hb₀ne : b₀ ≠ 0 := ne_of_gt hb₀pos
    have hb₀m1ne : b₀ - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hb₀lt1)
    have hb₀p1ne : b₀ + 1 ≠ 0 := by linarith
    have hb₀p1ne1 : b₀ + 1 ≠ 1 := by linarith
    have hc₀ne : c₀ ≠ 0 := by rw [hc₀E]; positivity
    have hc₀pos : 0 < c₀ := by rw [hc₀E]; positivity
    have hc : ∀ k : ℕ, c₀ ≠ -(k : ℝ) := by
      intro k hk
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hwneg : w < 0 := by
      rw [hwE]
      have h1 : 0 < b ^ 2 * X ^ (2 * n - 2) :=
        mul_pos (sq_pos_of_ne_zero hbzero) (pow_pos hXpos _)
      linarith
    have hwne0 : w ≠ 0 := ne_of_lt hwneg
    have hwne1 : w ≠ 1 := by intro h; linarith
    have hwabs : |w| < 1 := by rw [hwE]; simpa only [abs_neg] using hsmall
    -- `b₀ + k` is never `0` or `1` for an integer `k`, since `0 < b₀ < 1`.
    have hsum_ne_zero : ∀ k : ℤ, b₀ + (k : ℝ) ≠ 0 := by
      intro k hk
      by_cases hk0 : k ≤ 0
      · rcases eq_or_lt_of_le hk0 with hkzero | hkneg
        · subst hkzero; exact hb₀ne (by simpa using hk)
        · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
          linarith
      · have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
        linarith
    have hsum_ne_one : ∀ k : ℤ, b₀ + (k : ℝ) ≠ 1 := by
      intro k hk
      by_cases hk0 : k ≤ 0
      · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
        linarith
      · have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
        linarith
    -- `c₀ - a₀ = 3/2 + 1/M` is not an integer.
    have hca_notInt : ∀ k : ℤ, c₀ - a₀ ≠ (k : ℝ) := by
      intro k hk
      rw [ha₀, hc₀] at hk
      have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
      have h1 : (1 : ℝ) / (M : ℝ) = (k : ℝ) - 3 / 2 := by linarith
      have h3 : (M : ℝ) * ((k : ℝ) - 3 / 2) = 1 := by
        rw [← h1]; field_simp
      have hR : ((M : ℤ) * (2 * k - 3) : ℝ) = 2 := by
        push_cast
        nlinarith [h3]
      have hInt : (M : ℤ) * (2 * k - 3) = 2 := by exact_mod_cast hR
      have hdvd : (M : ℤ) ∣ (2 : ℤ) := ⟨2 * k - 3, hInt.symm⟩
      have hle : (M : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
      have h4 : (4 : ℤ) ≤ (M : ℤ) := by exact_mod_cast (by omega : 4 ≤ M)
      omega
    -- The seeds: the base value and its five contiguous neighbours.
    have h00 : PConstructible (hyp a₀ b₀ c₀ w) := by
      rw [ha₀E, hb₀E, hc₀E, hwE]
      exact hyp_neg_half_arcLength_Pconstructible (n := n) (by omega) hn6 hb hX hXpos hsmall
    obtain ⟨hEm, hAp, hEm0, hAp0, _⟩ :=
      hyp_graphFamily_neighbours_Pconstructible (n := n) (by omega) hn6 hb hbzero hX hXpos hsmall
    have hE : PConstructible (hyp (a₀ - 1) b₀ c₀ w) := by
      rw [ha₀E, hb₀E, hc₀E, hwE]; exact hEm
    have hA : PConstructible (hyp (a₀ + 1) b₀ c₀ w) := by
      rw [ha₀E, hb₀E, hc₀E, hwE]; exact hAp
    have hE0 : PConstructible (hyp a₀ (b₀ - 1) c₀ w) := by
      rw [ha₀E, hb₀E, hc₀E, hwE]; exact hEm0
    have hA0 : PConstructible (hyp a₀ (b₀ + 1) c₀ w) := by
      rw [ha₀E, hb₀E, hc₀E, hwE]; exact hAp0
    -- Two consecutive seeds at a fixed level determine the whole `a`-line.
    have hprop : ∀ (β : ℝ), PConstructible β → β ≠ 0 →
        PConstructible (hyp (a₀ - 1) β c₀ w) →
        PConstructible (hyp a₀ β c₀ w) →
        ∀ i : ℤ, PConstructible (hyp (a₀ + (i : ℝ)) β c₀ w) := by
      intro β hβP hβ hseedm hseed0
      have hUp : ∀ i : ℤ, -1 ≤ i → PConstructible (hyp (a₀ + (i : ℝ)) β c₀ w) := by
        have hM2 : ∀ i : ℤ, -1 ≤ i →
            PConstructible (hyp (a₀ + (i : ℝ)) β c₀ w) ∧
              PConstructible (hyp (a₀ + (i : ℝ) + 1) β c₀ w) :=
          Int.leInduction (motive := fun i _ =>
              PConstructible (hyp (a₀ + (i : ℝ)) β c₀ w) ∧
                PConstructible (hyp (a₀ + (i : ℝ) + 1) β c₀ w))
            (by
              refine ⟨?_, ?_⟩
              · rw [show a₀ + ((-1 : ℤ) : ℝ) = a₀ - 1 by push_cast; ring]; exact hseedm
              · rw [show a₀ + ((-1 : ℤ) : ℝ) + 1 = a₀ by push_cast; ring]; exact hseed0)
            (fun i _ hMi => by
              refine ⟨?_, ?_⟩
              · rw [show a₀ + ((i + 1 : ℤ) : ℝ) = a₀ + (i : ℝ) + 1 by push_cast; ring]
                exact hMi.2
              · rw [show a₀ + ((i + 1 : ℤ) : ℝ) + 1 = a₀ + (i : ℝ) + 2 by push_cast; ring]
                have hA1 : a₀ + (i : ℝ) + 2 ≠ 1 := by
                  rw [ha₀E]; intro hcon
                  have h2 : ((2 * i + 3 : ℤ) : ℝ) = 2 := by push_cast; linarith
                  have h3 : (2 * i + 3 : ℤ) = 2 := by exact_mod_cast h2
                  omega
                have hca : c₀ - (a₀ + (i : ℝ) + 2) + 1 ≠ 0 := by
                  have hk := hca_notInt (i + 1)
                  intro hcon
                  apply hk
                  push_cast at hcon ⊢
                  linarith
                have hden : (a₀ + (i : ℝ) + 1) * (1 - w) ≠ 0 := by
                  refine mul_ne_zero ?_ (sub_ne_zero.mpr (Ne.symm hwne1))
                  rw [ha₀E]; intro hcon
                  have h2 : ((2 * i + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
                  have h3 : (2 * i + 1 : ℤ) = 0 := by exact_mod_cast h2
                  omega
                have hrec := hyp_three_term_a (a := a₀ + (i : ℝ) + 2) (b := β) (c := c₀)
                  (z := w) hA1 hβ hca hc hwabs hwne1
                rw [show a₀ + (i : ℝ) + 2 - 2 = a₀ + (i : ℝ) by ring,
                    show a₀ + (i : ℝ) + 2 - 1 = a₀ + (i : ℝ) + 1 by ring] at hrec
                have heq : hyp (a₀ + (i : ℝ) + 2) β c₀ w =
                    ((c₀ - (a₀ + (i : ℝ) + 2) + 1) * hyp (a₀ + (i : ℝ)) β c₀ w
                      + (2 * (a₀ + (i : ℝ) + 1) - c₀
                          + w * (β - (a₀ + (i : ℝ) + 2) + 1))
                        * hyp (a₀ + (i : ℝ) + 1) β c₀ w)
                      / ((a₀ + (i : ℝ) + 1) * (1 - w)) := by
                  rw [eq_div_iff hden]
                  linear_combination hrec
                rw [heq]
                have hiP : PConstructible (i : ℝ) := int_Pconstructible i
                pconstructible)
        intro i hi
        exact (hM2 i hi).1
      have hDown : ∀ i : ℤ, i ≤ -1 → PConstructible (hyp (a₀ + (i : ℝ)) β c₀ w) := by
        have hM2 : ∀ i : ℤ, i ≤ -1 →
            PConstructible (hyp (a₀ + (i : ℝ)) β c₀ w) ∧
              PConstructible (hyp (a₀ + (i : ℝ) + 1) β c₀ w) :=
          Int.leInductionDown (motive := fun i _ =>
              PConstructible (hyp (a₀ + (i : ℝ)) β c₀ w) ∧
                PConstructible (hyp (a₀ + (i : ℝ) + 1) β c₀ w))
            (by
              refine ⟨?_, ?_⟩
              · rw [show a₀ + ((-1 : ℤ) : ℝ) = a₀ - 1 by push_cast; ring]; exact hseedm
              · rw [show a₀ + ((-1 : ℤ) : ℝ) + 1 = a₀ by push_cast; ring]; exact hseed0)
            (fun i _ hMi => by
              refine ⟨?_, ?_⟩
              · rw [show a₀ + ((i - 1 : ℤ) : ℝ) = a₀ + (i : ℝ) - 1 by push_cast; ring]
                have hA1 : a₀ + (i : ℝ) + 1 ≠ 1 := by
                  rw [ha₀E]; intro hcon
                  have h2 : ((2 * i + 1 : ℤ) : ℝ) = 2 := by push_cast; linarith
                  have h3 : (2 * i + 1 : ℤ) = 2 := by exact_mod_cast h2
                  omega
                have hca : c₀ - (a₀ + (i : ℝ) + 1) + 1 ≠ 0 := by
                  have hk := hca_notInt i
                  intro hcon
                  apply hk
                  linarith
                have hrec := hyp_three_term_a (a := a₀ + (i : ℝ) + 1) (b := β) (c := c₀)
                  (z := w) hA1 hβ hca hc hwabs hwne1
                rw [show a₀ + (i : ℝ) + 1 - 2 = a₀ + (i : ℝ) - 1 by ring,
                    show a₀ + (i : ℝ) + 1 - 1 = a₀ + (i : ℝ) by ring] at hrec
                have heq : hyp (a₀ + (i : ℝ) - 1) β c₀ w =
                    ((a₀ + (i : ℝ)) * (1 - w) * hyp (a₀ + (i : ℝ) + 1) β c₀ w
                      - (2 * (a₀ + (i : ℝ)) - c₀ + w * (β - (a₀ + (i : ℝ) + 1) + 1))
                        * hyp (a₀ + (i : ℝ)) β c₀ w)
                      / (c₀ - (a₀ + (i : ℝ) + 1) + 1) := by
                  rw [eq_div_iff hca]
                  linear_combination (-1) * hrec
                rw [heq]
                have hiP : PConstructible (i : ℝ) := int_Pconstructible i
                pconstructible
              · rw [show a₀ + ((i - 1 : ℤ) : ℝ) + 1 = a₀ + (i : ℝ) by push_cast; ring]
                exact hMi.1)
        intro i hi
        exact (hM2 i hi).1
      intro i
      by_cases hi : -1 ≤ i
      · exact hUp i hi
      · exact hDown i (by omega)
    -- Mixed seed: the derivative at `(a₀, b₀ - 1)`, from the `b`-up shift.
    have hderE0 : PConstructible (deriv (fun u => hyp a₀ (b₀ - 1) c₀ u) w) := by
      have hshift := hyp_shift_b (a := a₀) (b := b₀ - 1) (c := c₀) (z := w)
        hb₀m1ne hc hwabs
      rw [show b₀ - 1 + 1 = b₀ by ring] at hshift
      have heq : deriv (fun u => hyp a₀ (b₀ - 1) c₀ u) w
          = (b₀ - 1) * (hyp a₀ b₀ c₀ w - hyp a₀ (b₀ - 1) c₀ w) / w := by
        rw [eq_div_iff hwne0]
        field_simp at hshift
        nlinarith [hshift]
      rw [heq]
      pconstructible
    have hC : PConstructible (hyp (a₀ - 1) (b₀ - 1) c₀ w) := by
      have hca : c₀ - a₀ ≠ 0 := by simpa using hca_notInt 0
      have hshift := hyp_shift_a_down (a := a₀) (b := b₀ - 1) (c := c₀) (z := w)
        hb₀m1ne hca hc hwabs
      rw [hshift]
      pconstructible
    have hB : PConstructible (hyp (a₀ + 1) (b₀ - 1) c₀ w) := by
      have ha₀ne : a₀ ≠ 0 := by rw [ha₀E]; norm_num
      have hshift := hyp_shift_a (a := a₀) (b := b₀ - 1) (c := c₀) (z := w)
        ha₀ne hc hwabs
      rw [hshift]
      pconstructible
    -- The remaining two level-`1` corners, from the `b`-recurrence at `b₀ + 1`.
    have hB' : PConstructible (hyp (a₀ - 1) (b₀ + 1) c₀ w) := by
      have ha : a₀ - 1 ≠ 0 := by rw [ha₀E]; norm_num
      have hcb : c₀ - (b₀ + 1) + 1 ≠ 0 := by
        have heq : c₀ - (b₀ + 1) + 1 = 1 := by rw [hc₀, hb₀]; ring
        rw [heq]; norm_num
      have hden : b₀ * (1 - w) ≠ 0 :=
        mul_ne_zero hb₀ne (sub_ne_zero.mpr (Ne.symm hwne1))
      have hrec := hyp_three_term_b (a := a₀ - 1) (b := b₀ + 1) (c := c₀) (z := w)
        hb₀p1ne1 ha hcb hc hwabs hwne1
      rw [show b₀ + 1 - 1 = b₀ by ring, show b₀ + 1 - 2 = b₀ - 1 by ring] at hrec
      have heq : hyp (a₀ - 1) (b₀ + 1) c₀ w =
          ((c₀ - (b₀ + 1) + 1) * hyp (a₀ - 1) (b₀ - 1) c₀ w
            + (2 * b₀ - c₀ + w * ((a₀ - 1) - (b₀ + 1) + 1)) * hyp (a₀ - 1) b₀ c₀ w)
            / (b₀ * (1 - w)) := by
        rw [eq_div_iff hden]
        linear_combination hrec
      rw [heq]
      pconstructible
    have h11 : PConstructible (hyp (a₀ + 1) (b₀ + 1) c₀ w) := by
      have ha : a₀ + 1 ≠ 0 := by rw [ha₀E]; norm_num
      have hcb : c₀ - (b₀ + 1) + 1 ≠ 0 := by
        have heq : c₀ - (b₀ + 1) + 1 = 1 := by rw [hc₀, hb₀]; ring
        rw [heq]; norm_num
      have hden : b₀ * (1 - w) ≠ 0 :=
        mul_ne_zero hb₀ne (sub_ne_zero.mpr (Ne.symm hwne1))
      have hrec := hyp_three_term_b (a := a₀ + 1) (b := b₀ + 1) (c := c₀) (z := w)
        hb₀p1ne1 ha hcb hc hwabs hwne1
      rw [show b₀ + 1 - 1 = b₀ by ring, show b₀ + 1 - 2 = b₀ - 1 by ring] at hrec
      have heq : hyp (a₀ + 1) (b₀ + 1) c₀ w =
          ((c₀ - (b₀ + 1) + 1) * hyp (a₀ + 1) (b₀ - 1) c₀ w
            + (2 * b₀ - c₀ + w * ((a₀ + 1) - (b₀ + 1) + 1)) * hyp (a₀ + 1) b₀ c₀ w)
            / (b₀ * (1 - w)) := by
        rw [eq_div_iff hden]
        linear_combination hrec
      rw [heq]
      pconstructible
    -- The degenerate level `b₀ + 2 = c₀ + 1`, reached through `hyp_shift_b` at `b = c₀`.
    have h02 : PConstructible (hyp a₀ (b₀ + 2) c₀ w) := by
      have hbpeq : b₀ + 1 = c₀ := by rw [hc₀, hb₀]; ring
      have hfun : hyp a₀ c₀ c₀ w = hyp a₀ (b₀ + 1) c₀ w := by rw [hbpeq]
      have ha_val : PConstructible (hyp a₀ c₀ c₀ w) := by rw [hfun]; exact hA0
      have hfun2 : hyp (a₀ - 1) c₀ c₀ w = hyp (a₀ - 1) (b₀ + 1) c₀ w := by rw [hbpeq]
      have hm_val : PConstructible (hyp (a₀ - 1) c₀ c₀ w) := by rw [hfun2]; exact hB'
      have hcane : c₀ - a₀ ≠ 0 := by simpa using hca_notInt 0
      have hshift := hyp_shift_a_down (a := a₀) (b := c₀) (c := c₀) (z := w)
        hc₀ne hcane hc hwabs
      have hD : deriv (fun u => hyp a₀ c₀ c₀ u) w
          = ((c₀ - a₀) * hyp (a₀ - 1) c₀ c₀ w + (a₀ - c₀ + c₀ * w) * hyp a₀ c₀ c₀ w)
            / (w * (1 - w)) := by
        rw [eq_div_iff (mul_ne_zero hwne0 (sub_ne_zero.mpr (Ne.symm hwne1)))]
        rw [eq_div_iff hcane] at hshift
        linear_combination (-1) * hshift
      have hshift2 := hyp_shift_b (a := a₀) (b := c₀) (c := c₀) (z := w) hc₀ne hc hwabs
      rw [show b₀ + 2 = c₀ + 1 by rw [hc₀, hb₀]; ring]
      rw [hshift2, hD]
      pconstructible
    have hb₀m1P : PConstructible (b₀ - 1) := by pconstructible
    let L : ℤ → Prop := fun j =>
      ∀ i : ℤ, PConstructible (hyp (a₀ + (i : ℝ)) (b₀ + (j : ℝ)) c₀ w)
    have hL0 : L 0 := by
      intro i
      simpa using hprop b₀ hb₀P hb₀ne hE h00 i
    have hLm1 : L (-1) := by
      intro i
      rw [show b₀ + ((-1 : ℤ) : ℝ) = b₀ - 1 by push_cast; ring]
      exact hprop (b₀ - 1) hb₀m1P hb₀m1ne hC hE0 i
    -- The `b`-direction: `L (j+2)` from `L j` and `L (j+1)`, valid for `j ≠ 0`.
    have recurB : ∀ j : ℤ, j ≠ 0 → L j → L (j + 1) → L (j + 2) := by
      intro j hj0 hLj hLj1 i
      have hb1 : b₀ + (j : ℝ) + 2 ≠ 1 := by
        have h := hsum_ne_one (j + 2)
        rwa [show b₀ + ((j + 2 : ℤ) : ℝ) = b₀ + (j : ℝ) + 2 by push_cast; ring] at h
      have ha : a₀ + (i : ℝ) ≠ 0 := by
        rw [ha₀E]; intro hcon
        have h2 : ((2 * i - 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
        have h3 : (2 * i - 1 : ℤ) = 0 := by exact_mod_cast h2
        omega
      have hcb : c₀ - (b₀ + (j : ℝ) + 2) + 1 ≠ 0 := by
        have heq : c₀ - (b₀ + (j : ℝ) + 2) + 1 = -(j : ℝ) := by rw [hc₀, hb₀]; ring
        rw [heq]
        intro hcon
        exact hj0 (by exact_mod_cast (neg_eq_zero.mp hcon))
      have hden : (b₀ + (j : ℝ) + 1) * (1 - w) ≠ 0 := by
        refine mul_ne_zero ?_ (sub_ne_zero.mpr (Ne.symm hwne1))
        have h := hsum_ne_zero (j + 1)
        rwa [show b₀ + ((j + 1 : ℤ) : ℝ) = b₀ + (j : ℝ) + 1 by push_cast; ring] at h
      have hrec := hyp_three_term_b (a := a₀ + (i : ℝ)) (b := b₀ + (j : ℝ) + 2)
        (c := c₀) (z := w) hb1 ha hcb hc hwabs hwne1
      rw [show b₀ + (j : ℝ) + 2 - 2 = b₀ + (j : ℝ) by ring,
          show b₀ + (j : ℝ) + 2 - 1 = b₀ + (j : ℝ) + 1 by ring] at hrec
      have heq : hyp (a₀ + (i : ℝ)) (b₀ + (j : ℝ) + 2) c₀ w =
          ((c₀ - (b₀ + (j : ℝ) + 2) + 1) * hyp (a₀ + (i : ℝ)) (b₀ + (j : ℝ)) c₀ w
            + (2 * (b₀ + (j : ℝ) + 1) - c₀
                + w * ((a₀ + (i : ℝ)) - (b₀ + (j : ℝ) + 2) + 1))
              * hyp (a₀ + (i : ℝ)) (b₀ + (j : ℝ) + 1) c₀ w)
            / ((b₀ + (j : ℝ) + 1) * (1 - w)) := by
        rw [eq_div_iff hden]
        linear_combination hrec
      have hLj1' : PConstructible (hyp (a₀ + (i : ℝ)) (b₀ + (j : ℝ) + 1) c₀ w) := by
        simpa only [show b₀ + ((j + 1 : ℤ) : ℝ) = b₀ + (j : ℝ) + 1 by push_cast; ring]
          using hLj1 i
      rw [show b₀ + ((j + 2 : ℤ) : ℝ) = b₀ + (j : ℝ) + 2 by push_cast; ring]
      rw [heq]
      have hiP : PConstructible (i : ℝ) := int_Pconstructible i
      have hjP : PConstructible (j : ℝ) := int_Pconstructible j
      pconstructible
    -- Downward: `L (j-1)` from `L j` and `L (j+1)` for `j ≤ -1`.
    have recurBdown : ∀ j : ℤ, j ≤ -1 → L j → L (j + 1) → L (j - 1) := by
      intro j hj hLj hLj1 i
      have hb1 : b₀ + (j : ℝ) + 1 ≠ 1 := by
        have h := hsum_ne_one (j + 1)
        rwa [show b₀ + ((j + 1 : ℤ) : ℝ) = b₀ + (j : ℝ) + 1 by push_cast; ring] at h
      have ha : a₀ + (i : ℝ) ≠ 0 := by
        rw [ha₀E]; intro hcon
        have h2 : ((2 * i - 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
        have h3 : (2 * i - 1 : ℤ) = 0 := by exact_mod_cast h2
        omega
      have hcb : c₀ - (b₀ + (j : ℝ) + 1) + 1 ≠ 0 := by
        have heq : c₀ - (b₀ + (j : ℝ) + 1) + 1 = 1 - (j : ℝ) := by rw [hc₀, hb₀]; ring
        rw [heq]
        intro hcon
        have hjR : (j : ℝ) ≤ -1 := by exact_mod_cast hj
        linarith
      have hrec := hyp_three_term_b (a := a₀ + (i : ℝ)) (b := b₀ + (j : ℝ) + 1)
        (c := c₀) (z := w) hb1 ha hcb hc hwabs hwne1
      rw [show b₀ + (j : ℝ) + 1 - 1 = b₀ + (j : ℝ) by ring,
          show b₀ + (j : ℝ) + 1 - 2 = b₀ + (j : ℝ) - 1 by ring] at hrec
      have heq : hyp (a₀ + (i : ℝ)) (b₀ + (j : ℝ) - 1) c₀ w =
          ((b₀ + (j : ℝ)) * (1 - w) * hyp (a₀ + (i : ℝ)) (b₀ + (j : ℝ) + 1) c₀ w
            - (2 * (b₀ + (j : ℝ)) - c₀ + w * ((a₀ + (i : ℝ)) - (b₀ + (j : ℝ))))
              * hyp (a₀ + (i : ℝ)) (b₀ + (j : ℝ)) c₀ w)
            / (c₀ - (b₀ + (j : ℝ) + 1) + 1) := by
        rw [eq_div_iff hcb]
        linear_combination (-1) * hrec
      have hLj1' : PConstructible (hyp (a₀ + (i : ℝ)) (b₀ + (j : ℝ) + 1) c₀ w) := by
        simpa only [show b₀ + ((j + 1 : ℤ) : ℝ) = b₀ + (j : ℝ) + 1 by push_cast; ring]
          using hLj1 i
      rw [show b₀ + ((j - 1 : ℤ) : ℝ) = b₀ + (j : ℝ) - 1 by push_cast; ring]
      rw [heq]
      have hiP : PConstructible (i : ℝ) := int_Pconstructible i
      have hjP : PConstructible (j : ℝ) := int_Pconstructible j
      pconstructible
    have hL1 : L 1 := by
      have h := recurB (-1) (by norm_num) hLm1
        (by simpa only [show (-1 : ℤ) + 1 = 0 by norm_num] using hL0)
      rwa [show (-1 : ℤ) + 2 = 1 by norm_num] at h
    -- Level `b₀ + 2 = c₀ + 1`, where the recurrence degenerates.
    have hL2 : L 2 := by
      intro i
      have hbpeq : b₀ + 1 = c₀ := by rw [hc₀, hb₀]; ring
      have ha_val : PConstructible (hyp (a₀ + (i : ℝ)) c₀ c₀ w) := by
        have h := hL1 i
        rwa [show b₀ + ((1 : ℤ) : ℝ) = b₀ + 1 by norm_num, hbpeq] at h
      have hm_val : PConstructible (hyp (a₀ + (i : ℝ) - 1) c₀ c₀ w) := by
        have h := hL1 (i - 1)
        rwa [show a₀ + ((i - 1 : ℤ) : ℝ) = a₀ + (i : ℝ) - 1 by push_cast; ring,
             show b₀ + ((1 : ℤ) : ℝ) = b₀ + 1 by norm_num, hbpeq] at h
      have hcane : c₀ - (a₀ + (i : ℝ)) ≠ 0 := by
        have hk := hca_notInt i
        intro hcon; apply hk; linarith
      have hshift := hyp_shift_a_down (a := a₀ + (i : ℝ)) (b := c₀) (c := c₀) (z := w)
        hc₀ne hcane hc hwabs
      have hD : deriv (fun u => hyp (a₀ + (i : ℝ)) c₀ c₀ u) w
          = ((c₀ - (a₀ + (i : ℝ))) * hyp (a₀ + (i : ℝ) - 1) c₀ c₀ w
              + ((a₀ + (i : ℝ)) - c₀ + c₀ * w) * hyp (a₀ + (i : ℝ)) c₀ c₀ w)
            / (w * (1 - w)) := by
        rw [eq_div_iff (mul_ne_zero hwne0 (sub_ne_zero.mpr (Ne.symm hwne1)))]
        rw [eq_div_iff hcane] at hshift
        linear_combination (-1) * hshift
      have hshift2 := hyp_shift_b (a := a₀ + (i : ℝ)) (b := c₀) (c := c₀) (z := w)
        hc₀ne hc hwabs
      rw [show b₀ + ((2 : ℤ) : ℝ) = c₀ + 1 by push_cast; rw [hc₀, hb₀]; ring]
      rw [hshift2, hD]
      have hiP : PConstructible (i : ℝ) := int_Pconstructible i
      pconstructible
    have hUp : ∀ j : ℤ, -1 ≤ j → L j := by
      have hM2 : ∀ j : ℤ, -1 ≤ j → L j ∧ L (j + 1) :=
        Int.leInduction (motive := fun j _ => L j ∧ L (j + 1))
          ⟨hLm1, hL0⟩
          (fun j _ hMj => by
            refine ⟨hMj.2, ?_⟩
            rw [show j + 1 + 1 = j + 2 by ring]
            by_cases hj1 : j = -1
            · subst hj1; simpa using hL1
            · by_cases hj0 : j = 0
              · subst hj0; simpa using hL2
              · exact recurB j hj0 hMj.1 hMj.2)
      intro j hj
      exact (hM2 j hj).1
    have hDown : ∀ j : ℤ, j ≤ -1 → L j := by
      have hM2 : ∀ j : ℤ, j ≤ -1 → L j ∧ L (j + 1) :=
        Int.leInductionDown (motive := fun j _ => L j ∧ L (j + 1))
          ⟨hLm1, hL0⟩
          (fun j hj hNj => by
            refine ⟨recurBdown j hj hNj.1 hNj.2, ?_⟩
            rw [show j - 1 + 1 = j by ring]
            exact hNj.1)
      intro j hj
      exact (hM2 j hj).1
    by_cases hj : -1 ≤ j
    · exact hUp j hj i
    · exact hDown j (by omega) i

/-! ### Step 4: advancing the denominator `c = 1 + 1/m + k`

With the whole level `c = c₀ = 1 + 1/m` in hand, `hyp_shift_c_up` advances the denominator
one step at a time. Its right-hand side needs `₂F₁′(a,b;c;·)`, which `hyp_shift_a_down`
expresses at the same level as `((c-a) ₂F₁(a-1,b;c;·) + (a-c+bz) ₂F₁(a,b;c;·))/(z(1-z))`;
each step therefore consumes the two level-`c` values `a-1` and `a`. At `b = b₀ + k + 1`
the denominator of the `b`-shift degenerates, so that single corner is reached through the
`b`-recurrence `hyp_three_term_b` instead. -/

-- Theorem (L5b): for `n ∈ {3,…,6}`, P-constructible `b, X` with `X > 0` and
-- `|b²X^(2n-2)| < 1`, `₂F₁(-1/2+i, 1/(2n-2)+j; 1+1/(2n-2)+k; -(b²X^(2n-2)))` is
-- P-constructible for all `i, j : ℤ` and `k : ℕ`.
set_option maxHeartbeats 1000000 in
-- The induction below carries the whole level-zero context plus a dozen new local
-- hypotheses; the default heartbeat budget is not enough.
@[pconstructible_cond]
theorem hyp_graphFamily_class_Pconstructible {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≤ 6)
    {b X : ℝ} (hb : PConstructible b) (hX : PConstructible X) (hXpos : 0 < X)
    (hsmall : |b ^ 2 * X ^ (2 * n - 2)| < 1) {i j : ℤ} {k : ℕ} :
    PConstructible (hyp (-(1 / 2) + i) (1 / ((2 * n - 2 : ℕ) : ℝ) + j)
      (1 + 1 / ((2 * n - 2 : ℕ) : ℝ) + k) (-(b ^ 2 * X ^ (2 * n - 2)))) := by
  by_cases hbzero : b = 0
  · subst hbzero
    have h0 : -(0 ^ 2 * X ^ (2 * n - 2)) = 0 := by ring
    rw [h0, hyp_at_zero]
    exact PConstructible.base_one
  · set M : ℕ := 2 * n - 2 with hM
    set a₀ : ℝ := -(1 / 2) with ha₀
    set b₀ : ℝ := 1 / ((M : ℝ)) with hb₀
    set c₀ : ℝ := 1 + 1 / ((M : ℝ)) with hc₀
    set w : ℝ := -(b ^ 2 * X ^ M) with hw_def
    have ha₀E : a₀ = -(1 / 2) := ha₀
    have hb₀E : b₀ = 1 / ((2 * n - 2 : ℕ) : ℝ) := by rw [hb₀, hM]
    have hc₀E : c₀ = 1 + 1 / ((2 * n - 2 : ℕ) : ℝ) := by rw [hc₀, hM]
    have hwE : w = -(b ^ 2 * X ^ (2 * n - 2)) := by rw [hw_def, hM]
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hMP : PConstructible (M : ℝ) := nat_Pconstructible M
    have ha₀P : PConstructible a₀ := by rw [ha₀E]; pconstructible
    have hb₀P : PConstructible b₀ := by rw [hb₀E]; pconstructible
    have hc₀P : PConstructible c₀ := by rw [hc₀E]; pconstructible
    have hwP : PConstructible w := by rw [hwE]; pconstructible
    have hb₀pos : 0 < b₀ := by rw [hb₀E]; positivity
    have hb₀lt1 : b₀ < 1 := by
      rw [hb₀E, div_lt_one hMpos]
      exact_mod_cast (by omega : 1 < M)
    have hb₀ne : b₀ ≠ 0 := ne_of_gt hb₀pos
    have hc₀pos : 0 < c₀ := by rw [hc₀E]; positivity
    have hwneg : w < 0 := by
      rw [hwE]
      have h1 : 0 < b ^ 2 * X ^ (2 * n - 2) :=
        mul_pos (sq_pos_of_ne_zero hbzero) (pow_pos hXpos _)
      linarith
    have hwne0 : w ≠ 0 := ne_of_lt hwneg
    have hwne1 : w ≠ 1 := by intro h; linarith
    have hwabs : |w| < 1 := by rw [hwE]; simpa only [abs_neg] using hsmall
    -- `b₀ + k` is never `0`, since `0 < b₀ < 1`.
    have hsum_ne_zero : ∀ k : ℤ, b₀ + (k : ℝ) ≠ 0 := by
      intro k hk
      by_cases hk0 : k ≤ 0
      · rcases eq_or_lt_of_le hk0 with hkzero | hkneg
        · subst hkzero; exact hb₀ne (by simpa using hk)
        · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
          linarith
      · have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
        linarith
    -- `c₀ - a₀ = 3/2 + 1/M` is not an integer.
    have hca_notInt : ∀ k : ℤ, c₀ - a₀ ≠ (k : ℝ) := by
      intro k hk
      rw [ha₀, hc₀] at hk
      have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
      have h1 : (1 : ℝ) / (M : ℝ) = (k : ℝ) - 3 / 2 := by linarith
      have h3 : (M : ℝ) * ((k : ℝ) - 3 / 2) = 1 := by
        rw [← h1]; field_simp
      have hR : ((M : ℤ) * (2 * k - 3) : ℝ) = 2 := by
        push_cast
        nlinarith [h3]
      have hInt : (M : ℤ) * (2 * k - 3) = 2 := by exact_mod_cast hR
      have hdvd : (M : ℤ) ∣ (2 : ℤ) := ⟨2 * k - 3, hInt.symm⟩
      have hle : (M : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
      have h4 : (4 : ℤ) ≤ (M : ℤ) := by exact_mod_cast (by omega : 4 ≤ M)
      omega
    have hmain : ∀ k : ℕ, ∀ i j : ℤ,
        PConstructible (hyp (a₀ + (i : ℝ)) (b₀ + (j : ℝ)) (c₀ + (k : ℝ)) w) := by
      intro k
      induction k with
      | zero =>
        intro i j
        simpa only [ha₀E, hb₀E, hc₀E, hwE, Nat.cast_zero, add_zero] using
          hyp_graphFamily_level_zero_Pconstructible hn hn6 hb hX hXpos hsmall
            (i := i) (j := j)
      | succ k ih =>
        intro i j
        set a : ℝ := a₀ + (i : ℝ) with ha
        set c : ℝ := c₀ + (k : ℝ) with hcdef
        have haP : PConstructible a := by
          rw [ha]
          have hiP : PConstructible (i : ℝ) := int_Pconstructible i
          pconstructible
        have hcP : PConstructible c := by
          rw [hcdef]
          have hkP : PConstructible (k : ℝ) := nat_Pconstructible k
          pconstructible
        have hkP : PConstructible (k : ℝ) := nat_Pconstructible k
        have hcne : ∀ m : ℕ, c ≠ -(m : ℝ) := by
          intro m hm
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          have hcpos : 0 < c := by rw [hcdef]; linarith [hc₀pos]
          linarith
        have hc1ne : ∀ m : ℕ, c + 1 ≠ -(m : ℝ) := by
          intro m hm
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          have hcpos : 0 < c := by rw [hcdef]; linarith [hc₀pos]
          linarith
        have hcane : c - a ≠ 0 := by
          have heq : c - a = (c₀ - a₀) + ((k - i : ℤ) : ℝ) := by
            rw [hcdef, ha]; push_cast; ring
          rw [heq]
          intro hcon
          apply hca_notInt (i - k)
          push_cast at hcon ⊢
          linarith
        -- The `c`-uple step for the non-degenerate `b`-index.
        have hshift : ∀ j : ℤ, j ≠ (k + 1 : ℤ) →
            PConstructible (hyp a (b₀ + (j : ℝ)) (c + 1) w) := by
          intro j hj
          have hjP : PConstructible (j : ℝ) := int_Pconstructible j
          have hbj : b₀ + (j : ℝ) ≠ 0 := hsum_ne_zero j
          have hcb : c - (b₀ + (j : ℝ)) ≠ 0 := by
            have heq : c - (b₀ + (j : ℝ)) = 1 + ((k - j : ℤ) : ℝ) := by
              rw [hcdef]; push_cast; ring
            rw [heq]
            intro hcon
            have h2 : ((k - j : ℤ) : ℝ) = -1 := by push_cast at hcon ⊢; linarith
            have h3 : (k : ℤ) - j = -1 := by exact_mod_cast h2
            exact hj (by omega)
          have hC := hyp_shift_c_up (a := a) (b := b₀ + (j : ℝ)) (c := c) (z := w)
            hcne hc1ne hcane hcb hwabs
          have hrecA := hyp_shift_a_down (a := a) (b := b₀ + (j : ℝ)) (c := c) (z := w)
            hbj hcane hcne hwabs
          have hD : deriv (fun u => hyp a (b₀ + (j : ℝ)) c u) w
              = ((c - a) * hyp (a - 1) (b₀ + (j : ℝ)) c w
                  + (a - c + (b₀ + (j : ℝ)) * w) * hyp a (b₀ + (j : ℝ)) c w)
                / (w * (1 - w)) := by
            rw [eq_div_iff (mul_ne_zero hwne0 (sub_ne_zero.mpr (Ne.symm hwne1)))]
            rw [eq_div_iff hcane] at hrecA
            linear_combination (-1) * hrecA
          rw [hD] at hC
          rw [hC]
          have h1P : PConstructible (hyp (a - 1) (b₀ + (j : ℝ)) c w) := by
            have harg : a - 1 = a₀ + ((i - 1 : ℤ) : ℝ) := by rw [ha]; push_cast; ring
            rw [harg, hcdef]
            exact ih (i - 1) j
          have h0P : PConstructible (hyp a (b₀ + (j : ℝ)) c w) := by
            rw [ha, hcdef]
            exact ih i j
          pconstructible
        have hgoal_eq : c₀ + ((k + 1 : ℕ) : ℝ) = c + 1 := by
          simp only [hcdef]; push_cast; ring
        rw [hgoal_eq]
        by_cases hj : j = (k + 1 : ℤ)
        · -- Degenerate `b`-index `b₀ + k + 1`, from the `b`-recurrence.
          subst hj
          rw [show b₀ + ((k + 1 : ℤ) : ℝ) = b₀ + (k : ℝ) + 1 by push_cast; ring]
          have hb1 : b₀ + (k : ℝ) + 1 ≠ 1 := by
            have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
            linarith [hb₀pos]
          have ha0 : a ≠ 0 := by
            rw [ha, ha₀E]
            intro hcon
            have h2 : ((2 * i - 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
            have h3 : (2 * i - 1 : ℤ) = 0 := by exact_mod_cast h2
            omega
          have hcb : (c + 1) - (b₀ + (k : ℝ) + 1) + 1 ≠ 0 := by
            have heq : (c + 1) - (b₀ + (k : ℝ) + 1) + 1 = 2 := by
              rw [hcdef, hc₀, hb₀]; ring
            rw [heq]; norm_num
          have hbk0 : b₀ + (k : ℝ) ≠ 0 := by
            have h := hsum_ne_zero (k : ℤ)
            rwa [show (((k : ℤ) : ℝ)) = (k : ℝ) by simp] at h
          have hden : (b₀ + (k : ℝ)) * (1 - w) ≠ 0 :=
            mul_ne_zero hbk0 (sub_ne_zero.mpr (Ne.symm hwne1))
          have hrec := hyp_three_term_b (a := a) (b := b₀ + (k : ℝ) + 1) (c := c + 1)
            (z := w) hb1 ha0 hcb hc1ne hwabs hwne1
          rw [show b₀ + (k : ℝ) + 1 - 1 = b₀ + (k : ℝ) by ring,
              show b₀ + (k : ℝ) + 1 - 2 = b₀ + (k : ℝ) - 1 by ring] at hrec
          have heq : hyp a (b₀ + (k : ℝ) + 1) (c + 1) w =
              (((c + 1) - (b₀ + (k : ℝ) + 1) + 1)
                  * hyp a (b₀ + (k : ℝ) - 1) (c + 1) w
                + (2 * (b₀ + (k : ℝ) + 1 - 1) - (c + 1)
                    + w * (a - (b₀ + (k : ℝ) + 1) + 1))
                  * hyp a (b₀ + (k : ℝ)) (c + 1) w)
                / ((b₀ + (k : ℝ)) * (1 - w)) := by
            rw [eq_div_iff hden]
            linear_combination hrec
          rw [heq]
          have h1P : PConstructible (hyp a (b₀ + (k : ℝ) - 1) (c + 1) w) := by
            have h := hshift (k - 1) (by omega)
            rwa [show b₀ + ((k - 1 : ℤ) : ℝ) = b₀ + (k : ℝ) - 1 by push_cast; ring] at h
          have h0P : PConstructible (hyp a (b₀ + (k : ℝ)) (c + 1) w) := by
            have h := hshift (k : ℤ) (by omega)
            rwa [show (((k : ℤ) : ℝ)) = (k : ℝ) by simp] at h
          pconstructible
        · exact hshift j hj
    simpa only [ha₀E, hb₀E, hc₀E, hwE] using hmain k i j

end

end Pconstructible
