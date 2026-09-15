/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Scaling rational ternary solutions into `ℤ_[p]`

Port of the analytic core of WiN7 `Padics/Lemmas.lean`.  Given a nontrivial rational solution of
`z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0`, multiplying all three coordinates by the inverse of a
coordinate of maximal `p`-adic norm produces an integral solution with at least one unit
coordinate.

`exists_nontrivial_zero` is stated here in its *corrected* form: the upstream statement (without
the hypothesis that `v` is a unit) is false, e.g. `p = 2`, `v = 2`, `z = 2`, `x = y = 1`.  With
`‖v‖ = 1` it is true and, in fact, both `z` and `y` become units.
-/

open Padic

namespace Padic

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ### Norms of rescaled coordinates -/

-- Theorem: multiplying a coordinate of norm at most `‖w‖` by `p ^ (-(w.valuation))` keeps it in
-- the unit ball.
private lemma norm_mul_pow_neg_valuation_le_one {u w : ℚ_[p]} (hw : w ≠ 0) (hu : ‖u‖ ≤ ‖w‖) :
    ‖u * p ^ (-(w.valuation))‖ ≤ 1 := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  have hw_norm : ‖w‖ = (p : ℝ) ^ (-(w.valuation)) := Padic.norm_eq_zpow_neg_valuation hw
  rw [norm_mul, Padic.norm_p_zpow, neg_neg]
  calc
    ‖u‖ * (p : ℝ) ^ w.valuation
        ≤ (p : ℝ) ^ (-(w.valuation)) * (p : ℝ) ^ w.valuation :=
          mul_le_mul_of_nonneg_right (by rw [← hw_norm]; exact hu)
            (zpow_nonneg (Nat.cast_nonneg p) _)
    _ = 1 := by rw [← zpow_add₀ hp0, neg_add_cancel, zpow_zero]

-- Theorem: multiplying `w` itself by `p ^ (-(w.valuation))` gives a vector of norm `1`.
private lemma norm_mul_pow_neg_valuation_eq_one {w : ℚ_[p]} (hw : w ≠ 0) :
    ‖w * p ^ (-(w.valuation))‖ = 1 := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  rw [norm_mul, Padic.norm_p_zpow, neg_neg, Padic.norm_eq_zpow_neg_valuation hw,
    ← zpow_add₀ hp0, neg_add_cancel, zpow_zero]

/-! ### Rescaling a rational solution -/

-- Theorem: rescaling all three coordinates of a rational solution by a common factor preserves
-- the solution; this packages the resulting `ℤ_[p]` triple and its equation.
private lemma scaled_solution {v : ℚ_[p]ˣ} {x y z c : ℚ_[p]}
    (hsol : z ^ 2 - p * x ^ 2 - (v : ℚ_[p]) * y ^ 2 = 0)
    (hx : ‖x * c‖ ≤ 1) (hy : ‖y * c‖ ≤ 1) (hz : ‖z * c‖ ≤ 1) :
    let X : ℤ_[p] := ⟨x * c, hx⟩
    let Y : ℤ_[p] := ⟨y * c, hy⟩
    let Z : ℤ_[p] := ⟨z * c, hz⟩
    (Z : ℚ_[p]) ^ 2 - p * (X : ℚ_[p]) ^ 2 - (v : ℚ_[p]) * (Y : ℚ_[p]) ^ 2 = 0 := by
  dsimp only
  have hpow : (z * c) ^ 2 - p * (x * c) ^ 2 - (v : ℚ_[p]) * (y * c) ^ 2
      = c ^ 2 * (z ^ 2 - p * x ^ 2 - (v : ℚ_[p]) * y ^ 2) := by ring
  rw [hpow, hsol, mul_zero]

/-- Given a nontrivial rational solution of `z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0`, multiplying the
three coordinates by `p ^ (-n)`, where `n` is the valuation of a coordinate of maximal norm,
produces a solution in `ℤ_[p]` at least one of whose coordinates is a unit. -/
-- Theorem: a nontrivial rational solution of `z² - p x² - v y² = 0` yields an integral solution
-- with at least one unit coordinate.
lemma exists_padicInt_solution {v : ℚ_[p]ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - (v : ℚ_[p]) * y ^ 2 = 0) :
    ∃ z' y' x' : ℤ_[p],
      (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - (v : ℚ_[p]) * (y' : ℚ_[p]) ^ 2 = 0
      ∧ (IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
  set m : ℝ := max ‖x‖ (max ‖y‖ ‖z‖) with hm
  have hm_ne_zero : m ≠ 0 := by
    intro h
    have hx0 : x = 0 := by
      refine norm_eq_zero.mp ?_
      exact le_antisymm (le_trans (le_max_left _ _) (le_of_eq h)) (norm_nonneg _)
    have hy0 : y = 0 := by
      refine norm_eq_zero.mp ?_
      exact le_antisymm
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_eq h)) (norm_nonneg _)
    have hz0 : z = 0 := by
      refine norm_eq_zero.mp ?_
      exact le_antisymm
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_eq h)) (norm_nonneg _)
    exact hnontriv (by simp [hx0, hy0, hz0])
  have hm_pos : 0 < m := lt_of_le_of_ne (le_trans (norm_nonneg x) (le_max_left _ _))
    (Ne.symm hm_ne_zero)
  have hcoord : ‖x‖ = m ∨ ‖y‖ = m ∨ ‖z‖ = m := by
    simp only [hm]
    rcases le_total (max ‖y‖ ‖z‖) ‖x‖ with h | h
    · exact Or.inl (Eq.symm (max_eq_left h))
    · rcases le_total ‖y‖ ‖z‖ with hyz | hzy
      · exact Or.inr (Or.inr (Eq.symm (by rw [max_eq_right h, max_eq_right hyz])))
      · exact Or.inr (Or.inl (Eq.symm (by rw [max_eq_right h, max_eq_left hzy])))
  have hxle : ‖x‖ ≤ m := le_max_left _ _
  have hyle : ‖y‖ ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hzle : ‖z‖ ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  rcases hcoord with hxmax | hymax | hzmax
  · have hx0 : x ≠ 0 := norm_pos_iff.mp (hxmax ▸ hm_pos)
    have heq : ‖x * p ^ (-(x.valuation))‖ = 1 := norm_mul_pow_neg_valuation_eq_one hx0
    have hy' : ‖y * p ^ (-(x.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one hx0 (hxmax ▸ hyle)
    have hz' : ‖z * p ^ (-(x.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one hx0 (hxmax ▸ hzle)
    exact ⟨⟨z * p ^ (-(x.valuation)), hz'⟩, ⟨y * p ^ (-(x.valuation)), hy'⟩,
      ⟨x * p ^ (-(x.valuation)), heq.le⟩, scaled_solution hsol heq.le hy' hz',
      Or.inr (Or.inr (PadicInt.isUnit_iff.mpr heq))⟩
  · have hy0 : y ≠ 0 := norm_pos_iff.mp (hymax ▸ hm_pos)
    have heq : ‖y * p ^ (-(y.valuation))‖ = 1 := norm_mul_pow_neg_valuation_eq_one hy0
    have hx' : ‖x * p ^ (-(y.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one hy0 (hymax ▸ hxle)
    have hz' : ‖z * p ^ (-(y.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one hy0 (hymax ▸ hzle)
    exact ⟨⟨z * p ^ (-(y.valuation)), hz'⟩, ⟨y * p ^ (-(y.valuation)), heq.le⟩,
      ⟨x * p ^ (-(y.valuation)), hx'⟩, scaled_solution hsol hx' heq.le hz',
      Or.inr (Or.inl (PadicInt.isUnit_iff.mpr heq))⟩
  · have hz0 : z ≠ 0 := norm_pos_iff.mp (hzmax ▸ hm_pos)
    have heq : ‖z * p ^ (-(z.valuation))‖ = 1 := norm_mul_pow_neg_valuation_eq_one hz0
    have hx' : ‖x * p ^ (-(z.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one hz0 (hzmax ▸ hxle)
    have hy' : ‖y * p ^ (-(z.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one hz0 (hzmax ▸ hyle)
    exact ⟨⟨z * p ^ (-(z.valuation)), heq.le⟩, ⟨y * p ^ (-(z.valuation)), hy'⟩,
      ⟨x * p ^ (-(z.valuation)), hx'⟩, scaled_solution hsol hx' hy' heq.le,
      Or.inl (PadicInt.isUnit_iff.mpr heq)⟩

/-- Alias of `exists_padicInt_solution` under the name used upstream. -/
-- Theorem: same statement as `exists_padicInt_solution`.
lemma lift_solutions_to_int_first {v : ℚ_[p]ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - (v : ℚ_[p]) * y ^ 2 = 0) :
    ∃ z' y' x' : ℤ_[p],
      (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - (v : ℚ_[p]) * (y' : ℚ_[p]) ^ 2 = 0
      ∧ (IsUnit z' ∨ IsUnit y' ∨ IsUnit x') :=
  exists_padicInt_solution hnontriv hsol

/-! ### Norm bounds for `ℤ_[p]` elements -/

-- Theorem: a nonunit `p`-adic integer has norm at most `p ^ (-1)`.
private lemma norm_coe_le_pow_neg_one_of_not_isUnit {Y : ℤ_[p]} (hY : ¬ IsUnit Y) :
    ‖(Y : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
  rw [← PadicInt.norm_def]
  have hlt : ‖Y‖ < 1 := PadicInt.not_isUnit_iff.mp hY
  have hdvd : (p : ℤ_[p]) ∣ Y := (PadicInt.norm_lt_one_iff_dvd Y).mp hlt
  have hmem : Y ∈ Ideal.span {((p : ℤ_[p])) ^ 1} := by
    rw [pow_one]; exact Ideal.mem_span_singleton.mpr hdvd
  simpa using (PadicInt.norm_le_pow_iff_mem_span_pow Y 1).mpr hmem

-- Theorem: a unit `p`-adic integer has norm `1` after coercion into `ℚ_[p]`.
private lemma norm_coe_eq_one_of_isUnit {Z : ℤ_[p]} (hZ : IsUnit Z) :
    ‖(Z : ℚ_[p])‖ = 1 := by
  rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp hZ

-- Theorem: a `p`-adic integer has norm at most `1` after coercion into `ℚ_[p]`.
private lemma norm_coe_le_one (X : ℤ_[p]) : ‖(X : ℚ_[p])‖ ≤ 1 := by
  rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one X

-- Theorem: the square of a nonunit `p`-adic integer has norm at most `p ^ (-2)`.
private lemma norm_sq_coe_le_pow_neg_two_of_not_isUnit {Y : ℤ_[p]} (hY : ¬ IsUnit Y) :
    ‖(Y : ℚ_[p]) ^ 2‖ ≤ (p : ℝ) ^ (-(2 : ℤ)) := by
  have h := norm_coe_le_pow_neg_one_of_not_isUnit hY
  rw [norm_pow, pow_two]
  calc
    ‖(Y : ℚ_[p])‖ * ‖(Y : ℚ_[p])‖
        ≤ (p : ℝ) ^ (-(1 : ℤ)) * (p : ℝ) ^ (-(1 : ℤ)) :=
          mul_le_mul h h (norm_nonneg _) (zpow_nonneg (Nat.cast_nonneg p) _)
    _ = (p : ℝ) ^ (-(2 : ℤ)) := by
        rw [← zpow_add₀ (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))]
        norm_num

-- Theorem: `p ^ n < 1` for every negative integer `n` and prime `p`.
private lemma p_zpow_neg_lt_one {n : ℤ} (hn : n < 0) : (p : ℝ) ^ n < 1 := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast (Nat.Prime.one_lt Fact.out)
  rw [← zpow_zero (p : ℝ)]
  exact (zpow_lt_zpow_iff_right₀ h1).mpr hn

-- Theorem: `p ^ (-2) < p ^ (-1)` for prime `p`.
private lemma p_zpow_neg_two_lt_neg_one : (p : ℝ) ^ (-(2 : ℤ)) < (p : ℝ) ^ (-(1 : ℤ)) := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast (Nat.Prime.one_lt Fact.out)
  exact (zpow_lt_zpow_iff_right₀ h1).mpr (by norm_num)

/-- Corrected form of the upstream `exists_nontrivial_zero`: assuming the coefficient `v` is a
`p`-adic unit, a nontrivial rational solution of `z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0` rescales to
an integral solution whose `z` and `y` coordinates are units.  (Upstream omits the hypothesis
`‖v‖ = 1`; the statement is then false, e.g. `p = 2`, `v = 2`, `z = 2`, `x = y = 1`.) -/
-- Theorem: with `v` a unit, a nontrivial rational solution rescales to an integral solution with
-- both the `z`- and `y`-coordinates units.
lemma exists_nontrivial_zero {v : ℚ_[p]ˣ} {x y z : ℚ_[p]}
    (hv : ‖(v : ℚ_[p])‖ = 1)
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - (v : ℚ_[p]) * y ^ 2 = 0) :
    ∃ z' y' : ℤ_[p]ˣ, ∃ x' : ℤ_[p],
      (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - (v : ℚ_[p]) * (y' : ℚ_[p]) ^ 2 = 0 := by
  obtain ⟨Z, Y, X, heq, hu⟩ := exists_padicInt_solution hnontriv hsol
  have heq_add : ((Z : ℚ_[p])) ^ 2 = p * ((X : ℚ_[p])) ^ 2 + (v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2 := by
    linear_combination heq
  have hX2 : ‖((X : ℚ_[p])) ^ 2‖ ≤ 1 := by
    rw [norm_pow, pow_two]
    simpa using mul_le_mul (norm_coe_le_one X) (norm_coe_le_one X)
      (norm_nonneg _) (by norm_num)
  have hB_le : ‖p * ((X : ℚ_[p])) ^ 2‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
    rw [norm_mul, Padic.norm_p]
    calc
      (p : ℝ)⁻¹ * ‖((X : ℚ_[p])) ^ 2‖ ≤ (p : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hX2 (inv_nonneg.mpr (Nat.cast_nonneg p))
      _ = (p : ℝ) ^ (-(1 : ℤ)) := by rw [mul_one, zpow_neg_one]
  have hy_of_hz : IsUnit Z → IsUnit Y := by
    intro hZ
    by_contra hY
    have hZ2 : ‖((Z : ℚ_[p])) ^ 2‖ = 1 := by
      rw [norm_pow, norm_coe_eq_one_of_isUnit hZ]; norm_num
    have hCle : ‖(v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2‖ ≤ (p : ℝ) ^ (-(2 : ℤ)) := by
      rw [norm_mul, hv, one_mul]
      exact norm_sq_coe_le_pow_neg_two_of_not_isUnit hY
    have hC : ‖(v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2‖ < 1 :=
      lt_of_le_of_lt hCle (p_zpow_neg_lt_one (by norm_num))
    have htri : ‖((Z : ℚ_[p])) ^ 2‖ ≤
        max ‖p * ((X : ℚ_[p])) ^ 2‖ ‖(v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2‖ := by
      rw [heq_add]
      exact Padic.nonarchimedean _ _
    have hmax : 1 ≤ max ‖p * ((X : ℚ_[p])) ^ 2‖ ‖(v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2‖ :=
      calc (1 : ℝ) = ‖((Z : ℚ_[p])) ^ 2‖ := hZ2.symm
        _ ≤ max ‖p * ((X : ℚ_[p])) ^ 2‖ ‖(v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2‖ := htri
    have hB : 1 ≤ ‖p * ((X : ℚ_[p])) ^ 2‖ := by
      by_contra hlt
      push Not at hlt
      linarith [hmax, max_lt hlt hC]
    have hneg : (p : ℝ) ^ (-(1 : ℤ)) < 1 :=
      p_zpow_neg_lt_one (n := -(1 : ℤ)) (by norm_num)
    linarith [hB, hB_le, hneg]
  have hz_of_hy : IsUnit Y → IsUnit Z := by
    intro hY
    by_contra hZ
    have hC2 : ‖(v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2‖ = 1 := by
      rw [norm_mul, hv, one_mul, norm_pow, norm_coe_eq_one_of_isUnit hY]; norm_num
    have hZ2 : ‖((Z : ℚ_[p])) ^ 2‖ ≤ (p : ℝ) ^ (-(2 : ℤ)) :=
      norm_sq_coe_le_pow_neg_two_of_not_isUnit hZ
    have heq_sub : (v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2
        = ((Z : ℚ_[p])) ^ 2 - p * ((X : ℚ_[p])) ^ 2 := by
      linear_combination -heq
    have htri : ‖(v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2‖ ≤
        max ‖((Z : ℚ_[p])) ^ 2‖ ‖p * ((X : ℚ_[p])) ^ 2‖ := by
      calc
        ‖(v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2‖
            = ‖((Z : ℚ_[p])) ^ 2 - p * ((X : ℚ_[p])) ^ 2‖ := by rw [heq_sub]
        _ = ‖((Z : ℚ_[p])) ^ 2 + -(p * ((X : ℚ_[p])) ^ 2)‖ := by rw [sub_eq_add_neg]
        _ ≤ max ‖((Z : ℚ_[p])) ^ 2‖ ‖-(p * ((X : ℚ_[p])) ^ 2)‖ :=
              Padic.nonarchimedean _ _
        _ = max ‖((Z : ℚ_[p])) ^ 2‖ ‖p * ((X : ℚ_[p])) ^ 2‖ := by rw [norm_neg]
    have hmax1 : (1 : ℝ) ≤ max ‖((Z : ℚ_[p])) ^ 2‖ ‖p * ((X : ℚ_[p])) ^ 2‖ :=
      hC2.ge.trans htri
    have hmaxlt : max ‖((Z : ℚ_[p])) ^ 2‖ ‖p * ((X : ℚ_[p])) ^ 2‖ < 1 :=
      max_lt (lt_of_le_of_lt hZ2
        (p_zpow_neg_two_lt_neg_one.trans (p_zpow_neg_lt_one (by norm_num))))
        (lt_of_le_of_lt hB_le (p_zpow_neg_lt_one (by norm_num)))
    linarith
  have hZY : IsUnit Z ∧ IsUnit Y := by
    rcases hu with hZ | hY | hX
    · exact ⟨hZ, hy_of_hz hZ⟩
    · exact ⟨hz_of_hy hY, hY⟩
    · have hZY : IsUnit Z ∨ IsUnit Y := by
        by_contra h
        push Not at h
        obtain ⟨hZn, hYn⟩ := h
        have hZ2 : ‖((Z : ℚ_[p])) ^ 2‖ ≤ (p : ℝ) ^ (-(2 : ℤ)) :=
          norm_sq_coe_le_pow_neg_two_of_not_isUnit hZn
        have hC2 : ‖(v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2‖ ≤ (p : ℝ) ^ (-(2 : ℤ)) := by
          rw [norm_mul, hv, one_mul]
          exact norm_sq_coe_le_pow_neg_two_of_not_isUnit hYn
        have heq_sub : p * ((X : ℚ_[p])) ^ 2
            = ((Z : ℚ_[p])) ^ 2 - (v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2 := by
          linear_combination -heq
        have hB_le' : ‖p * ((X : ℚ_[p])) ^ 2‖ ≤ (p : ℝ) ^ (-(2 : ℤ)) := by
          rw [heq_sub, sub_eq_add_neg]
          calc
            ‖((Z : ℚ_[p])) ^ 2 + -((v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2)‖
                ≤ max ‖((Z : ℚ_[p])) ^ 2‖ ‖-((v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2)‖ :=
                  Padic.nonarchimedean _ _
            _ = max ‖((Z : ℚ_[p])) ^ 2‖ ‖(v : ℚ_[p]) * ((Y : ℚ_[p])) ^ 2‖ := by rw [norm_neg]
            _ ≤ (p : ℝ) ^ (-(2 : ℤ)) := max_le hZ2 hC2
        have hB_eq : ‖p * ((X : ℚ_[p])) ^ 2‖ = (p : ℝ) ^ (-(1 : ℤ)) := by
          rw [norm_mul, Padic.norm_p, norm_pow, norm_coe_eq_one_of_isUnit hX, one_pow, mul_one,
            zpow_neg_one]
        have hlt : (p : ℝ) ^ (-(2 : ℤ)) < (p : ℝ) ^ (-(1 : ℤ)) := p_zpow_neg_two_lt_neg_one
        have hbad : (p : ℝ) ^ (-(1 : ℤ)) ≤ (p : ℝ) ^ (-(2 : ℤ)) := hB_eq.ge.trans hB_le'
        linarith
      rcases hZY with hZ | hY
      · exact ⟨hZ, hy_of_hz hZ⟩
      · exact ⟨hz_of_hy hY, hY⟩
  obtain ⟨hZ, hY⟩ := hZY
  refine ⟨hZ.unit, hY.unit, X, ?_⟩
  simpa only [IsUnit.unit_spec] using heq

end Padic
