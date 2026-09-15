/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.HilbertSymbol.Local
import Pptc.HasseMinkowski.Legendre
import Pptc.HasseMinkowski.Prod
import Pptc.HasseMinkowski.RankCriteria
import Pptc.HasseMinkowski.RatApproximation
import Pptc.HasseMinkowski.Padics.Squares
import Mathlib.Analysis.Real.Sqrt

/-!
# WP5 toolkit: diagonal Hasse–Minkowski for rank ≥ 5

This file collects the two "one-step" tools of the rank-`n ≥ 5` induction of Serre IV.2
(see `Plan-v3.md` §WP5).  The final rank ≥ 5 theorem is proved elsewhere; here we supply

* **WP5.1** — over an odd prime, a ternary diagonal form whose three weights are `p`-adic
  units is isotropic, and hence so is any diagonal form with at least three unit weights;
* **WP5.2** — the openness of the nonzero square classes of `ℝ` and `ℚ_[p]` (a number close
  enough to a nonzero `a₀` has `a / a₀` a square), and the vector form of weak approximation
  for `ℚ` (a rational vector can be found close to prescribed local vectors).

The rank-three criterion of `RankCriteria.lean` together with `hilbertSym_padicInt_units`
turns the local isotropy into the vanishing of a Hilbert symbol of two `p`-adic units.
-/

open Module QuadraticMap

namespace Pptc.HasseMinkowski

/-! ### WP5.1 — three unit weights over an odd prime -/

-- Theorem: over an odd prime, a ternary diagonal form all of whose weights are `p`-adic units
-- is isotropic.
--
-- The rank-three criterion `weightedSumSquares_isotropic_iff_hilbertSym_eq_one` reduces this
-- to `(-u₂u₀, -u₂u₁) = 1`; both arguments are units of `ℤ_[p]`, so `hilbertSym_padicInt_units`
-- gives the result.
theorem isotropic_weightedSumSquares_three_units (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (u : Fin 3 → ℤ_[p]ˣ) :
    (weightedSumSquares ℚ_[p] (fun i => (u i : ℚ_[p]))).Isotropic := by
  have hfun : (fun i : Fin 3 => (u i : ℚ_[p])) =
      ![(u 0 : ℚ_[p]), (u 1 : ℚ_[p]), (u 2 : ℚ_[p])] := by
    funext i
    fin_cases i <;> rfl
  have hne : ∀ i : Fin 3, ((u i : ℤ_[p]) : ℚ_[p]) ≠ 0 := fun i => by
    rw [PadicInt.coe_ne_zero]
    exact (u i).ne_zero
  rw [hfun, weightedSumSquares_isotropic_iff_hilbertSym_eq_one _ _ _
    (hne 0) (hne 1) (hne 2)]
  have h0 : (-(u 2 : ℚ_[p])) * (u 0 : ℚ_[p]) = ((-(u 2 * u 0) : ℤ_[p]ˣ) : ℚ_[p]) := by
    rw [Units.val_neg, Units.val_mul]
    push_cast
    ring
  have h1 : (-(u 2 : ℚ_[p])) * (u 1 : ℚ_[p]) = ((-(u 2 * u 1) : ℤ_[p]ˣ) : ℚ_[p]) := by
    rw [Units.val_neg, Units.val_mul]
    push_cast
    ring
  rw [h0, h1]
  exact hilbertSym_padicInt_units hp (-(u 2 * u 0)) (-(u 2 * u 1))

-- Theorem: over an odd prime, a diagonal form with at least three `p`-adic unit weights is
-- isotropic.
--
-- The three unit coordinates span a ternary subform which is isotropic by
-- `isotropic_weightedSumSquares_three_units`; extending its isotropic vector by `0` to `ι`
-- preserves the value of the whole form, because the added coordinates have weight `0`.
theorem isotropic_of_three_units (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {ι : Type*}
    [Fintype ι] {w : ι → ℚ_[p]} (u : Fin 3 ↪ ι)
    (hu : ∀ j, ∃ v : ℤ_[p]ˣ, (v : ℚ_[p]) = w (u j)) :
    (weightedSumSquares ℚ_[p] w).Isotropic := by
  classical
  choose v hv using hu
  have hsub : (weightedSumSquares ℚ_[p] (fun j : Fin 3 => w (u j))).Isotropic := by
    have hw_eq : (fun j : Fin 3 => (v j : ℚ_[p])) = fun j : Fin 3 => w (u j) :=
      funext fun j => hv j
    rw [← hw_eq]
    exact isotropic_weightedSumSquares_three_units p hp v
  obtain ⟨y, hy_ne, hy0⟩ := hsub
  let V : ι → ℚ_[p] := fun i =>
    if hi : i ∈ Set.range (fun j : Fin 3 => u j) then y (Classical.choose hi) else 0
  have hVf : ∀ j, V (u j) = y j := by
    intro j
    have hi : u j ∈ Set.range (fun j : Fin 3 => u j) := ⟨j, rfl⟩
    have hc : Classical.choose hi = j := u.injective (Classical.choose_spec hi)
    dsimp only [V]
    rw [dif_pos hi, hc]
  have hV0 : ∀ i, i ∉ Set.range (fun j : Fin 3 => u j) → V i = 0 := by
    intro i hi
    dsimp only [V]
    rw [dif_neg hi]
  refine ⟨V, ?_, ?_⟩
  · intro hVz
    have hex : ∃ j, y j ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hy_ne (funext hcon)
    obtain ⟨j, hj⟩ := hex
    exact hj (by rw [← hVf j, hVz]; rfl)
  · have hL : (weightedSumSquares ℚ_[p] w) V = ∑ i : ι, w i * (V i * V i) := by
      simp only [weightedSumSquares_apply, smul_eq_mul]
    have hR : (weightedSumSquares ℚ_[p] (fun j : Fin 3 => w (u j))) y =
        ∑ j : Fin 3, w (u j) * (y j * y j) := by
      simp only [weightedSumSquares_apply, smul_eq_mul]
    have hsum : (∑ i : ι, w i * (V i * V i)) = ∑ j : Fin 3, w (u j) * (y j * y j) := by
      have hzero : ∀ i ∈ (Finset.univ : Finset ι),
          i ∉ Finset.univ.image (fun j : Fin 3 => u j) → w i * (V i * V i) = 0 := by
        intro i _ hi
        have hir : i ∉ Set.range (fun j : Fin 3 => u j) := by
          intro hmem
          obtain ⟨a, ha⟩ := hmem
          exact hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
        rw [hV0 i hir]; ring
      rw [← Finset.sum_subset
        (Finset.subset_univ (Finset.univ.image (fun j : Fin 3 => u j))) hzero]
      rw [Finset.sum_image (fun a _ b _ hab => u.injective hab)]
      exact Finset.sum_congr rfl (fun j _ => by simp only [hVf j])
    rw [hL, hsum, ← hR]
    exact hy0

-- Theorem: the integral-weight form of `isotropic_of_three_units`, stated with the literal
-- hypothesis that the three chosen weights are units of `ℤ_[p]`.
theorem isotropic_of_three_units_int (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {ι : Type*}
    [Fintype ι] {w : ι → ℤ_[p]} (u : Fin 3 ↪ ι) (hu : ∀ j, IsUnit (w (u j))) :
    (weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p]))).Isotropic := by
  refine isotropic_of_three_units p hp u (fun j => ?_)
  exact ⟨(hu j).unit, by rw [IsUnit.unit_spec]⟩

/-! ### WP5.2 — openness of square classes and vector approximation -/

-- Theorem (openness of the nonzero square class of `ℝ`): a real number within distance
-- `‖a₀‖` of a nonzero `a₀` has `a / a₀` positive, hence a square.
theorem isSquare_div_of_close_real {a₀ a : ℝ} (h₀ : a₀ ≠ 0) (h : ‖a - a₀‖ < ‖a₀‖) :
    IsSquare (a / a₀) := by
  have h' : |a - a₀| < |a₀| := by simpa only [Real.norm_eq_abs] using h
  rw [Real.isSquare_iff]
  by_cases hpos : 0 < a₀
  · rw [abs_of_pos hpos] at h'
    have ha : 0 < a := by linarith [(abs_lt.mp h').1]
    exact le_of_lt (div_pos ha hpos)
  · have hneg : a₀ < 0 := lt_of_le_of_ne (not_lt.mp hpos) h₀
    rw [abs_of_neg hneg] at h'
    have ha : a < 0 := by linarith [(abs_lt.mp h').2]
    exact le_of_lt (div_pos_of_neg_of_neg ha hneg)

-- Theorem (openness of the nonzero square class of `ℚ_[p]`, odd `p`): a `p`-adic number
-- within distance `‖a₀‖` of a nonzero `a₀` has `a / a₀` a square.
--
-- Writing `a / a₀ = 1 + (a - a₀) / a₀`, the closeness hypothesis gives
-- `dist (a / a₀) 1 ≤ ‖a - a₀‖ / ‖a₀‖ < 1`, and `Padic.isSquare_of_dist_one_lt_one` applies.
theorem isSquare_div_of_close_padic (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {a₀ a : ℚ_[p]}
    (h₀ : a₀ ≠ 0) (h : ‖a - a₀‖ < ‖a₀‖) : IsSquare (a / a₀) := by
  refine Padic.isSquare_of_dist_one_lt_one (p := p) hp ?_
  rw [dist_eq_norm, show a / a₀ - 1 = (a - a₀) / a₀ by field_simp, norm_div,
    div_lt_one (norm_pos_iff.mpr h₀)]
  exact h

-- Theorem (openness of the nonzero square class of `ℚ_[2]`): the same conclusion holds for
-- `p = 2`, but the closeness must be measured against the modulus-`8` threshold `2⁻²`.
--
-- Indeed `a / a₀` is a `2`-adic square as soon as `dist (a / a₀) 1 < 2⁻²`.
theorem isSquare_div_of_close_padic_two {a₀ a : ℚ_[2]} (h₀ : a₀ ≠ 0)
    (h : ‖a - a₀‖ < 2 ^ (-(2 : ℤ)) * ‖a₀‖) : IsSquare (a / a₀) := by
  refine Padic.isSquare_of_dist_one_lt_pow ?_
  rw [dist_eq_norm, show a / a₀ - 1 = (a - a₀) / a₀ by field_simp, norm_div,
    div_lt_iff₀ (norm_pos_iff.mpr h₀)]
  exact h

-- Theorem: a prime bundled as `Nat.Primes` is prime, as an instance (needed to form `ℚ_[p]`
-- for `p` ranging over a finite set of primes).
local instance factPrimeOfPrimesHighRank (p : Nat.Primes) : Fact (Nat.Prime (p : ℕ)) :=
  ⟨p.2⟩

-- Theorem (vector weak approximation for `ℚ`): given local vectors `x p ∈ ℚ_p²` at the
-- finitely many places `p ∈ S`, there is a rational vector `q ∈ ℚ²` whose coordinates are
-- within `1` of `x p` at every place `p ∈ S`.
--
-- The two coordinates are approximated independently by `Rat.approximation'`; the real
-- coordinate of the approximation theorem is irrelevant here and is taken to be `0`.
theorem exists_rat_close_vec {S : Finset Nat.Primes}
    (x : Π p : S, Fin 2 → ℚ_[p]) :
    ∃ q : Fin 2 → ℚ, ∀ p : S,
      ‖(x p) 0 - (q 0 : ℚ_[p])‖ < 1 ∧ ‖(x p) 1 - (q 1 : ℚ_[p])‖ < 1 := by
  classical
  obtain ⟨q₀, hq₀⟩ := Rat.approximation' (S := S) (ε := 1) (by norm_num)
    (0, fun p : S => (x p) 0)
  obtain ⟨q₁, hq₁⟩ := Rat.approximation' (S := S) (ε := 1) (by norm_num)
    (0, fun p : S => (x p) 1)
  refine ⟨![q₀, q₁], fun p => ⟨?_, ?_⟩⟩
  · simp only [Matrix.cons_val_zero]
    have hsingle : ‖(x p) 0 - (q₀ : ℚ_[p])‖ ≤
        Finset.sum (Finset.attach S) (fun n => ‖(x n) 0 - (q₀ : ℚ_[n])‖) :=
      Finset.single_le_sum (f := fun n : S => ‖(x n) 0 - (q₀ : ℚ_[n])‖)
        (fun i _ => norm_nonneg _) (Finset.mem_attach S p)
    have hle : Finset.sum (Finset.attach S) (fun n => ‖(x n) 0 - (q₀ : ℚ_[n])‖) ≤
        ‖(0 : ℝ) - q₀‖ +
          Finset.sum (Finset.attach S) (fun n => ‖(x n) 0 - (q₀ : ℚ_[n])‖) :=
      le_add_of_nonneg_left (norm_nonneg _)
    exact lt_of_le_of_lt hsingle (lt_of_le_of_lt hle hq₀)
  · simp only [Matrix.cons_val_one]
    have hsingle : ‖(x p) 1 - (q₁ : ℚ_[p])‖ ≤
        Finset.sum (Finset.attach S) (fun n => ‖(x n) 1 - (q₁ : ℚ_[n])‖) :=
      Finset.single_le_sum (f := fun n : S => ‖(x n) 1 - (q₁ : ℚ_[n])‖)
        (fun i _ => norm_nonneg _) (Finset.mem_attach S p)
    have hle : Finset.sum (Finset.attach S) (fun n => ‖(x n) 1 - (q₁ : ℚ_[n])‖) ≤
        ‖(0 : ℝ) - q₁‖ +
          Finset.sum (Finset.attach S) (fun n => ‖(x n) 1 - (q₁ : ℚ_[n])‖) :=
      le_add_of_nonneg_left (norm_nonneg _)
    exact lt_of_le_of_lt hsingle (lt_of_le_of_lt hle hq₁)

/-! ### The rank-four input of the high-rank induction

The rank-`n ≥ 5` induction of Serre IV.2 bottoms out at rank 4, so `HighRank.lean` is stated
relative to the following `Prop`, which is exactly the diagonal rank-four Hasse–Minkowski
theorem that `RankFour.lean` (WP4.2) proves.  Keeping it as an explicit hypothesis lets the
high-rank induction be developed and checked independently of the rank-four proof. -/

/-- Diagonal rank-four Hasse–Minkowski over `ℚ`: a diagonal rank-four form with nonzero
rational weights that is isotropic over every `p`-adic completion and over `ℝ` is isotropic
over `ℚ`.  This is the WP4.2 statement, recorded as a `Prop` so that the rank-`≥ 5`
induction can be stated against it. -/
def RankFourDiagonalHM : Prop :=
  ∀ w : Fin 4 → ℚ, (∀ i, w i ≠ 0) →
    (∀ (p : ℕ) [Fact (Nat.Prime p)],
      (weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p]))).Isotropic) →
    (weightedSumSquares ℝ (fun i => (w i : ℝ))).Isotropic →
    (weightedSumSquares ℚ w).Isotropic

end Pptc.HasseMinkowski
