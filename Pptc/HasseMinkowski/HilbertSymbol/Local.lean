/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.Basic
import Pptc.HasseMinkowski.Prod
import Pptc.HasseMinkowski.RankCriteria
import Pptc.HasseMinkowski.HilbertSymbol.Padic
import Pptc.HasseMinkowski.HilbertSymbol.Two

/-!
# Local Hilbert symbols at the completions of `ℚ`

This file collects the place-by-place facts about the Hilbert symbol `(·,·)_k` for
`k = ℚ_[p]` (and, later, `ℝ`).  The first item is the bilinearity of the symbol in its
first argument, `HasBilinHilbertSym ℚ_[p]`, which makes the generic rank criteria of
`RankCriteria.lean` available at every `p`-adic place.

The two-adic case is imported from `HilbertSymbol/Two.lean`; for odd `p` the result is
`hilbertSym_padic_odd_mul_left`.
-/

open Module QuadraticMap

namespace Pptc.HasseMinkowski

/-! ### Bilinearity of the `p`-adic Hilbert symbol -/

/-- The Hilbert symbol on the `p`-adic numbers is bilinear in its first argument.

For `p = 2` this is `instHasBilinHilbertSym` from `HilbertSymbol/Two.lean`; for odd `p` it
is `hilbertSym_padic_odd_mul_left`. -/
instance instHasBilinHilbertSymPadic (p : ℕ) [Fact p.Prime] : HasBilinHilbertSym ℚ_[p] := by
  by_cases hp : p = 2
  · subst hp
    infer_instance
  · exact ⟨fun {a a' b} => hilbertSym_padic_odd_mul_left hp a a' b⟩

/-! ### The rank-two representation criterion -/

section TwoRepresents

variable {k : Type*} [Field k]

/-- A nonzero vector of the plane `⟨a, b⟩` represents `x` exactly when the ternary form
`⟨a, b, -x⟩` is isotropic.

This is the bridge between representability by a rank-two form and the ternary isotropy
criterion of `RankCriteria.lean`.  The hard case is when the isotropic vector of `⟨a, b, -x⟩`
has last coordinate `0`: then `⟨a, b⟩` is itself isotropic, and since it is nondegenerate it
represents every value. -/
private lemma weightedSumSquares_two_represents_iff_ternary {a b x : k} [Invertible (2 : k)]
    (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) :
    (weightedSumSquares k ![a, b]).represents x ↔
      (weightedSumSquares k ![a, b, -x]).Isotropic := by
  have key2 : ∀ y : Fin 2 → k,
      (weightedSumSquares k ![a, b]) y = a * y 0 ^ 2 + b * y 1 ^ 2 := by
    intro y
    simp [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul, pow_two]
  have key3 : ∀ y : Fin 3 → k,
      (weightedSumSquares k ![a, b, -x]) y =
        a * y 0 ^ 2 + b * y 1 ^ 2 + (-x) * y 2 ^ 2 := by
    intro y
    simp [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul, pow_two]
  constructor
  · rintro ⟨y, _hy, hyQ⟩
    refine ⟨![y 0, y 1, 1], ?_, ?_⟩
    · intro h0
      have h1 : (1 : k) = 0 := by simpa using congr_fun h0 2
      exact one_ne_zero h1
    · rw [key3]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [key2] at hyQ
      linear_combination hyQ
  · rintro ⟨y, hy, hyQ⟩
    rw [key3] at hyQ
    by_cases hy2 : y 2 = 0
    · have hyQ' : a * y 0 ^ 2 + b * y 1 ^ 2 = 0 := by
        have h := hyQ
        rw [hy2] at h
        simpa using h
      have hneq : (![y 0, y 1] : Fin 2 → k) ≠ 0 := by
        intro h0
        apply hy
        funext j
        fin_cases j
        · simpa using congr_fun h0 0
        · simpa using congr_fun h0 1
        · exact hy2
      have hiso : (weightedSumSquares k ![a, b]).Isotropic := by
        refine ⟨![y 0, y 1], hneq, ?_⟩
        rw [key2]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact hyQ'
      have hnd : (weightedSumSquares k ![a, b]).Nondegenerate := by
        let w : Fin 2 → kˣ := ![Units.mk0 a ha, Units.mk0 b hb]
        have hw : (fun i => (w i : k)) = ![a, b] := by
          funext i
          fin_cases i <;> simp [w]
        rw [← hw]
        exact nondegenerate_weightedSumSquares w
      exact represents_of_isotropic_nondegenerate hnd hiso x
    · set z : Fin 2 → k := ![y 0 / y 2, y 1 / y 2] with hz_def
      have hzval : (weightedSumSquares k ![a, b]) z = x := by
        rw [key2]
        simp only [hz_def, Matrix.cons_val_zero, Matrix.cons_val_one]
        have hdiv : a * (y 0 / y 2) ^ 2 + b * (y 1 / y 2) ^ 2 =
            (a * y 0 ^ 2 + b * y 1 ^ 2) / y 2 ^ 2 := by
          field_simp [hy2]
        rw [hdiv]
        have hthis : a * y 0 ^ 2 + b * y 1 ^ 2 = x * y 2 ^ 2 := by
          linear_combination hyQ
        rw [hthis, mul_div_assoc, div_self (pow_ne_zero 2 hy2), mul_one]
      exact ⟨z, fun h0 => by
        rw [h0, map_zero] at hzval
        exact hx hzval.symm, hzval⟩

-- Theorem: the rank-two criterion for a diagonal form with two named weights.
-- `⟨a, b⟩` represents `x ≠ 0` exactly when `(x, -ab) = (a, b)`.
theorem represents_weightedSumSquares_two_iff {a b x : k} [HasBilinHilbertSym k]
    [Invertible (2 : k)] (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) :
    (weightedSumSquares k ![a, b]).represents x ↔
      hilbertSym x (-(a * b)) = hilbertSym a b := by
  rw [weightedSumSquares_two_represents_iff_ternary ha hb hx,
    weightedSumSquares_isotropic_iff_hilbertSym_eq_one a b (-x) ha hb (neg_ne_zero.mpr hx)]
  rw [show -(-x) * a = x * a by ring, show -(-x) * b = x * b by ring]
  rw [hilbertSym_mul_mul (a := a) (b := b) (c := x)]
  exact mul_eq_one_iff_eq_of_signs
    (hilbertSym_eq_one_or_neg_one_of_ne_zero hx (neg_ne_zero.mpr (mul_ne_zero ha hb)))
    (hilbertSym_eq_one_or_neg_one_of_ne_zero ha hb)

end TwoRepresents

end Pptc.HasseMinkowski
