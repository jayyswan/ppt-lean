/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.HasseInvariantWellDef
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Rank criteria for the Hasse–Minkowski invariant, general (non-diagonal) forms

`Pptc/HasseMinkowski/RankCriteria.lean` proves the rank criteria for a *diagonal* form
`⟨w₀, w₁⟩` / `⟨w₀, w₁, w₂⟩`.  This file lifts them to an arbitrary nondegenerate quadratic form
over a field `k`, stated in terms of a chosen `k`-basis `b`:

* `represents_iff_of_rank_two`: a nondegenerate rank-two form `Q` represents `a : kˣ` exactly
  when `(a, -discr Q) = ε(Q)`;
* `represents_zero_iff_of_rank_three`: a nondegenerate rank-three form `Q` is isotropic exactly
  when `(-1, -discr Q) = ε(Q)`.

The proofs are a diagonal reduction: `Q` is isometric to a weighted sum of squares
`⟨w⟩` with unit weights (`QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'`),
the diagonal criteria apply to `⟨w⟩`, and the discriminant of `Q` in the basis `b` differs from
the product `∏ wᵢ` by a square, which the Hilbert symbol cannot see.

## Hypotheses

Everything is over a field `k` with `[Invertible (2 : k)]` and a bilinear Hilbert symbol
`[HasBilinHilbertSym k]`.  In addition the statements mention `hasseMinkowskiInv Q hQ`, whose
value depends on the diagonalization chosen by `Classical.choose`.  To identify it with the
invariant computed from the exhibited weights we use the well-definedness hypothesis `hconn`
of `HasseInvariantWellDef.lean` (WiN7's connectivity of diagonalizations, `Chain.lean`); it is
carried as an explicit argument, exactly as in that file.
-/

open Module QuadraticMap

namespace Pptc.HasseMinkowski

variable {k : Type*} [Field k]

/-! ### The diagonal rank-two criterion -/

section DiagonalTwo

variable [Invertible (2 : k)] [HasBilinHilbertSym k]

-- Theorem: `⟨w₀, w₁⟩` represents `a` exactly when the ternary form `⟨w₀, w₁, -a⟩` is
-- isotropic, the bridge to the ternary criterion of `RankCriteria.lean`.
omit [HasBilinHilbertSym k] in
private lemma weightedSumSquares_two_represents_iff_ternary (w : Fin 2 → kˣ) (a : kˣ) :
    (weightedSumSquares k w).represents (a : k) ↔
      (weightedSumSquares k ![(w 0 : k), (w 1 : k), -(a : k)]).Isotropic := by
  rw [weightedSumSquares_units_coe (w := w)]
  have key2 : ∀ x : Fin 2 → k,
      (weightedSumSquares k (fun i => (w i : k))) x =
        (w 0 : k) * x 0 ^ 2 + (w 1 : k) * x 1 ^ 2 := by
    intro x
    simp [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul, pow_two]
  have key3 : ∀ y : Fin 3 → k,
      (weightedSumSquares k ![(w 0 : k), (w 1 : k), -(a : k)]) y =
        (w 0 : k) * y 0 ^ 2 + (w 1 : k) * y 1 ^ 2 + (-(a : k)) * y 2 ^ 2 := by
    intro y
    simp [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul, pow_two]
  constructor
  · rintro ⟨x, _hx, hxQ⟩
    refine ⟨![x 0, x 1, 1], ?_, ?_⟩
    · intro h0
      have h1 : (1 : k) = 0 := by simpa using congr_fun h0 2
      exact one_ne_zero h1
    · rw [key3]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [key2] at hxQ
      linear_combination hxQ
  · rintro ⟨y, hy, hyQ⟩
    rw [key3] at hyQ
    by_cases hy2 : y 2 = 0
    · have hyQ' : (w 0 : k) * y 0 ^ 2 + (w 1 : k) * y 1 ^ 2 = 0 := by
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
      have hiso : (weightedSumSquares k (fun i => (w i : k))).Isotropic := by
        refine ⟨![y 0, y 1], hneq, ?_⟩
        rw [key2]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact hyQ'
      exact represents_of_isotropic_nondegenerate (nondegenerate_weightedSumSquares w) hiso (a : k)
    · set x : Fin 2 → k := ![y 0 / y 2, y 1 / y 2] with hx_def
      have hxval : (weightedSumSquares k (fun i => (w i : k))) x = (a : k) := by
        rw [key2]
        simp only [hx_def, Matrix.cons_val_zero, Matrix.cons_val_one]
        have hdiv : (w 0 : k) * (y 0 / y 2) ^ 2 + (w 1 : k) * (y 1 / y 2) ^ 2 =
            ((w 0 : k) * y 0 ^ 2 + (w 1 : k) * y 1 ^ 2) / y 2 ^ 2 := by
          field_simp [hy2]
        rw [hdiv]
        have hthis : (w 0 : k) * y 0 ^ 2 + (w 1 : k) * y 1 ^ 2 = (a : k) * y 2 ^ 2 := by
          linear_combination hyQ
        rw [hthis, mul_div_assoc, div_self (pow_ne_zero 2 hy2), mul_one]
      exact ⟨x, fun h0 => by
        rw [h0, map_zero] at hxval
        exact Units.ne_zero a hxval.symm, hxval⟩

-- Theorem: the rank-two criterion for a diagonal form with unit weights.
theorem weightedSumSquares_represents_iff_of_rank_two (w : Fin 2 → kˣ) (a : kˣ) :
    (weightedSumSquares k w).represents (a : k) ↔
      hilbertSym (a : k) (-∏ i, (w i : k)) = hasseMinkowskiInvAux w := by
  rw [weightedSumSquares_two_represents_iff_ternary w a]
  rw [weightedSumSquares_isotropic_iff_hilbertSym_eq_one (w 0 : k) (w 1 : k) (-(a : k))
    (Units.ne_zero _) (Units.ne_zero _) (neg_ne_zero.mpr (Units.ne_zero _))]
  rw [neg_neg, hilbertSym_mul_mul (a := (w 0 : k)) (b := (w 1 : k)) (c := (a : k)),
    hasseMinkowskiInvAux_two, Fin.prod_univ_two]
  refine mul_eq_one_iff_eq_of_signs ?_ ?_
  · exact hilbertSym_eq_one_or_neg_one_of_ne_zero (Units.ne_zero a)
      (neg_ne_zero.mpr (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)))
  · exact hilbertSym_eq_one_or_neg_one_of_ne_zero (Units.ne_zero _) (Units.ne_zero _)

end DiagonalTwo

/-! ### Discriminants and the product of the diagonal weights

An isometry `e : Q ≅ ⟨w⟩` changes the discriminant by the square of `det e`, and the Hilbert
symbol against a nonzero argument cannot see square factors.  Hence `-Q.discr b` and `-∏ wᵢ`
have the same Hilbert symbol against every unit. -/

section Discr

variable [Invertible (2 : k)] [HasBilinHilbertSym k]

-- Theorem: the Hilbert symbol against `a` is unchanged when `∏ wᵢ` is replaced by `discr Q b`,
-- since the two differ by the square of the change-of-basis determinant.
private lemma hilbertSym_neg_discr_eq_neg_prod {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module k V] (Q : QuadraticForm k V) (b : Basis (Fin n) k V) {w : Fin n → kˣ}
    (hw : Q.Equivalent (weightedSumSquares k w)) (hdiscr : Q.discr b ≠ 0) (a : kˣ) :
    hilbertSym (a : k) (-Q.discr b) = hilbertSym (a : k) (-∏ i, (w i : k)) := by
  obtain ⟨e⟩ := hw
  let b' : Basis (Fin n) k (Fin n → k) := Pi.basisFun k (Fin n)
  let M := LinearMap.toMatrix b b' e.toLinearEquiv
  have hcomp : (weightedSumSquares k w).comp e.toLinearEquiv = Q := by
    ext x
    rw [QuadraticMap.comp_apply]
    exact e.map_app x
  have hdisc := QuadraticForm.discr_comp (b := b) (b' := b')
    (Q := weightedSumSquares k w) (f := e.toLinearEquiv)
  rw [hcomp, weightedSumSquares_discr] at hdisc
  simp only [Units.smul_def, smul_eq_mul, mul_one] at hdisc
  have hdet : M.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at hdisc
    exact hdiscr hdisc
  have hsq : hilbertSym (a : k) M.det * hilbertSym (a : k) M.det = 1 := by
    rcases hilbertSym_eq_one_or_neg_one_of_ne_zero (Units.ne_zero a) hdet with h | h <;>
      rw [h] <;> norm_num
  calc hilbertSym (a : k) (-Q.discr b)
      = hilbertSym (a : k) (-(M.det * M.det * ∏ i, (w i : k))) := by rw [hdisc]
    _ = hilbertSym (a : k) ((-(∏ i, (w i : k))) * M.det * M.det) := by
        rw [show -(M.det * M.det * ∏ i, (w i : k)) =
          (-(∏ i, (w i : k))) * M.det * M.det by ring]
    _ = hilbertSym (a : k) (-(∏ i, (w i : k))) := by
        rw [HasBilinHilbertSym.mul_right_eq, HasBilinHilbertSym.mul_right_eq,
          mul_assoc, hsq, mul_one]

end Discr

/-! ### Two elementary transports

Nondegeneracy gives a separating associated form, and an isometry transports the values
represented by a form. -/

section Transport

variable [Invertible (2 : k)]

-- Theorem: the associated bilinear form of a nondegenerate quadratic form is separating left.
private theorem separatingLeft_of_nondegenerate {V : Type*} [AddCommGroup V] [Module k V]
    {Q : QuadraticForm k V} (hQ : Q.Nondegenerate) :
    (QuadraticMap.associated (R := k) Q).SeparatingLeft :=
  (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1

end Transport

-- Theorem: equivalent quadratic forms represent exactly the same values.
private theorem equivalent_represents_iff {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁]
    [AddCommGroup M₂] [Module R M₁] [Module R M₂] {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} (h : Q₁.Equivalent Q₂) (a : R) :
    Q₁.represents a ↔ Q₂.represents a := by
  obtain ⟨e⟩ := h
  constructor
  · rintro ⟨x, hx, hxQ⟩
    exact ⟨e x, fun h0 => hx (by simpa using congrArg (⇑e.symm) h0),
      by rw [e.map_app x, hxQ]⟩
  · rintro ⟨x, hx, hxQ⟩
    exact ⟨e.symm x, fun h0 => hx (by simpa using congrArg (⇑e) h0),
      by rw [e.symm.map_app x, hxQ]⟩

/-! ### The general rank-two criterion -/

-- Theorem: a nondegenerate rank-two form `Q` represents `a : kˣ` exactly when
-- `(a, -discr Q) = ε(Q)`.
theorem represents_iff_of_rank_two
    [Invertible (2 : k)] [HasBilinHilbertSym k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (b : Basis (Fin 2) k V) (hr : finrank k V = 2)
    {Q : QuadraticForm k V} (hQ : Q.Nondegenerate) (a : kˣ)
    (hconn : ∀ {n : ℕ} (w w' : Fin n → kˣ),
      (weightedSumSquares k w).Equivalent (weightedSumSquares k w') →
        Relation.ReflTransGen (Step n) w w') :
    Q.represents (a : k) ↔
      hilbertSym (a : k) (-Q.discr b) =
        hasseMinkowskiInv Q (separatingLeft_of_nondegenerate hQ) := by
  have hsep : (QuadraticMap.associated (R := k) Q).SeparatingLeft :=
    separatingLeft_of_nondegenerate hQ
  obtain ⟨w₀, hw₀⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
  let w : Fin 2 → kˣ := w₀ ∘ finCongr hr.symm
  have hw : Q.Equivalent (weightedSumSquares k w) :=
    hw₀.trans ⟨wssCongr (finCongr hr.symm) w₀⟩
  have hdiscr : Q.discr b ≠ 0 := (nondegenerate_iff_discr_ne_zero b Q).mp hQ
  have hd2 := hilbertSym_neg_discr_eq_neg_prod Q b hw hdiscr a
  have hfin := hasseMinkowskiInvAux_finCongr (k := k) hr.symm w₀
  have hinv : hasseMinkowskiInv Q hsep = hasseMinkowskiInvAux w :=
    (hasseMinkowskiInv_eq_aux_of_equiv hconn Q hsep hw₀).trans (by simpa [w] using hfin.symm)
  rw [equivalent_represents_iff hw (a : k),
    weightedSumSquares_represents_iff_of_rank_two w a, hd2, hinv]

/-! ### The diagonal rank-three criterion -/

section DiagonalThree

variable [HasBilinHilbertSym k]

-- Theorem: the rank-three criterion for a diagonal form with unit weights.
theorem weightedSumSquares_isotropic_iff_of_rank_three (w : Fin 3 → kˣ) :
    Isotropic (weightedSumSquares k w) ↔
      hilbertSym (-1) (-∏ i, (w i : k)) = hasseMinkowskiInvAux w := by
  have hw3 : (![w 0, w 1, w 2] : Fin 3 → kˣ) = w := by
    funext i
    fin_cases i <;> rfl
  have h := represents_zero_iff_of_rank_three_diag (w 0) (w 1) (w 2)
  rw [hw3] at h
  simpa only [Fin.prod_univ_three] using h

end DiagonalThree

/-! ### The general rank-three criterion -/

-- Theorem: a nondegenerate rank-three form `Q` is isotropic exactly when
-- `(-1, -discr Q) = ε(Q)`.
theorem represents_zero_iff_of_rank_three
    [Invertible (2 : k)] [HasBilinHilbertSym k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (b : Basis (Fin 3) k V) (hr : finrank k V = 3)
    {Q : QuadraticForm k V} (hQ : Q.Nondegenerate)
    (hconn : ∀ {n : ℕ} (w w' : Fin n → kˣ),
      (weightedSumSquares k w).Equivalent (weightedSumSquares k w') →
        Relation.ReflTransGen (Step n) w w') :
    Q.Isotropic ↔
      hilbertSym (-1 : k) (-Q.discr b) =
        hasseMinkowskiInv Q (separatingLeft_of_nondegenerate hQ) := by
  have hsep : (QuadraticMap.associated (R := k) Q).SeparatingLeft :=
    separatingLeft_of_nondegenerate hQ
  obtain ⟨w₀, hw₀⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
  let w : Fin 3 → kˣ := w₀ ∘ finCongr hr.symm
  have hw : Q.Equivalent (weightedSumSquares k w) :=
    hw₀.trans ⟨wssCongr (finCongr hr.symm) w₀⟩
  have hdiscr : Q.discr b ≠ 0 := (nondegenerate_iff_discr_ne_zero b Q).mp hQ
  have hd2 : hilbertSym (-1 : k) (-Q.discr b) =
      hilbertSym (-1 : k) (-∏ i, (w i : k)) := by
    simpa using hilbertSym_neg_discr_eq_neg_prod Q b hw hdiscr (-1 : kˣ)
  have hfin := hasseMinkowskiInvAux_finCongr (k := k) hr.symm w₀
  have hinv : hasseMinkowskiInv Q hsep = hasseMinkowskiInvAux w :=
    (hasseMinkowskiInv_eq_aux_of_equiv hconn Q hsep hw₀).trans (by simpa [w] using hfin.symm)
  refine (QuadraticMap.Equivalent.isotropic_iff hw).trans ?_
  rw [weightedSumSquares_isotropic_iff_of_rank_three w, hd2, hinv]

end Pptc.HasseMinkowski
