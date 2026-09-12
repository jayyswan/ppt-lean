import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
### Elementary inertia lemmas

If a matrix form has a two-dimensional negative-definite (resp. positive-definite)
subspace, then any diagonal form congruent to it has at least two negative (resp.
positive) diagonal entries. This is the piece of Sylvester's law of inertia the
degree-7 Bring–Jerrard construction needs.
-/

open Matrix

namespace Pconstructible

variable {n : ℕ}

/-- The quadratic form attached to a matrix, `x ⬝ᵥ (A *ᵥ x)`. -/
noncomputable def qform (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

/-- The bilinear form attached to a matrix, `x ⬝ᵥ (A *ᵥ y)`. -/
noncomputable def bilin (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ y)

-- Theorem: the quadratic form is transported by a congruence.
theorem qform_congr (A U : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    qform (Uᵀ * A * U) y = qform A (U *ᵥ y) := by
  unfold qform
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

-- Theorem: on a diagonal matrix the quadratic form is the weighted sum of squares.
theorem qform_diag {D : Matrix (Fin n) (Fin n) ℝ} (hdiag : ∀ i j, i ≠ j → D i j = 0)
    (z : Fin n → ℝ) :
    qform D z = ∑ i, D i i * z i ^ 2 := by
  simp only [qform, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    rw [hdiag i j (Ne.symm hji), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

-- Theorem: a diagonal form whose weighted square sum is negative along two
-- independent directions has two negative diagonal entries.
theorem two_neg_of_negDef {D : Matrix (Fin n) (Fin n) ℝ}
    (_hdiag : ∀ i j, i ≠ j → D i j = 0) {v1 v2 : Fin n → ℝ}
    (hneg : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) →
      (∑ i, D i i * (a * v1 i + b * v2 i) ^ 2) < 0) :
    ∃ i j : Fin n, i ≠ j ∧ D i i < 0 ∧ D j j < 0 := by
  by_contra h
  have hno : ∀ i j, i ≠ j → D i i < 0 → D j j < 0 → False := by
    intro i j hij hi hj
    exact h ⟨i, j, hij, hi, hj⟩
  by_cases hk : ∃ k, D k k < 0
  · obtain ⟨k, hk⟩ := hk
    have hother : ∀ i, i ≠ k → 0 ≤ D i i := by
      intro i hik
      by_contra hlt
      exact hno k i (Ne.symm hik) hk (lt_of_not_ge hlt)
    by_cases hv1 : v1 k = 0
    · have hsum := hneg 1 0 (Or.inl one_ne_zero)
      have hnn : 0 ≤ ∑ i, D i i * (1 * v1 i + 0 * v2 i) ^ 2 := by
        apply Finset.sum_nonneg
        intro i _
        by_cases hik : i = k
        · simp [hik, hv1]
        · exact mul_nonneg (hother i hik) (sq_nonneg _)
      linarith
    · have hsum := hneg (v2 k) (-v1 k) (Or.inr (neg_ne_zero.mpr hv1))
      have hnn : 0 ≤ ∑ i, D i i * (v2 k * v1 i + (-v1 k) * v2 i) ^ 2 := by
        apply Finset.sum_nonneg
        intro i _
        by_cases hik : i = k
        · rw [hik]
          have hz : v2 k * v1 k + -v1 k * v2 k = 0 := by ring
          rw [hz]; norm_num
        · exact mul_nonneg (hother i hik) (sq_nonneg _)
      linarith
  · have hnonneg : ∀ i, 0 ≤ D i i := by
      intro i
      by_contra hlt
      exact hk ⟨i, lt_of_not_ge hlt⟩
    have hnn : 0 ≤ ∑ i, D i i * (1 * v1 i + 0 * v2 i) ^ 2 := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (hnonneg i) (sq_nonneg _)
    have hsum := hneg 1 0 (Or.inl one_ne_zero)
    linarith

-- Theorem: a diagonal form whose weighted square sum is positive along two
-- independent directions has two positive diagonal entries.
theorem two_pos_of_posDef {D : Matrix (Fin n) (Fin n) ℝ}
    (_hdiag : ∀ i j, i ≠ j → D i j = 0) {v1 v2 : Fin n → ℝ}
    (hpos : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) →
      0 < (∑ i, D i i * (a * v1 i + b * v2 i) ^ 2)) :
    ∃ i j : Fin n, i ≠ j ∧ 0 < D i i ∧ 0 < D j j := by
  by_contra h
  have hno : ∀ i j, i ≠ j → 0 < D i i → 0 < D j j → False := by
    intro i j hij hi hj
    exact h ⟨i, j, hij, hi, hj⟩
  by_cases hk : ∃ k, 0 < D k k
  · obtain ⟨k, hk⟩ := hk
    have hother : ∀ i, i ≠ k → D i i ≤ 0 := by
      intro i hik
      by_contra hlt
      exact hno k i (Ne.symm hik) hk (lt_of_not_ge hlt)
    by_cases hv1 : v1 k = 0
    · have hsum := hpos 1 0 (Or.inl one_ne_zero)
      have hnp : (∑ i, D i i * (1 * v1 i + 0 * v2 i) ^ 2) ≤ 0 := by
        apply Finset.sum_nonpos
        intro i _
        by_cases hik : i = k
        · simp [hik, hv1]
        · exact mul_nonpos_of_nonpos_of_nonneg (hother i hik) (sq_nonneg _)
      linarith
    · have hsum := hpos (v2 k) (-v1 k) (Or.inr (neg_ne_zero.mpr hv1))
      have hnp : (∑ i, D i i * (v2 k * v1 i + (-v1 k) * v2 i) ^ 2) ≤ 0 := by
        apply Finset.sum_nonpos
        intro i _
        by_cases hik : i = k
        · rw [hik]
          have hz : v2 k * v1 k + -v1 k * v2 k = 0 := by ring
          rw [hz]; norm_num
        · exact mul_nonpos_of_nonpos_of_nonneg (hother i hik) (sq_nonneg _)
      linarith
  · have hnonpos : ∀ i, D i i ≤ 0 := by
      intro i
      by_contra hlt
      exact hk ⟨i, lt_of_not_ge hlt⟩
    have hnp : (∑ i, D i i * (1 * v1 i + 0 * v2 i) ^ 2) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      exact mul_nonpos_of_nonpos_of_nonneg (hnonpos i) (sq_nonneg _)
    have hsum := hpos 1 0 (Or.inl one_ne_zero)
    linarith

-- Theorem: under an invertible congruence, two negative directions for `A`
-- force two negative diagonal entries of any diagonal `D` congruent to `A`.
theorem two_neg_diag_of_pair {A D U : Matrix (Fin n) (Fin n) ℝ}
    (hdiag : ∀ i j, i ≠ j → D i j = 0) (hUD : Uᵀ * A * U = D) (hdet : U.det ≠ 0)
    {v1 v2 : Fin n → ℝ}
    (hneg : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → qform A (a • v1 + b • v2) < 0) :
    ∃ i j : Fin n, i ≠ j ∧ D i i < 0 ∧ D j j < 0 := by
  let z1 : Fin n → ℝ := U⁻¹ *ᵥ v1
  let z2 : Fin n → ℝ := U⁻¹ *ᵥ v2
  have hUi : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U (isUnit_iff_ne_zero.mpr hdet)
  have hzv : ∀ a b : ℝ, U *ᵥ (a • z1 + b • z2) = a • v1 + b • v2 := by
    intro a b
    simp only [z1, z2, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      hUi, Matrix.one_mulVec]
  refine two_neg_of_negDef hdiag (v1 := z1) (v2 := z2) (fun a b hab => ?_)
  have hq : qform D (a • z1 + b • z2) = qform A (a • v1 + b • v2) := by
    rw [← hUD, qform_congr, hzv]
  have hsum : (∑ i, D i i * (a * z1 i + b * z2 i) ^ 2) = qform D (a • z1 + b • z2) := by
    rw [qform_diag hdiag]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum, hq]
  exact hneg a b hab

-- Theorem: under an invertible congruence, two positive directions for `A`
-- force two positive diagonal entries of any diagonal `D` congruent to `A`.
theorem two_pos_diag_of_pair {A D U : Matrix (Fin n) (Fin n) ℝ}
    (hdiag : ∀ i j, i ≠ j → D i j = 0) (hUD : Uᵀ * A * U = D) (hdet : U.det ≠ 0)
    {v1 v2 : Fin n → ℝ}
    (hpos : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < qform A (a • v1 + b • v2)) :
    ∃ i j : Fin n, i ≠ j ∧ 0 < D i i ∧ 0 < D j j := by
  let z1 : Fin n → ℝ := U⁻¹ *ᵥ v1
  let z2 : Fin n → ℝ := U⁻¹ *ᵥ v2
  have hUi : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U (isUnit_iff_ne_zero.mpr hdet)
  have hzv : ∀ a b : ℝ, U *ᵥ (a • z1 + b • z2) = a • v1 + b • v2 := by
    intro a b
    simp only [z1, z2, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      hUi, Matrix.one_mulVec]
  refine two_pos_of_posDef hdiag (v1 := z1) (v2 := z2) (fun a b hab => ?_)
  have hq : qform D (a • z1 + b • z2) = qform A (a • v1 + b • v2) := by
    rw [← hUD, qform_congr, hzv]
  have hsum : (∑ i, D i i * (a * z1 i + b * z2 i) ^ 2) = qform D (a • z1 + b • z2) := by
    rw [qform_diag hdiag]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum, hq]
  exact hpos a b hab

end Pconstructible
