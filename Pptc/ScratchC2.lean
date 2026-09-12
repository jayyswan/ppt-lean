import Pptc.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fintype

open Polynomial
open Matrix

namespace Pconstructible

/-! ### Helpers: P-constructibility of finite sums and matrix operations -/

lemma Finset.sum_Pconstructible {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, PConstructible (f i)) : PConstructible (s.sum f) := by
  induction s using Finset.induction_on with
  | empty => simpa using zero_Pconstructible
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact PConstructible.add (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma mul_entries_Pconstructible {m n o : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix m n ℝ} {N : Matrix n o ℝ}
    (hM : ∀ i j, PConstructible (M i j)) (hN : ∀ i j, PConstructible (N i j)) :
    ∀ i j, PConstructible ((M * N) i j) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_Pconstructible Finset.univ (fun k => M i k * N k j)
    (fun k _ => PConstructible.mul (hM i k) (hN k j))

lemma add_entries_Pconstructible {m n : Type*} {M N : Matrix m n ℝ}
    (hM : ∀ i j, PConstructible (M i j)) (hN : ∀ i j, PConstructible (N i j)) :
    ∀ i j, PConstructible ((M + N) i j) := by
  intro i j
  rw [Matrix.add_apply]
  exact PConstructible.add (hM i j) (hN i j)

lemma neg_entries_Pconstructible {m n : Type*} {M : Matrix m n ℝ}
    (hM : ∀ i j, PConstructible (M i j)) : ∀ i j, PConstructible ((-M) i j) := by
  intro i j
  rw [Matrix.neg_apply]
  exact neg_Pconstructible (hM i j)

lemma smul_entries_Pconstructible {m n : Type*} {c : ℝ} (hc : PConstructible c)
    {M : Matrix m n ℝ} (hM : ∀ i j, PConstructible (M i j)) :
    ∀ i j, PConstructible ((c • M) i j) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact PConstructible.mul hc (hM i j)

/-! ### Helpers: reindexing a congruence -/

lemma reindex_congr {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) {A U D : Matrix m m ℝ} (h : Uᵀ * A * U = D) :
    (reindex e e U)ᵀ * (reindex e e A) * (reindex e e U) = reindex e e D := by
  have h' := congrArg (reindexRingEquiv ℝ e) h
  simpa only [map_mul, coe_reindexRingEquiv, transpose_reindex] using h'

lemma reindex_entries_Pconstructible {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) {M : Matrix m m ℝ}
    (hM : ∀ i j, PConstructible (M i j)) :
    ∀ i j, PConstructible ((reindex e e M) i j) := by
  intro i j
  exact hM (e.symm i) (e.symm j)

lemma reindex_symm {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) {M : Matrix m m ℝ} (h : Mᵀ = M) :
    (reindex e e M)ᵀ = reindex e e M := by
  rw [transpose_reindex, h]

lemma reindex_diag {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) {D : Matrix m m ℝ} (h : ∀ i j, i ≠ j → D i j = 0) :
    ∀ i j, i ≠ j → (reindex e e D) i j = 0 := by
  intro i j hij
  exact h (e.symm i) (e.symm j) (fun hh => hij (by simpa using congrArg e hh))

/-! ### Helpers: lifting a congruence through a block diagonal -/

set_option maxHeartbeats 800000 in
lemma lift_block {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (S Ds : Matrix β β ℝ) (A22 : Matrix γ γ ℝ) (Us : Matrix β β ℝ)
    (h : Usᵀ * S * Us = Ds) :
    (fromBlocks Us 0 0 (1 : Matrix γ γ ℝ))ᵀ * fromBlocks S 0 0 A22 *
        (fromBlocks Us 0 0 (1 : Matrix γ γ ℝ)) = fromBlocks Ds 0 0 A22 := by
  simp [fromBlocks_transpose, fromBlocks_multiply, h]

/-! ### The pivot equivalence -/

def pivotEquiv {α : Type} [DecidableEq α] (i : α) :
    α ≃ {a : α // a ≠ i} ⊕ {a : α // a = i} where
  toFun a := if h : a = i then Sum.inr ⟨a, h⟩ else Sum.inl ⟨a, h⟩
  invFun s := match s with
    | Sum.inl x => (x : α)
    | Sum.inr y => (y : α)
  left_inv a := by by_cases h : a = i <;> simp [h]
  right_inv s := by
    rcases s with x | y
    · obtain ⟨a, ha⟩ := x
      simp [ha]
    · obtain ⟨a, ha⟩ := y
      simp [ha]

@[simp]
theorem pivotEquiv_symm_apply_inl {α : Type} [DecidableEq α] (i : α)
    (x : {a : α // a ≠ i}) : (pivotEquiv i).symm (Sum.inl x) = x := by
  simp [pivotEquiv]

@[simp]
theorem pivotEquiv_symm_apply_inr {α : Type} [DecidableEq α] (i : α)
    (y : {a : α // a = i}) : (pivotEquiv i).symm (Sum.inr y) = y := by
  simp [pivotEquiv]

@[simp]
theorem pivotEquiv_apply_of_ne {α : Type} [DecidableEq α] {i a : α} (h : a ≠ i) :
    pivotEquiv i a = Sum.inl ⟨a, h⟩ := by
  simp [pivotEquiv, h]

@[simp]
theorem pivotEquiv_apply_of_eq {α : Type} [DecidableEq α] {i a : α} (h : a = i) :
    pivotEquiv i a = Sum.inr ⟨a, h⟩ := by
  simp [pivotEquiv, h]

/-! ### Block elimination -/

set_option maxHeartbeats 800000 in
lemma block_elim {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (A : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) (hsym : Aᵀ = A)
    (h22 : IsUnit (A.toBlocks₂₂).det) :
    (fromBlocks (1 : Matrix β β ℝ) 0 (-((A.toBlocks₂₂)⁻¹ * A.toBlocks₂₁)) 1)ᵀ * A *
        (fromBlocks (1 : Matrix β β ℝ) 0 (-((A.toBlocks₂₂)⁻¹ * A.toBlocks₂₁)) 1) =
      fromBlocks
        (A.toBlocks₁₁ + A.toBlocks₁₂ * (-((A.toBlocks₂₂)⁻¹ * A.toBlocks₂₁))) 0 0
        A.toBlocks₂₂ := by
  set A11 := A.toBlocks₁₁
  set A12 := A.toBlocks₁₂
  set A21 := A.toBlocks₂₁
  set A22 := A.toBlocks₂₂
  set Y : Matrix γ β ℝ := -(A22⁻¹ * A21) with hY
  have hAeq : A = fromBlocks A11 A12 A21 A22 := (fromBlocks_toBlocks A).symm
  have hs' : (fromBlocks A11 A12 A21 A22)ᵀ = fromBlocks A11 A12 A21 A22 := by
    rw [← hAeq]; exact hsym
  have hblocks := hs'
  rw [fromBlocks_transpose, fromBlocks_inj] at hblocks
  have hs21 : A21ᵀ = A12 := hblocks.2.1
  have hs22 : A22ᵀ = A22 := hblocks.2.2.2
  have hmul22 : A22 * A22⁻¹ = 1 := mul_nonsing_inv A22 h22
  have hmul22' : A22⁻¹ * A22 = 1 := nonsing_inv_mul A22 h22
  have hA21Y : A22 * Y = -A21 := by
    rw [hY]
    calc A22 * (-(A22⁻¹ * A21)) = -(A22 * (A22⁻¹ * A21)) := by rw [Matrix.mul_neg]
      _ = -((A22 * A22⁻¹) * A21) := by rw [Matrix.mul_assoc]
      _ = -A21 := by rw [hmul22, Matrix.one_mul]
  have hY22 : Yᵀ * A22 = -A12 := by
    rw [hY]
    calc (-(A22⁻¹ * A21))ᵀ * A22 = (-(A21ᵀ * (A22⁻¹)ᵀ)) * A22 := by
          rw [Matrix.transpose_neg, Matrix.transpose_mul]
      _ = -(A21ᵀ * (A22⁻¹)ᵀ * A22) := by rw [Matrix.neg_mul]
      _ = -(A21ᵀ * A22⁻¹ * A22) := by rw [transpose_nonsing_inv, hs22]
      _ = -(A21ᵀ * (A22⁻¹ * A22)) := by rw [Matrix.mul_assoc]
      _ = -A12 := by rw [hmul22', Matrix.mul_one, hs21]
  have hYA21 : Yᵀ * A21 = A12 * Y := by
    rw [hY]
    calc (-(A22⁻¹ * A21))ᵀ * A21 = (-(A21ᵀ * (A22⁻¹)ᵀ)) * A21 := by
          rw [Matrix.transpose_neg, Matrix.transpose_mul]
      _ = -(A21ᵀ * (A22⁻¹)ᵀ * A21) := by rw [Matrix.neg_mul]
      _ = -(A21ᵀ * A22⁻¹ * A21) := by rw [transpose_nonsing_inv, hs22]
      _ = -(A21ᵀ * (A22⁻¹ * A21)) := by rw [Matrix.mul_assoc]
      _ = A12 * (-(A22⁻¹ * A21)) := by rw [Matrix.mul_neg, ← hs21]
  rw [hAeq]
  rw [show (fromBlocks (1 : Matrix β β ℝ) 0 Y 1)ᵀ = fromBlocks 1 Yᵀ 0 1 by
    rw [fromBlocks_transpose]; simp]
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, hYA21, hY22, add_neg_cancel,
      add_zero]
  · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, hY22, add_neg_cancel, add_zero]
  · simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, hA21Y, add_neg_cancel, zero_add]
  · simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add]

set_option maxHeartbeats 800000 in
lemma block_elim_symm {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (A : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) (hsym : Aᵀ = A) :
    (A.toBlocks₁₁ + A.toBlocks₁₂ * (-((A.toBlocks₂₂)⁻¹ * A.toBlocks₂₁)))ᵀ =
      A.toBlocks₁₁ + A.toBlocks₁₂ * (-((A.toBlocks₂₂)⁻¹ * A.toBlocks₂₁)) := by
  set A11 := A.toBlocks₁₁
  set A12 := A.toBlocks₁₂
  set A21 := A.toBlocks₂₁
  set A22 := A.toBlocks₂₂
  set Y : Matrix γ β ℝ := -(A22⁻¹ * A21) with hY
  have hAeq : A = fromBlocks A11 A12 A21 A22 := (fromBlocks_toBlocks A).symm
  have hs' : (fromBlocks A11 A12 A21 A22)ᵀ = fromBlocks A11 A12 A21 A22 := by
    rw [← hAeq]; exact hsym
  have hblocks := hs'
  rw [fromBlocks_transpose, fromBlocks_inj] at hblocks
  have hs11 : A11ᵀ = A11 := hblocks.1
  have hs21 : A21ᵀ = A12 := hblocks.2.1
  have hs22 : A22ᵀ = A22 := hblocks.2.2.2
  have hs12 : A12ᵀ = A21 := by rw [← hs21, Matrix.transpose_transpose]
  have hYA21 : Yᵀ * A21 = A12 * Y := by
    rw [hY]
    calc (-(A22⁻¹ * A21))ᵀ * A21 = (-(A21ᵀ * (A22⁻¹)ᵀ)) * A21 := by
          rw [Matrix.transpose_neg, Matrix.transpose_mul]
      _ = -(A21ᵀ * (A22⁻¹)ᵀ * A21) := by rw [Matrix.neg_mul]
      _ = -(A21ᵀ * A22⁻¹ * A21) := by rw [transpose_nonsing_inv, hs22]
      _ = -(A21ᵀ * (A22⁻¹ * A21)) := by rw [Matrix.mul_assoc]
      _ = A12 * (-(A22⁻¹ * A21)) := by rw [Matrix.mul_neg, ← hs21]
  calc (A11 + A12 * Y)ᵀ = A11ᵀ + (A12 * Y)ᵀ := by rw [Matrix.transpose_add]
    _ = A11 + Yᵀ * A12ᵀ := by rw [Matrix.transpose_mul, hs11]
    _ = A11 + Yᵀ * A21 := by rw [hs12]
    _ = A11 + A12 * Y := by rw [hYA21]

/-! ### Lifting a congruence back across an equivalence -/

lemma reindex_reindex_symm {m n : Type*} (e : m ≃ n) (M : Matrix m m ℝ) :
    reindex e.symm e.symm (reindex e e M) = M := by
  rw [← Matrix.reindex_symm e e]
  exact Equiv.symm_apply_apply (reindex e e) M

lemma one_entries_Pconstructible {m : Type*} [DecidableEq m] :
    ∀ i j, PConstructible ((1 : Matrix m m ℝ) i j) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs with h
  · exact PConstructible.base_one
  · exact zero_Pconstructible

/-! ### Eliminating a nonzero diagonal entry -/

set_option maxHeartbeats 1200000 in
lemma diag_congr_of_pivot {α : Type} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hsym : Aᵀ = A) (hA : ∀ p q, PConstructible (A p q))
    (i : α) (hi : A i i ≠ 0)
    (ih : ∀ (β : Type) [Fintype β] [DecidableEq β], Fintype.card β < Fintype.card α →
      ∀ (B : Matrix β β ℝ), Bᵀ = B → (∀ p q, PConstructible (B p q)) →
        ∃ U D : Matrix β β ℝ,
          (∀ p q, PConstructible (U p q)) ∧ (∀ p q, PConstructible (D p q)) ∧
          (∀ p q, p ≠ q → D p q = 0) ∧ Uᵀ * B * U = D ∧ U.det ≠ 0) :
    ∃ U D : Matrix α α ℝ,
      (∀ p q, PConstructible (U p q)) ∧ (∀ p q, PConstructible (D p q)) ∧
      (∀ p q, p ≠ q → D p q = 0) ∧ Uᵀ * A * U = D ∧ U.det ≠ 0 := by
  let β := {a : α // a ≠ i}
  let γ := {a : α // a = i}
  let e : α ≃ β ⊕ γ := pivotEquiv i
  let B : Matrix (β ⊕ γ) (β ⊕ γ) ℝ := reindex e e A
  have hBsym : Bᵀ = B := reindex_symm e hsym
  have hBP : ∀ p q, PConstructible (B p q) := reindex_entries_Pconstructible e hA
  let d : ℝ := A i i
  have hd : d ≠ 0 := hi
  have hB22 : B.toBlocks₂₂ = d • (1 : Matrix γ γ ℝ) := by
    ext y y'
    change A ((pivotEquiv i).symm (Sum.inr y)) ((pivotEquiv i).symm (Sum.inr y')) =
      (d • (1 : Matrix γ γ ℝ)) y y'
    rw [pivotEquiv_symm_apply_inr, pivotEquiv_symm_apply_inr, y.2, y'.2]
    simp [d, Subsingleton.elim y y']
  have h22 : IsUnit (B.toBlocks₂₂).det := by
    have hdet : (B.toBlocks₂₂).det = d := by
      rw [hB22, Matrix.det_smul, Matrix.det_one, Fintype.card_unique, pow_one, mul_one]
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr hd
  have hcongr := block_elim B hBsym h22
  have hSsym := block_elim_symm B hBsym
  let Y : Matrix γ β ℝ := -((B.toBlocks₂₂)⁻¹ * B.toBlocks₂₁)
  let S : Matrix β β ℝ := B.toBlocks₁₁ + B.toBlocks₁₂ * Y
  have hB22inv_apply : ∀ y y' : γ, (B.toBlocks₂₂)⁻¹ y y' = d⁻¹ := by
    intro y y'
    have hinv : (B.toBlocks₂₂)⁻¹ = d⁻¹ • (1 : Matrix γ γ ℝ) := by
      apply Matrix.inv_eq_right_inv
      rw [hB22, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        mul_inv_cancel₀ hd, one_smul]
    rw [hinv]
    simp [Matrix.smul_apply, Subsingleton.elim y y']
  have hYentry : ∀ y q, PConstructible (Y y q) := by
    intro y q
    have h22invP : ∀ y y' : γ, PConstructible ((B.toBlocks₂₂)⁻¹ y y') := by
      intro y y'
      rw [hB22inv_apply y y']
      exact inv_Pconstructible (hA i i)
    have h21P : ∀ y q, PConstructible ((B.toBlocks₂₁) y q) :=
      fun y q => hBP (Sum.inr y) (Sum.inl q)
    rw [show Y y q = (-((B.toBlocks₂₂)⁻¹ * B.toBlocks₂₁)) y q from rfl]
    rw [Matrix.neg_apply]
    exact neg_Pconstructible (mul_entries_Pconstructible h22invP h21P y q)
  have hSP : ∀ p q, PConstructible (S p q) := by
    intro p q
    have h11P : ∀ p q, PConstructible ((B.toBlocks₁₁) p q) :=
      fun p q => hBP (Sum.inl p) (Sum.inl q)
    have h12P : ∀ p q, PConstructible ((B.toBlocks₁₂) p q) :=
      fun p q => hBP (Sum.inl p) (Sum.inr q)
    rw [show S p q = (B.toBlocks₁₁ + B.toBlocks₁₂ * Y) p q from rfl]
    exact add_entries_Pconstructible h11P (mul_entries_Pconstructible h12P hYentry) p q
  have hcard : Fintype.card β < Fintype.card α :=
    Fintype.card_subtype_lt (p := fun a : α => a ≠ i) (x := i) (by simp)
  obtain ⟨Us, Ds, hUsP, hDsP, hDsdiag, hUsDs, hUsdet⟩ := ih β hcard S hSsym hSP
  let U1 : Matrix (β ⊕ γ) (β ⊕ γ) ℝ := fromBlocks (1 : Matrix β β ℝ) 0 Y 1
  let U2 : Matrix (β ⊕ γ) (β ⊕ γ) ℝ := fromBlocks Us 0 0 (1 : Matrix γ γ ℝ)
  have hU2 : U2ᵀ * fromBlocks S 0 0 B.toBlocks₂₂ * U2 =
      fromBlocks Ds 0 0 B.toBlocks₂₂ := by
    rw [show U2 = fromBlocks Us 0 0 1 from rfl,
      show S = B.toBlocks₁₁ + B.toBlocks₁₂ * Y from rfl]
    exact lift_block S Ds B.toBlocks₂₂ Us hUsDs
  have hblock : (U1 * U2)ᵀ * B * (U1 * U2) = fromBlocks Ds 0 0 B.toBlocks₂₂ := by
    have step : (U1 * U2)ᵀ * B * (U1 * U2) = U2ᵀ * (U1ᵀ * B * U1) * U2 := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [step, hcongr, hU2]
  have hU1P : ∀ p q, PConstructible (U1 p q) := by
    intro p q
    rcases p with p | y <;> rcases q with q | y'
    · simpa only [U1, Matrix.fromBlocks_apply₁₁] using one_entries_Pconstructible p q
    · simpa only [U1, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using zero_Pconstructible
    · simpa only [U1, Matrix.fromBlocks_apply₂₁] using hYentry y q
    · simpa only [U1, Matrix.fromBlocks_apply₂₂] using one_entries_Pconstructible y y'
  have hUblockP : ∀ p q, PConstructible ((U1 * U2) p q) := by
    refine mul_entries_Pconstructible hU1P ?_
    intro p q
    rcases p with p | y <;> rcases q with q | y'
    · simpa only [U2, Matrix.fromBlocks_apply₁₁] using hUsP p q
    · simpa only [U2, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using zero_Pconstructible
    · simpa only [U2, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using zero_Pconstructible
    · simpa only [U2, Matrix.fromBlocks_apply₂₂] using one_entries_Pconstructible y y'
  have hDblockP : ∀ p q, PConstructible ((fromBlocks Ds 0 0 B.toBlocks₂₂) p q) := by
    intro p q
    rcases p with p | y <;> rcases q with q | y'
    · simpa only [Matrix.fromBlocks_apply₁₁] using hDsP p q
    · simpa only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using zero_Pconstructible
    · simpa only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using zero_Pconstructible
    · have : B.toBlocks₂₂ y y' = d := by
        rw [hB22, Matrix.smul_apply, Matrix.one_apply, if_pos (Subsingleton.elim y y'),
          smul_eq_mul, mul_one]
      rw [Matrix.fromBlocks_apply₂₂, this]
      exact hA i i
  have hDblockdiag : ∀ p q, p ≠ q → (fromBlocks Ds 0 0 B.toBlocks₂₂) p q = 0 := by
    intro p q hpq
    rcases p with p | y <;> rcases q with q | y'
    · exact hDsdiag p q (fun h => hpq (by rw [h]))
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    · exact absurd (congrArg Sum.inr (Subsingleton.elim y y')) hpq
  have hBback : reindex e.symm e.symm B = A := by
    show reindex e.symm e.symm (reindex e e A) = A
    exact reindex_reindex_symm e A
  refine ⟨reindex e.symm e.symm (U1 * U2),
    reindex e.symm e.symm (fromBlocks Ds 0 0 B.toBlocks₂₂), ?_, ?_, ?_, ?_, ?_⟩
  · exact reindex_entries_Pconstructible e.symm hUblockP
  · exact reindex_entries_Pconstructible e.symm hDblockP
  · exact reindex_diag e.symm hDblockdiag
  · rw [← hBback]
    exact reindex_congr e.symm hblock
  · rw [Matrix.det_reindex_self e.symm (U1 * U2), Matrix.det_mul]
    have h1 : U1.det = 1 := by
      rw [show U1 = fromBlocks (1 : Matrix β β ℝ) 0 Y 1 from rfl,
        Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, mul_one]
    have h2 : U2.det = Us.det := by
      rw [show U2 = fromBlocks Us 0 0 (1 : Matrix γ γ ℝ) from rfl,
        Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
    rw [h1, h2, one_mul]
    exact hUsdet

/-! ### The hyperbolic change of basis `!![1,1;1,-1]` embedded at two coordinates -/

def hyper {α : Type} [DecidableEq α] (i j : α) : Matrix α α ℝ :=
  fun p q => if p = q then (if p = i then 1 else if p = j then -1 else 1)
             else (if (p = i ∧ q = j) ∨ (p = j ∧ q = i) then 1 else 0)

lemma hyper_symm {α : Type} [DecidableEq α] (i j : α) : (hyper i j)ᵀ = hyper i j := by
  ext p q
  simp only [Matrix.transpose_apply, hyper]
  by_cases hpq : p = q
  · subst hpq; simp
  · rw [if_neg hpq, if_neg (Ne.symm hpq)]
    by_cases h : (p = i ∧ q = j) ∨ (p = j ∧ q = i)
    · rw [if_pos h]
      apply if_pos
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
    · rw [if_neg h]
      apply if_neg
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h (Or.inr ⟨h2, h1⟩)
      · exact h (Or.inl ⟨h2, h1⟩)

lemma hyper_self {α : Type} [DecidableEq α] (i j : α) : hyper i j i i = 1 := by
  simp [hyper]

lemma hyper_ij {α : Type} [DecidableEq α] {i j : α} (hij : i ≠ j) : hyper i j i j = 1 := by
  simp [hyper, hij]

lemma hyper_row_ne {α : Type} [DecidableEq α] {i j p : α} (hpi : p ≠ i) (hpj : p ≠ j) :
    hyper i j i p = 0 := by
  simp only [hyper]
  rw [if_neg (fun h : i = p => hpi h.symm)]
  rw [if_neg]
  rintro (⟨-, h2⟩ | ⟨-, h2⟩)
  · exact hpj h2
  · exact hpi h2

lemma hyper_entries_Pconstructible {α : Type} [DecidableEq α] (i j : α) :
    ∀ p q, PConstructible (hyper i j p q) := by
  intro p q
  simp only [hyper]
  split_ifs <;> first
    | exact PConstructible.base_one
    | exact zero_Pconstructible
    | exact neg_one_Pconstructible

/-- The explicit inverse of `hyper i j`: the identity except in the two special
coordinates, where it is the block `!![1/2,1/2;1/2,-1/2]`. -/
noncomputable def hyperInv {α : Type} [DecidableEq α] (i j : α) : Matrix α α ℝ :=
  fun p q => if p = q then (if p = i then (1 / 2 : ℝ) else if p = j then -(1 / 2 : ℝ) else 1)
             else (if (p = i ∧ q = j) ∨ (p = j ∧ q = i) then (1 / 2 : ℝ) else 0)

lemma hyper_jj {α : Type} [DecidableEq α] {i j : α} (hij : i ≠ j) :
    hyper i j j j = -1 := by
  simp only [hyper]
  rw [if_pos trivial, if_neg (Ne.symm hij), if_pos trivial]

lemma hyper_ji {α : Type} [DecidableEq α] {i j : α} (hij : i ≠ j) :
    hyper i j j i = 1 := by
  simp only [hyper]
  rw [if_neg (Ne.symm hij), if_pos (Or.inr ⟨trivial, trivial⟩)]

lemma Finset.sum_eq_add_of_support {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (f : ι → ℝ) (h : ∀ p, p ≠ i → p ≠ j → f p = 0) :
    (∑ p, f p) = f i + f j := by
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset ι)) (fun p _ hp => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    exact h p (fun hpi => hp (Or.inl hpi)) (fun hpj => hp (Or.inr hpj)))]
  exact Finset.sum_pair hij

lemma hyper_mul_hyperInv {α : Type} [Fintype α] [DecidableEq α] {i j : α} (hij : i ≠ j) :
    hyper i j * hyperInv i j = 1 := by
  ext p q
  rw [Matrix.mul_apply]
  by_cases hpi : p = i
  · rw [hpi]
    rw [Finset.sum_eq_add_of_support hij
      (fun k => hyper i j i k * hyperInv i j k q)
      (fun k hki hkj => by
        have h0 : hyper i j i k = 0 := by
          simp only [hyper]
          rw [if_neg (Ne.symm hki), if_neg]
          rintro (⟨-, h2⟩ | ⟨h1, -⟩)
          · exact hkj h2
          · exact hij h1
        rw [h0, zero_mul])]
    rw [hyper_self, hyper_ij hij, one_mul, one_mul]
    by_cases hqi : q = i
    · rw [hqi]
      simp [hyperInv, Matrix.one_apply, hij, Ne.symm hij] <;> norm_num
    · by_cases hqj : q = j
      · rw [hqj]
        simp [hyperInv, Matrix.one_apply, hij, Ne.symm hij] <;> norm_num
      · have h1 : hyperInv i j i q = 0 := by
          simp only [hyperInv]
          rw [if_neg (Ne.symm hqi), if_neg]
          rintro (⟨-, h2⟩ | ⟨-, h2⟩)
          · exact hqj h2
          · exact hqi h2
        have h2 : hyperInv i j j q = 0 := by
          simp only [hyperInv]
          rw [if_neg (Ne.symm hqj), if_neg]
          rintro (⟨h1, -⟩ | ⟨-, h2⟩)
          · exact hij h1.symm
          · exact hqi h2
        rw [h1, h2, add_zero, Matrix.one_apply, if_neg (Ne.symm hqi)]
  · by_cases hpj : p = j
    · rw [hpj]
      rw [Finset.sum_eq_add_of_support hij
        (fun k => hyper i j j k * hyperInv i j k q)
        (fun k hki hkj => by
          have h0 : hyper i j j k = 0 := by
            simp only [hyper]
            rw [if_neg (Ne.symm hkj), if_neg]
            rintro (⟨h1, -⟩ | ⟨-, h2⟩)
            · exact hij h1.symm
            · exact hki h2
          rw [h0, zero_mul])]
      rw [hyper_jj hij, hyper_ji hij]
      by_cases hqi : q = i
      · rw [hqi]
        simp [hyperInv, Matrix.one_apply, hij, Ne.symm hij] <;> norm_num
      · by_cases hqj : q = j
        · rw [hqj]
          simp [hyperInv, Matrix.one_apply, hij, Ne.symm hij] <;> norm_num
        · have h1 : hyperInv i j i q = 0 := by
            simp only [hyperInv]
            rw [if_neg (Ne.symm hqi), if_neg]
            rintro (⟨-, h2⟩ | ⟨-, h2⟩)
            · exact hqj h2
            · exact hqi h2
          have h2 : hyperInv i j j q = 0 := by
            simp only [hyperInv]
            rw [if_neg (Ne.symm hqj), if_neg]
            rintro (⟨h1, -⟩ | ⟨-, h2⟩)
            · exact hij h1.symm
            · exact hqi h2
          rw [h1, h2, Matrix.one_apply, if_neg (Ne.symm hqj)]
          ring
    · have hsingle : (∑ k, hyper i j p k * hyperInv i j k q)
          = hyper i j p p * hyperInv i j p q :=
        Finset.sum_eq_single p
          (fun k _ hkp => by
            have h0 : hyper i j p k = 0 := by
              simp only [hyper]
              rw [if_neg (Ne.symm hkp), if_neg]
              rintro (⟨h1, -⟩ | ⟨h2, -⟩)
              · exact hpi h1
              · exact hpj h2
            rw [h0, zero_mul])
          (fun hp => absurd (Finset.mem_univ p) hp)
      rw [hsingle]
      have hpp : hyper i j p p = 1 := by simp [hyper, hpi, hpj]
      rw [hpp, one_mul]
      by_cases hqp : q = p
      · rw [hqp]
        simp [hyperInv, Matrix.one_apply, hpi, hpj] <;> norm_num
      · have h0 : hyperInv i j p q = 0 := by
          simp only [hyperInv]
          rw [if_neg (Ne.symm hqp), if_neg]
          rintro (⟨h1, -⟩ | ⟨h2, -⟩)
          · exact hpi h1
          · exact hpj h2
        rw [h0, Matrix.one_apply, if_neg (Ne.symm hqp)]

lemma hyper_det_ne_zero {α : Type} [Fintype α] [DecidableEq α] {i j : α} (hij : i ≠ j) :
    (hyper i j).det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse (hyper_mul_hyperInv hij)

set_option maxHeartbeats 800000 in
lemma hyper_pivot_apply {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ)
    (hsym : Aᵀ = A) {i j : α} (hij : i ≠ j) (hii : A i i = 0) (hjj : A j j = 0) :
    ((hyper i j)ᵀ * A * (hyper i j)) i i = 2 * A i j := by
  have hji : A j i = A i j := by
    have h := congrFun (congrFun hsym i) j
    simpa using h
  have hcomm : ∀ p q, hyper i j p q = hyper i j q p := by
    intro p q
    have h := congrFun (congrFun (hyper_symm i j) q) p
    simpa [Matrix.transpose_apply] using h
  rw [hyper_symm, Matrix.mul_assoc]
  have expand : (hyper i j * (A * hyper i j)) i i =
      ∑ p, ∑ q, hyper i j i p * (A p q * hyper i j i q) := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [hcomm q i]
  rw [expand]
  set H : α → α → ℝ := fun p q => hyper i j i p * (A p q * hyper i j i q) with hH
  have houter : (∑ p, ∑ q, H p q) = (∑ q, H i q) + (∑ q, H j q) := by
    apply Finset.sum_eq_add_of_support hij
    intro p hpi hpj
    have hp0 : hyper i j i p = 0 := hyper_row_ne hpi hpj
    simp only [hH, hp0, zero_mul, Finset.sum_const_zero]
  rw [houter]
  have hHi : (∑ q, H i q) = H i i + H i j := by
    apply Finset.sum_eq_add_of_support hij
    intro q hqi hqj
    have hq0 : hyper i j i q = 0 := hyper_row_ne hqi hqj
    simp only [hH, hq0, mul_zero]
  have hHj : (∑ q, H j q) = H j i + H j j := by
    apply Finset.sum_eq_add_of_support hij
    intro q hqi hqj
    have hq0 : hyper i j i q = 0 := hyper_row_ne hqi hqj
    simp only [hH, hq0, mul_zero]
  rw [hHi, hHj]
  simp only [hH, hyper_self, hyper_ij hij, hii, hjj, hji]
  ring

/-! ### The main strong induction -/

theorem exists_diag_congruence_fintype_aux :
    ∀ N : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α], Fintype.card α = N →
      ∀ (A : Matrix α α ℝ), Aᵀ = A → (∀ i j, PConstructible (A i j)) →
        ∃ U D : Matrix α α ℝ,
          (∀ i j, PConstructible (U i j)) ∧ (∀ i j, PConstructible (D i j)) ∧
          (∀ i j, i ≠ j → D i j = 0) ∧ Uᵀ * A * U = D ∧ U.det ≠ 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro α _ _ hcard A hsym hA
    have ihA : ∀ (β : Type) [Fintype β] [DecidableEq β],
        Fintype.card β < Fintype.card α →
        ∀ (B : Matrix β β ℝ), Bᵀ = B → (∀ p q, PConstructible (B p q)) →
          ∃ U D : Matrix β β ℝ,
            (∀ p q, PConstructible (U p q)) ∧ (∀ p q, PConstructible (D p q)) ∧
            (∀ p q, p ≠ q → D p q = 0) ∧ Uᵀ * B * U = D ∧ U.det ≠ 0 := by
      intro β _ _ hlt B hBsym hBP
      exact ih (Fintype.card β) (by rw [← hcard]; exact hlt) β rfl B hBsym hBP
    by_cases hA0 : A = 0
    · refine ⟨1, 0, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j; exact one_entries_Pconstructible i j
      · intro i j; exact zero_Pconstructible
      · intro i j hij; simp
      · rw [hA0]; simp
      · rw [Matrix.det_one]; exact one_ne_zero
    · by_cases hdiag : ∃ i, A i i ≠ 0
      · obtain ⟨i, hi⟩ := hdiag
        exact diag_congr_of_pivot A hsym hA i hi ihA
      · push Not at hdiag
        have hne : ∃ p q, A p q ≠ 0 := by
          by_contra h
          push Not at h
          exact hA0 (funext fun p => funext fun q => h p q)
        obtain ⟨p, q, hpq⟩ := hne
        have hpqne : p ≠ q := by
          intro heq
          subst heq
          exact hpq (hdiag p)
        let A' : Matrix α α ℝ := (hyper p q)ᵀ * A * (hyper p q)
        have hA'sym : A'ᵀ = A' := by
          show ((hyper p q)ᵀ * A * (hyper p q))ᵀ = (hyper p q)ᵀ * A * (hyper p q)
          simp only [Matrix.transpose_mul, hyper_symm, hsym, Matrix.mul_assoc]
        have hA'P : ∀ i j, PConstructible (A' i j) := by
          have hH : ∀ i j, PConstructible ((hyper p q) i j) := hyper_entries_Pconstructible p q
          have hHt : ∀ i j, PConstructible (((hyper p q)ᵀ) i j) := by
            intro i j; rw [Matrix.transpose_apply]; exact hH j i
          exact mul_entries_Pconstructible (mul_entries_Pconstructible hHt hA) hH
        have hi' : A' p p ≠ 0 := by
          have h := hyper_pivot_apply A hsym hpqne (hdiag p) (hdiag q)
          rw [show A' p p = 2 * A p q from h]
          exact mul_ne_zero two_ne_zero hpq
        obtain ⟨U', D', hU'P, hD'P, hD'diag, hU'D', hU'det'⟩ :=
          diag_congr_of_pivot A' hA'sym hA'P p hi' ihA
        refine ⟨hyper p q * U', D', ?_, hD'P, hD'diag, ?_, ?_⟩
        · exact mul_entries_Pconstructible (hyper_entries_Pconstructible p q) hU'P
        · have step : (hyper p q * U')ᵀ * A * (hyper p q * U') =
              U'ᵀ * ((hyper p q)ᵀ * A * hyper p q) * U' := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
          rw [step]
          exact hU'D'
        · rw [Matrix.det_mul]
          exact mul_ne_zero (hyper_det_ne_zero hpqne) hU'det'

theorem exists_diag_congruence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsym : Aᵀ = A) (hA : ∀ i j, PConstructible (A i j)) :
    ∃ U D : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, PConstructible (U i j)) ∧ (∀ i j, PConstructible (D i j)) ∧
      (∀ i j, i ≠ j → D i j = 0) ∧ Uᵀ * A * U = D ∧ U.det ≠ 0 :=
  exists_diag_congruence_fintype_aux n (Fin n) (Fintype.card_fin n) A hsym hA

/-! ### Totally isotropic vectors of a diagonal form of signature `(≥2, ≥2)` -/

-- Theorem: a diagonal form `Q y = ∑ λ i * y i ^ 2` with at least two positive and two
-- negative coefficients has two P-constructible, independent, totally isotropic vectors:
-- each has `Q = 0`, and their polar pairing vanishes.
theorem exists_diagonal_isotropic_vectors {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, PConstructible (lam i)) (_hn : 2 ≤ n)
    (hpos : ∃ i j : Fin n, i ≠ j ∧ 0 < lam i ∧ 0 < lam j)
    (hneg : ∃ i j : Fin n, i ≠ j ∧ lam i < 0 ∧ lam j < 0) :
    ∃ v w : Fin n → ℝ,
      (∀ i, PConstructible (v i)) ∧ (∀ i, PConstructible (w i)) ∧
      v ≠ 0 ∧ w ≠ 0 ∧
      (∑ i, lam i * v i ^ 2 = 0) ∧ (∑ i, lam i * w i ^ 2 = 0) ∧
      (∑ i, lam i * v i * w i = 0) ∧ (¬ ∃ c : ℝ, w = c • v) := by
  obtain ⟨p1, p2, hp12, hp1, hp2⟩ := hpos
  obtain ⟨n1, n2, hn12, hn1, hn2⟩ := hneg
  have hpn1 : p1 ≠ n1 := fun h => by rw [h] at hp1; linarith
  have hpn2 : p1 ≠ n2 := fun h => by rw [h] at hp1; linarith
  have hp2n1 : p2 ≠ n1 := fun h => by rw [h] at hp2; linarith
  have hp2n2 : p2 ≠ n2 := fun h => by rw [h] at hp2; linarith
  let v : Fin n → ℝ := fun i =>
    if i = p1 then Real.sqrt (-(lam n1) / lam p1) else if i = n1 then 1 else 0
  let w : Fin n → ℝ := fun i =>
    if i = p2 then Real.sqrt (-(lam n2) / lam p2) else if i = n2 then 1 else 0
  have hv_p1 : v p1 = Real.sqrt (-(lam n1) / lam p1) := by simp [v]
  have hv_n1 : v n1 = 1 := by
    simp [v, Ne.symm hpn1]
  have hv_zero : ∀ i, i ≠ p1 → i ≠ n1 → v i = 0 := by
    intro i h1 h2; simp only [v]; rw [if_neg h1, if_neg h2]
  have hw_p2 : w p2 = Real.sqrt (-(lam n2) / lam p2) := by simp [w]
  have hw_n2 : w n2 = 1 := by
    simp [w, Ne.symm hp2n2]
  have hw_zero : ∀ i, i ≠ p2 → i ≠ n2 → w i = 0 := by
    intro i h1 h2; simp only [w]; rw [if_neg h1, if_neg h2]
  have hvP : ∀ i, PConstructible (v i) := by
    intro i
    by_cases h1 : i = p1
    · rw [h1, hv_p1]
      exact sqrt_Pconstructible (PConstructible.div (neg_Pconstructible (hlam n1)) (hlam p1))
    · by_cases h2 : i = n1
      · rw [h2, hv_n1]; exact PConstructible.base_one
      · rw [hv_zero i h1 h2]; exact zero_Pconstructible
  have hwP : ∀ i, PConstructible (w i) := by
    intro i
    by_cases h1 : i = p2
    · rw [h1, hw_p2]
      exact sqrt_Pconstructible (PConstructible.div (neg_Pconstructible (hlam n2)) (hlam p2))
    · by_cases h2 : i = n2
      · rw [h2, hw_n2]; exact PConstructible.base_one
      · rw [hw_zero i h1 h2]; exact zero_Pconstructible
  have hsumv : (∑ i, lam i * v i ^ 2) = 0 := by
    rw [Finset.sum_eq_add_of_support hpn1 (fun i => lam i * v i ^ 2)
      (fun i h1 h2 => by rw [hv_zero i h1 h2]; ring)]
    rw [hv_p1, hv_n1, Real.sq_sqrt (le_of_lt (div_pos (neg_pos.mpr hn1) hp1))]
    have hp1ne : lam p1 ≠ 0 := ne_of_gt hp1
    field_simp
    ring
  have hsumw : (∑ i, lam i * w i ^ 2) = 0 := by
    rw [Finset.sum_eq_add_of_support hp2n2 (fun i => lam i * w i ^ 2)
      (fun i h1 h2 => by rw [hw_zero i h1 h2]; ring)]
    rw [hw_p2, hw_n2, Real.sq_sqrt (le_of_lt (div_pos (neg_pos.mpr hn2) hp2))]
    have hp2ne : lam p2 ≠ 0 := ne_of_gt hp2
    field_simp
    ring
  have hsumvw : (∑ i, lam i * v i * w i) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases h1 : i = p1
    · rw [h1]
      have hwp1 : w p1 = 0 := by
        simp only [w]; rw [if_neg hp12, if_neg hpn2]
      rw [hwp1]; ring
    · by_cases h2 : i = n1
      · rw [h2]
        have hwn1 : w n1 = 0 := by
          simp only [w]; rw [if_neg (Ne.symm hp2n1), if_neg hn12]
        rw [hwn1]; ring
      · rw [hv_zero i h1 h2]; ring
  have hindep : ¬ ∃ c : ℝ, w = c • v := by
    rintro ⟨c, hc⟩
    have h2 := congrFun hc p2
    have hw2 : w p2 ≠ 0 := by
      rw [hw_p2]
      exact ne_of_gt ((Real.sqrt_pos).mpr (div_pos (neg_pos.mpr hn2) hp2))
    have hv2 : v p2 = 0 := hv_zero p2 (Ne.symm hp12) hp2n1
    rw [Pi.smul_apply, smul_eq_mul, hv2, mul_zero] at h2
    exact hw2 h2
  have hvne : v ≠ 0 := by
    intro h0
    have h1 := congrFun h0 n1
    rw [hv_n1] at h1
    exact one_ne_zero h1
  have hwne : w ≠ 0 := by
    intro h0
    have h1 := congrFun h0 n2
    rw [hw_n2] at h1
    exact one_ne_zero h1
  exact ⟨v, w, hvP, hwP, hvne, hwne, hsumv, hsumw, hsumvw, hindep⟩

end Pconstructible
