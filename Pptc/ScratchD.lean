import Pptc.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

open Polynomial Matrix

namespace Pconstructible

/-! ### D1: characteristic-polynomial coefficients are P-constructible -/

theorem det_Pconstructible {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : ∀ i j, PConstructible (M i j)) :
    PConstructible M.det := by
  rw [Matrix.det_apply']
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun σ _ => ?_)
  have hprod : PConstructible (∏ i : n, M (σ i) i) :=
    Finset.prod_induction (fun i => M (σ i) i) PConstructible
      (fun _ _ ha hb => PConstructible.mul ha hb) PConstructible.base_one
      (fun i _ => hM (σ i) i)
  exact PConstructible.mul (int_Pconstructible ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) hprod

theorem charpoly_coeff_Pconstructible {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : ∀ i j, PConstructible (M i j)) (k : ℕ) :
    PConstructible (M.charpoly.coeff k) := by
  by_cases hk : k ≤ Fintype.card n
  · have hsub : Fintype.card n - (Fintype.card n - k) = k := Nat.sub_sub_self hk
    rw [← hsub]
    rw [Matrix.charpoly_coeff_eq_sum_minors M (Fintype.card n - k) (Nat.sub_le _ _)]
    refine PConstructible.mul (pow_Pconstructible neg_one_Pconstructible _) ?_
    refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
      zero_Pconstructible (fun s _ => ?_)
    exact det_Pconstructible (M.submatrix (Subtype.val) (Subtype.val))
      (fun i j => hM _ _)
  · push Not at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · exact zero_Pconstructible
    · rw [Matrix.charpoly_natDegree_eq_dim]
      exact hk

/-! ### D2: the companion matrix of a degree-7 polynomial -/

/-- The companion matrix of `q`, whose last row is `-q.coeff 0, …, -q.coeff 6` and whose
superdiagonal is `1`. For monic `q` of degree `7` its characteristic polynomial is `q`,
and `(1, β, …, β⁶)` is an eigenvector with eigenvalue any root `β` of `q`. -/
def companion7 (q : ℝ[X]) : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => if i.val = 6 then -q.coeff j.val
             else if j.val = i.val + 1 then 1 else 0

/-- The vector `(1, β, β², …, β⁶)`. -/
def companionVec (β : ℝ) : Fin 7 → ℝ := fun k => β ^ k.val

theorem companion7_apply (q : ℝ[X]) (i j : Fin 7) :
    companion7 q i j = if i.val = 6 then -q.coeff j.val
      else if j.val = i.val + 1 then 1 else 0 := rfl

theorem companion7_entries_Pconstructible {q : ℝ[X]}
    (hq : ∀ k, PConstructible (q.coeff k)) (i j : Fin 7) :
    PConstructible (companion7 q i j) := by
  rw [companion7_apply]
  by_cases hi : i.val = 6
  · simp only [hi, ↓reduceIte]
    exact neg_Pconstructible (hq j.val)
  · simp only [hi, ↓reduceIte]
    by_cases hj : j.val = i.val + 1
    · simp only [hj, ↓reduceIte]
      exact PConstructible.base_one
    · simp only [hj, ↓reduceIte]
      exact zero_Pconstructible

theorem companion7_mulVec_apply_of_lt (q : ℝ[X]) (w : Fin 7 → ℝ)
    {i : Fin 7} (hi : i.val < 6) :
    (companion7 q *ᵥ w) i = w ⟨i.val + 1, by omega⟩ := by
  have hi6 : i.val ≠ 6 := by omega
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single ⟨i.val + 1, by omega⟩]
  · simp [companion7, hi6]
  · intro j _ hne
    have hne' : j.val ≠ i.val + 1 := by
      intro hh; exact hne (Fin.ext (by simpa using hh))
    simp [companion7, hi6, hne']
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

theorem companion7_mulVec_apply_last (q : ℝ[X]) (w : Fin 7 → ℝ) :
    (companion7 q *ᵥ w) ⟨6, by norm_num⟩ = -∑ j : Fin 7, q.coeff j.val * w j := by
  rw [Matrix.mulVec, dotProduct]
  simp only [companion7, ↓reduceIte]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]

theorem companion7_mulVec_companionVec {q : ℝ[X]} {β : ℝ}
    (hβ : q.eval β = 0) (h7 : q.coeff 7 = 1) (hdeg : q.natDegree ≤ 7) :
    companion7 q *ᵥ companionVec β = β • companionVec β := by
  have hsum : (∑ k ∈ Finset.range 7, q.coeff k * β ^ k) = -β ^ 7 := by
    have h := hβ
    rw [Polynomial.eval_eq_sum_range' (p := q) (n := 8) (by omega)] at h
    rw [Finset.sum_range_succ, h7, one_mul] at h
    linarith
  funext i
  by_cases hi : i.val = 6
  · have hι : i = ⟨6, by norm_num⟩ := Fin.ext (by simpa using hi)
    subst hι
    rw [companion7_mulVec_apply_last]
    simp only [companionVec]
    rw [Fin.sum_univ_eq_sum_range (fun k => q.coeff k * β ^ k) 7, hsum, neg_neg]
    simp only [Pi.smul_apply, companionVec, smul_eq_mul]
    rw [pow_succ']
  · have hlt : i.val < 6 := by have := i.isLt; omega
    rw [companion7_mulVec_apply_of_lt q (companionVec β) hlt]
    simp only [Pi.smul_apply, companionVec, smul_eq_mul]
    rw [pow_succ']

/-! ### D3: `φ β` is a root of `charpoly (φ (companion q))` -/

theorem pow_mulVec_eigenvector {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) {β : ℝ} {v : n → ℝ} (hv : M *ᵥ v = β • v) :
    ∀ k : ℕ, (M ^ k) *ᵥ v = (β ^ k) • v
  | 0 => by rw [pow_zero, Matrix.one_mulVec, pow_zero, one_smul]
  | k + 1 => by
      rw [pow_succ, ← Matrix.mulVec_mulVec v (M ^ k) M, hv, Matrix.mulVec_smul,
        pow_mulVec_eigenvector M hv k, smul_smul, pow_succ']

theorem aeval_mulVec_eigenvector {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) {β : ℝ} {v : n → ℝ} (hv : M *ᵥ v = β • v) (p : ℝ[X]) :
    (aeval M p) *ᵥ v = (p.eval β) • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_mulVec, pow_mulVec_eigenvector M hv n,
        Polynomial.eval_monomial, smul_smul]

theorem companion7_charpoly_aeval_isRoot {q φ : ℝ[X]} {β : ℝ}
    (hβ : q.eval β = 0) (h7 : q.coeff 7 = 1) (hdeg : q.natDegree ≤ 7) :
    ((aeval (companion7 q) φ).charpoly).eval (φ.eval β) = 0 := by
  set M := companion7 q with hM
  set v : Fin 7 → ℝ := companionVec β with hv
  have hMv : M *ᵥ v = β • v := companion7_mulVec_companionVec hβ h7 hdeg
  have hvne : v ≠ 0 := by
    intro h0
    have h1 := congrFun h0 0
    simp [hv, companionVec] at h1
  have hNv : (aeval M φ) *ᵥ v = (φ.eval β) • v := aeval_mulVec_eigenvector M hMv φ
  have hzero : (Matrix.scalar (Fin 7) (φ.eval β) - aeval M φ) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hNv, Matrix.scalar_apply, Matrix.diagonal_const_mulVec, sub_self]
  rw [Matrix.eval_charpoly]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, hzero⟩

/-! ### D4: the resolvent's low coefficients give the power-law relation -/

theorem matrix_mul_entries_Pconstructible {n : Type*} [Fintype n]
    {A B : Matrix n n ℝ} (hA : ∀ i j, PConstructible (A i j))
    (hB : ∀ i j, PConstructible (B i j)) (i j : n) :
    PConstructible ((A * B) i j) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun k _ => ?_)
  exact PConstructible.mul (hA i k) (hB k j)

theorem matrix_pow_entries_Pconstructible {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : ∀ i j, PConstructible (A i j)) :
    ∀ k (i j : n), PConstructible ((A ^ k) i j) := by
  intro k
  induction k with
  | zero =>
      intro i j
      rw [pow_zero, Matrix.one_apply]
      by_cases h : i = j <;> simp [h, zero_Pconstructible, PConstructible.base_one]
  | succ k ih =>
      intro i j
      rw [pow_succ]
      exact matrix_mul_entries_Pconstructible ih hA i j

theorem matrix_sum_apply {ι : Type*} {n : Type*} [Fintype n] [DecidableEq n]
    (s : Finset ι) (f : ι → Matrix n n ℝ) (i j : n) :
    (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_apply, ih]

theorem aeval_entries_Pconstructible {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : ∀ i j, PConstructible (M i j))
    (φ : ℝ[X]) (hφ : ∀ k, PConstructible (φ.coeff k)) (i j : n) :
    PConstructible ((aeval M φ) i j) := by
  rw [Polynomial.aeval_eq_sum_range, matrix_sum_apply]
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun k _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul]
  exact PConstructible.mul (hφ k) (matrix_pow_entries_Pconstructible hM k i j)

-- Theorem: if `q` is monic of degree `7` with P-constructible coefficients, `φ` has
-- P-constructible coefficients, and the resolvent `charpoly (φ (companion q))` has its
-- `X ^ 6`, `X ^ 5`, `X ^ 4` coefficients zero, then `y = φ β` satisfies a power-law
-- equation `y ^ 7 = cubicVal c₀ c₁ c₂ c₃ y` with P-constructible `cᵢ`.
theorem resolvent_powerLaw {q φ : ℝ[X]} {β : ℝ}
    (hq : ∀ k, PConstructible (q.coeff k)) (hβ : q.eval β = 0) (h7 : q.coeff 7 = 1)
    (hdeg : q.natDegree ≤ 7) (hφ : ∀ k, PConstructible (φ.coeff k))
    (hkill : (aeval (companion7 q) φ).charpoly.coeff 6 = 0 ∧
             (aeval (companion7 q) φ).charpoly.coeff 5 = 0 ∧
             (aeval (companion7 q) φ).charpoly.coeff 4 = 0) :
    ∃ c₀ c₁ c₂ c₃ : ℝ, PConstructible c₀ ∧ PConstructible c₁ ∧ PConstructible c₂ ∧
      PConstructible c₃ ∧ (φ.eval β) ^ 7 = cubicVal c₀ c₁ c₂ c₃ (φ.eval β) := by
  set N : Matrix (Fin 7) (Fin 7) ℝ := aeval (companion7 q) φ with hN
  set R : ℝ[X] := N.charpoly with hR
  have hNc : ∀ i j, PConstructible (N i j) := fun i j =>
    aeval_entries_Pconstructible _ (companion7_entries_Pconstructible hq) φ hφ i j
  have hRc : ∀ k, PConstructible (R.coeff k) := fun k =>
    charpoly_coeff_Pconstructible N hNc k
  have hk6 : R.coeff 6 = 0 := by rw [hR, hN]; exact hkill.1
  have hk5 : R.coeff 5 = 0 := by rw [hR, hN]; exact hkill.2.1
  have hk4 : R.coeff 4 = 0 := by rw [hR, hN]; exact hkill.2.2
  have hnat : R.natDegree = 7 := by rw [hR]; exact Matrix.charpoly_natDegree_eq_dim N
  have hmonic : R.Monic := by rw [hR]; exact Matrix.charpoly_monic N
  have hc7 : R.coeff 7 = 1 := by rw [← hnat]; exact hmonic.coeff_natDegree
  have hroot : R.eval (φ.eval β) = 0 := by
    rw [hR, hN]
    exact companion7_charpoly_aeval_isRoot hβ h7 hdeg
  have heval : R.eval (φ.eval β) =
      (φ.eval β) ^ 7 + R.coeff 3 * (φ.eval β) ^ 3 + R.coeff 2 * (φ.eval β) ^ 2
        + R.coeff 1 * (φ.eval β) + R.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range' (p := R) (n := 8) (by rw [hnat]; norm_num)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hk6, hk5, hk4, hc7]
    ring
  have h0 : (φ.eval β) ^ 7 + R.coeff 3 * (φ.eval β) ^ 3 + R.coeff 2 * (φ.eval β) ^ 2
      + R.coeff 1 * (φ.eval β) + R.coeff 0 = 0 := by rw [← heval]; exact hroot
  refine ⟨-R.coeff 0, -R.coeff 1, -R.coeff 2, -R.coeff 3,
    neg_Pconstructible (hRc 0), neg_Pconstructible (hRc 1), neg_Pconstructible (hRc 2),
    neg_Pconstructible (hRc 3), ?_⟩
  rw [cubicVal]
  linarith [h0]

end Pconstructible
