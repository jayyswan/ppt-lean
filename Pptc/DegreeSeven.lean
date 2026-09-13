import Pptc.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fintype
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.IntermediateValue

/-! # Pptc.DegreeSeven — the degree-7 theorem of issue #6

This file is self-contained: it imports `Pptc.Basic` and Mathlib only, and proves that
every real root of a degree-`7` polynomial with P-constructible coefficients that has at
least one non-real root is P-constructible (`root_Pconstructible_of_nonreal_root`).

The proof splits on the number of non-real conjugate pairs:

* `root_Pconstructible_of_nonSeparable` handles the non-separable case;
* `root_Pconstructible_of_two_conjugate_pairs_monic` handles `s ≥ 2` (the classical
  Bring–Jerrard step) through `exists_tschirnhaus_traces`, the killing of the top three
  resolvent coefficients, and the power-law engine;
* `root_Pconstructible_of_one_conjugate_pair` handles `s = 1`: a P-constructible point
  `P₀` on the light cone, the conjugation sign certificate `exists_sign_change`, rational
  witnesses by density, the sextic along the stereographic line, and the same tail.

The declarations below were inlined, in dependency order, from the modules that used to
carry this development (`ScratchD/F/G/H/N/E/K/C/C2/AB/S/Sep`, `DegreeSevenOnePair`,
`S1Roots`, `S1Cert`, `S1Iso`, `S1Sign`, `S1Sextic`, `S1Final`).
-/


open Polynomial Matrix


/- ==================== inlined from Pptc.ScratchD ==================== -/


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


/- ==================== inlined from Pptc.ScratchF ==================== -/


open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-- The standard basis vector `eₖ`. -/
def e7 (k : Fin 7) : Fin 7 → ℝ := Pi.single k 1

@[simp] theorem e7_apply_self (k : Fin 7) : e7 k k = 1 := Pi.single_eq_same k 1

theorem e7_apply_ne {i k : Fin 7} (h : i ≠ k) : e7 k i = 0 := Pi.single_eq_of_ne h 1

end

end Pconstructible


/- ==================== inlined from Pptc.ScratchG ==================== -/


open Polynomial Matrix Module

namespace Pconstructible

noncomputable section

/-! ### A generic companion matrix and its eigenvectors

`ScratchD` defines the companion matrix over `ℝ`.  For the spectral identity we need it
over an arbitrary field (eventually `ℂ`), so we restate it generically and prove that the
vectors `z ↦ (1, z, …, z⁶)` are eigenvectors. -/

/-- The companion matrix of `q`, over an arbitrary commutative ring. -/
def companion7' {R : Type*} [CommRing R] (q : R[X]) : Matrix (Fin 7) (Fin 7) R :=
  fun i j => if i.val = 6 then -q.coeff j.val else if j.val = i.val + 1 then 1 else 0

theorem companion7'_apply {R : Type*} [CommRing R] (q : R[X]) (i j : Fin 7) :
    companion7' q i j = if i.val = 6 then -q.coeff j.val
      else if j.val = i.val + 1 then 1 else 0 := rfl

/-- Mapping the real companion matrix is the generic companion of the mapped polynomial. -/
theorem companion7_map_eq {S : Type*} [CommRing S] (f : ℝ →+* S) (q : ℝ[X]) :
    (companion7 q).map f = companion7' (q.map f) := by
  ext i j
  simp only [Matrix.map_apply, companion7'_apply, companion7]
  by_cases h : i.val = 6 <;> simp [h]

/-- The vector `(1, z, …, z⁶)`. -/
def companionVecC {K : Type*} [Monoid K] (z : K) : Fin 7 → K := fun k => z ^ k.val

theorem companion7'_mulVec_apply_of_lt {K : Type*} [CommRing K] (q : K[X]) (w : Fin 7 → K)
    {i : Fin 7} (hi : i.val < 6) :
    (companion7' q *ᵥ w) i = w ⟨i.val + 1, by omega⟩ := by
  have hi6 : i.val ≠ 6 := by omega
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single ⟨i.val + 1, by omega⟩]
  · simp [companion7', hi6]
  · intro j _ hne
    have hne' : j.val ≠ i.val + 1 := fun hh => hne (Fin.ext (by simpa using hh))
    simp [companion7', hi6, hne']
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

theorem companion7'_mulVec_apply_last {K : Type*} [CommRing K] (q : K[X]) (w : Fin 7 → K) :
    (companion7' q *ᵥ w) ⟨6, by norm_num⟩ = -∑ j : Fin 7, q.coeff j.val * w j := by
  rw [Matrix.mulVec, dotProduct]
  simp only [companion7', ↓reduceIte]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]

theorem companion7'_mulVec_companionVecC {K : Type*} [Field K] {q : K[X]} {z : K}
    (hz : q.eval z = 0) (h7 : q.coeff 7 = 1) (hdeg : q.natDegree ≤ 7) :
    companion7' q *ᵥ companionVecC z = z • companionVecC z := by
  have hsum : (∑ k ∈ Finset.range 7, q.coeff k * z ^ k) = -z ^ 7 := by
    have h := hz
    rw [Polynomial.eval_eq_sum_range' (p := q) (n := 8) (by omega)] at h
    rw [Finset.sum_range_succ, h7, one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  funext i
  by_cases hi : i.val = 6
  · have hι : i = ⟨6, by norm_num⟩ := Fin.ext (by simpa using hi)
    subst hι
    rw [companion7'_mulVec_apply_last]
    simp only [companionVecC]
    rw [Fin.sum_univ_eq_sum_range (fun k => q.coeff k * z ^ k) 7, hsum, neg_neg]
    simp only [Pi.smul_apply, companionVecC, smul_eq_mul]
    rw [pow_succ']
  · have hlt : i.val < 6 := by have := i.isLt; omega
    rw [companion7'_mulVec_apply_of_lt q (companionVecC z) hlt]
    simp only [Pi.smul_apply, companionVecC, smul_eq_mul]
    rw [pow_succ']

/-- In a basis of eigenvectors, the trace of a power is the sum of the eigenvalues' powers. -/
theorem trace_pow_eq_sum_eigen {K ι V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (F : Module.End K V) (b : Basis ι K V) (z : ι → K)
    (hv : ∀ i, F (b i) = z i • b i) (k : ℕ) :
    (F ^ k).trace K V = ∑ i, z i ^ k := by
  rw [LinearMap.trace_eq_matrix_trace K b]
  simp only [Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  have hpow : (F ^ k) (b i) = z i ^ k • b i := by
    induction k with
    | zero => rw [pow_zero, Module.End.one_apply, pow_zero, one_smul]
    | succ k ih => rw [pow_succ, Module.End.mul_apply, hv i, map_smul, ih, smul_smul, pow_succ,
        mul_comm]
  rw [hpow, map_smul, Basis.repr_self]
  simp

-- Theorem: trace of a power of the degree-7 companion matrix is the sum of the `k`-th powers
-- of the roots of `q` (with multiplicity).
set_option linter.style.haveILetI false in
theorem companion7'_trace_pow {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : K[X]) (hmon : q.Monic) (hnat : q.natDegree = 7) (hsep : q.Separable) (k : ℕ) :
    Matrix.trace ((companion7' q) ^ k) = (q.roots.map (fun z => z ^ k)).sum := by
  classical
  set M : Matrix (Fin 7) (Fin 7) K := companion7' q with hM
  have h7 : q.coeff 7 = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ 7 := le_of_eq hnat
  have hnodup : q.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard : q.roots.card = 7 := by
    rw [← hnat]; exact (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  let idx := q.roots.toFinset
  haveI : Nonempty idx := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
      show 0 < q.roots.toFinset.card
      rw [Multiset.toFinset_card_of_nodup hnodup, hcard]; norm_num)
    exact ⟨⟨x, hx⟩⟩
  let v : idx → (Fin 7 → K) := fun z => companionVecC (z : K)
  have hv : ∀ z : idx, M *ᵥ v z = (z : K) • v z := by
    intro z
    have hz : q.eval (z : K) = 0 :=
      (Polynomial.mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp z.2)
    exact companion7'_mulVec_companionVecC hz h7 hdeg
  have hvne : ∀ z : idx, v z ≠ 0 := by
    intro z h0
    have h1 := congrFun h0 0
    simp [v, companionVecC] at h1
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' M.toLin' (fun z : idx => (z : K))
      Subtype.coe_injective v (fun z =>
        ⟨(Module.End.mem_eigenspace_iff).mpr (by rw [Matrix.toLin'_apply]; exact hv z), hvne z⟩)
  have hcardfin : Fintype.card idx = Module.finrank K (Fin 7 → K) := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcard]
    norm_num
  let b : Basis idx K (Fin 7 → K) := basisOfLinearIndependentOfCardEqFinrank hli hcardfin
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have htrace := trace_pow_eq_sum_eigen (Matrix.toLin' M) b (fun z : idx => (z : K))
    (fun z => by rw [hb]; exact hv z) k
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow, htrace, Finset.sum_coe_sort idx
    (fun z : K => z ^ k)]
  have hval : idx.val = q.roots := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  rw [show (∑ i ∈ idx, i ^ k) = (idx.val.map (fun z => z ^ k)).sum from rfl, hval]

-- Theorem: the trace of any polynomial in the companion matrix is the sum over the roots of
-- the polynomial evaluated there.
theorem companion7'_trace_aeval {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q φ : K[X]) (hmon : q.Monic) (hnat : q.natDegree = 7) (hsep : q.Separable) :
    Matrix.trace (aeval (companion7' q) φ) = (q.roots.map φ.eval).sum := by
  induction φ using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [map_add, Matrix.trace_add, hp, hr]
      rw [show (q.roots.map (fun z => (p + r).eval z))
            = q.roots.map (fun z => p.eval z + r.eval z) from
          Multiset.map_congr rfl (fun z _ => by rw [Polynomial.eval_add])]
      rw [Multiset.sum_map_add]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
        Matrix.one_mul, Matrix.trace_smul, smul_eq_mul,
        companion7'_trace_pow q hmon hnat hsep n]
      rw [show (q.roots.map (fun x => eval x ((monomial n) a)))
            = q.roots.map (fun z => a * z ^ n) from
          Multiset.map_congr rfl (fun z _ => by rw [Polynomial.eval_monomial])]
      rw [Multiset.sum_map_mul_left]

-- Theorem: the spectral identity over `ℝ`, expressed through the complex roots.
theorem companion7_trace_aeval (q φ : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companion7 q) φ))
      = ((q.map (algebraMap ℝ ℂ)).roots.map
          (fun z => (φ.map (algebraMap ℝ ℂ)).eval z)).sum := by
  have hmon' : (q.map (algebraMap ℝ ℂ)).Monic := hmon.map (algebraMap ℝ ℂ)
  have hnat' : (q.map (algebraMap ℝ ℂ)).natDegree = 7 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]; exact hnat
  have hsep' : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  have hmap : (aeval (companion7 q) φ).map (algebraMap ℝ ℂ)
      = aeval (companion7' (q.map (algebraMap ℝ ℂ))) (φ.map (algebraMap ℝ ℂ)) := by
    rw [show (aeval (companion7 q) φ).map (algebraMap ℝ ℂ)
          = RingHom.mapMatrix (algebraMap ℝ ℂ) (aeval (companion7 q) φ) from
        (RingHom.mapMatrix_apply _ _).symm,
      Polynomial.map_aeval_eq_aeval_map (R := ℝ) (S := Matrix (Fin 7) (Fin 7) ℝ)
        (T := ℂ) (U := Matrix (Fin 7) (Fin 7) ℂ) (φ := algebraMap ℝ ℂ)
        (ψ := RingHom.mapMatrix (algebraMap ℝ ℂ))
        (by ext r i j; by_cases h : i = j <;>
          simp [RingHom.mapMatrix_apply, Matrix.algebraMap_matrix_apply, h])
        φ (companion7 q),
      RingHom.mapMatrix_apply, companion7_map_eq]
  rw [AddMonoidHom.map_trace (algebraMap ℝ ℂ) (aeval (companion7 q) φ), hmap]
  exact companion7'_trace_aeval (q.map (algebraMap ℝ ℂ)) (φ.map (algebraMap ℝ ℂ))
    hmon' hnat' hsep'

-- Theorem: for a non-real complex number `z`, every complex value `c` is `h(z)` for a real
-- polynomial `h` of degree at most one.  Writing `h = a + b X`, the system `a + b z = c` has
-- the real solution `b = Im c / Im z`, `a = Re c - Re z * b`.
theorem exists_linear_eval (z c : ℂ) (hz : z.im ≠ 0) :
    ∃ h : ℝ[X], h.natDegree ≤ 1 ∧ (h.map (algebraMap ℝ ℂ)).eval z = c := by
  refine ⟨C (c.re - z.re * (c.im / z.im)) + C (c.im / z.im) * X, ?_, ?_⟩
  · compute_degree!
  · rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.coe_algebraMap, Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.coe_algebraMap, Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      ring

/-- The real quadratic polynomial with complex roots `z` and `conj z`. -/
def conjQuad (z : ℂ) : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (z.re ^ 2 + z.im ^ 2)

theorem conjQuad_monic (z : ℂ) : (conjQuad z).Monic := by
  rw [conjQuad]; monicity!

theorem conjQuad_natDegree (z : ℂ) : (conjQuad z).natDegree = 2 := by
  rw [conjQuad]; compute_degree!

theorem conjQuad_eval_map (z : ℂ) : ((conjQuad z).map (algebraMap ℝ ℂ)).eval z = 0 := by
  rw [conjQuad]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, pow_two]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.coe_algebraMap,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, mul_zero, add_zero,
      Complex.zero_re, Complex.zero_im]
    ring
  · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.coe_algebraMap,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, mul_zero, add_zero,
      Complex.zero_re, Complex.zero_im]
    ring

-- Theorem: a real polynomial `q` with a non-real complex root `z` is divisible by the real
-- quadratic `conjQuad z`.  Reduce `q` modulo `conjQuad z`: the remainder has degree `< 2`,
-- and evaluating the congruence at `z` kills it, so the remainder is `a + b X` with `a + b z
-- = 0`; taking imaginary parts gives `b = 0` and then `a = 0`.
theorem conjQuad_dvd_of_root {q : ℝ[X]} {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) : conjQuad z ∣ q := by
  set r : ℝ[X] := q %ₘ conjQuad z with hr
  have hr0 : r = 0 := by
    have hmod := Polynomial.modByMonic_add_div q (conjQuad z)
    have h1 := congrArg (fun P : ℂ[X] => P.eval z)
      (congrArg (Polynomial.map (algebraMap ℝ ℂ)) hmod)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add, Polynomial.eval_mul]
      at h1
    rw [← hr, conjQuad_eval_map z, zero_mul, add_zero, hz] at h1
    -- h1 : (r.map _).eval z = 0
    have hdeg : r.natDegree < 2 := by
      rcases eq_or_ne r 0 with h | h
      · rw [h]; norm_num
      · refine (Polynomial.natDegree_lt_iff_degree_lt h).mpr ?_
        have hq := Polynomial.degree_modByMonic_lt q (conjQuad_monic z)
        have hdp : (conjQuad z).degree = (2 : WithBot ℕ) := by
          rw [Polynomial.degree_eq_natDegree (conjQuad_monic z).ne_zero, conjQuad_natDegree]
          norm_num
        rwa [hdp, ← hr] at hq
    have hexp : r = C (r.coeff 0) + C (r.coeff 1) * X := by
      ext n
      rcases lt_or_ge n 2 with hn | hn
      · interval_cases n <;>
          simp [Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_C_mul_X]
      · have h0 : r.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have h1' : (C (r.coeff 0) + C (r.coeff 1) * X : ℝ[X]).coeff n = 0 := by
          rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
            if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ n = 1), add_zero]
        rw [h0, h1']
    rw [hexp] at h1
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h1
    have h2 : (r.coeff 1 : ℂ) * z + (r.coeff 0 : ℂ) = 0 := by
      rw [add_comm] at h1; exact h1
    have hb : r.coeff 1 = 0 := by
      have := congrArg Complex.im h2
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_re, Complex.zero_im] at this
      have h3 : (r.coeff 1 : ℂ).re * z.im = 0 := by simpa using this
      simpa [Complex.ofReal_re] using (mul_eq_zero.mp h3).resolve_right hzim
    have ha : r.coeff 0 = 0 := by
      have := congrArg Complex.re h2
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, Complex.zero_re] at this
      rw [hb] at this
      simpa using this
    ext n
    rcases lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact ha
      · exact hb
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : r.natDegree < n)]
      rfl
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd (conjQuad_monic z), ← hr]
  exact hr0

end

end Pconstructible


/- ==================== inlined from Pptc.ScratchH ==================== -/


open Polynomial Matrix Module

namespace Pconstructible

noncomputable section

/-! ### The conjugate quadratic over `ℂ`

`conjQuad z` is the real quadratic with complex roots `z` and `z̄`.  Over `ℂ` it factors
as `(X - z) * (X - z̄)`, so it can be used to separate the conjugate pair `{z, z̄}` from
the other roots of a real polynomial. -/

-- Theorem: mapping the conjugate quadratic to `ℂ` factors it as `(X - z) * (X - z̄)`.
theorem conjQuad_map_eq_prod (z : ℂ) :
    (conjQuad z).map (algebraMap ℝ ℂ) = (X - C z) * (X - C (starRingEnd ℂ z)) := by
  have h1 : (algebraMap ℝ ℂ) (2 * z.re) = z + starRingEnd ℂ z :=
    (Complex.add_conj z).symm
  have h2 : (algebraMap ℝ ℂ) (z.re ^ 2 + z.im ^ 2) = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_apply, Complex.coe_algebraMap, Complex.ofReal_inj]
    ring
  rw [conjQuad]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  rw [h1, h2]
  simp only [Polynomial.C_add, Polynomial.C_mul]
  ring

-- Theorem: evaluation of a mapped real polynomial commutes with complex conjugation.
theorem eval_map_conj (f : ℝ[X]) (z : ℂ) :
    (f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)
      = starRingEnd ℂ ((f.map (algebraMap ℝ ℂ)).eval z) := by
  induction f using Polynomial.induction_on' with
  | add p r hp hr =>
      simp only [Polynomial.map_add, Polynomial.eval_add, map_add, hp, hr]
  | monomial n a =>
      simp only [Polynomial.map_monomial, Polynomial.eval_monomial, map_mul, map_pow]
      congr 1
      exact (Complex.conj_ofReal a).symm

/-! ### The Bring–Jerrard direction

For a monic separable real septic with a non-real root `z`, any complex value `c` can be
prescribed at `z`, with conjugate value forced at `z̄` and vanishing at every other root.
The construction factors `q = (conjQuad z) * G` over `ℝ`; over `ℂ` this is
`qC = (X - z)(X - z̄) * GC`, so `GC` is supported on the remaining roots.  Multiplying
`G` by a linear real polynomial `h` chosen so that `G(z) * h(z) = c` does the rest. -/

-- Theorem: for a monic separable real septic with a non-real complex root `z`, every
-- complex value is attained at `z` by a real polynomial of degree at most six that
-- vanishes at all other complex roots and takes the conjugate value at `z̄`.
theorem exists_poly_value_at_root (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (c : ℂ) :
    ∃ f : ℝ[X], f.natDegree ≤ 6 ∧
      (f.map (algebraMap ℝ ℂ)).eval z = c ∧
      (f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = starRingEnd ℂ c ∧
      ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z → x ≠ starRingEnd ℂ z →
        (f.map (algebraMap ℝ ℂ)).eval x = 0 := by
  classical
  have hqne : q ≠ 0 := hmon.ne_zero
  have hpmon : (conjQuad z).Monic := conjQuad_monic z
  have hpdeg : (conjQuad z).natDegree = 2 := conjQuad_natDegree z
  have hpvd : conjQuad z ∣ q := conjQuad_dvd_of_root hz hzim
  set G : ℝ[X] := q /ₘ conjQuad z with hG
  have hdiv : conjQuad z * G = q := by
    have hmod0 : q %ₘ conjQuad z = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hpmon).mpr hpvd
    have h := Polynomial.modByMonic_add_div q (conjQuad z)
    rw [hmod0, zero_add] at h
    rw [hG]
    exact h
  have hGne : G ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdiv
    exact hqne hdiv.symm
  have hGdeg : G.natDegree = 5 := by
    have h := Polynomial.natDegree_mul hpmon.ne_zero hGne
    rw [hdiv, hpdeg, hnat] at h
    omega
  have h2im : (2 * z.im : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hzim
  have h2imC : (algebraMap ℝ ℂ (2 * z.im)) ≠ 0 := fun h =>
    h2im ((algebraMap ℝ ℂ).injective (by simpa using h))
  have h2im_ne : (algebraMap ℝ ℂ (2 * z.im)) * Complex.I ≠ 0 :=
    mul_ne_zero h2imC Complex.I_ne_zero
  have hmap : q.map (algebraMap ℝ ℂ)
      = ((conjQuad z).map (algebraMap ℝ ℂ)) * (G.map (algebraMap ℝ ℂ)) := by
    rw [← hdiv, Polynomial.map_mul]
  have hpCder : (((conjQuad z).map (algebraMap ℝ ℂ)).derivative).eval z
      = (algebraMap ℝ ℂ (2 * z.im)) * Complex.I := by
    rw [conjQuad_map_eq_prod]
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C, Polynomial.derivative_X_sub_C]
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, one_mul, mul_one, sub_self, add_zero,
      Complex.sub_conj]
    rfl
  have hderiv : (q.map (algebraMap ℝ ℂ)).derivative.eval z
      = (((conjQuad z).map (algebraMap ℝ ℂ)).derivative.eval z)
          * (G.map (algebraMap ℝ ℂ)).eval z
        + (((conjQuad z).map (algebraMap ℝ ℂ)).eval z)
          * (G.map (algebraMap ℝ ℂ)).derivative.eval z := by
    rw [hmap, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul]
  have hGCeq : (G.map (algebraMap ℝ ℂ)).eval z
      = (q.map (algebraMap ℝ ℂ)).derivative.eval z
          / ((algebraMap ℝ ℂ (2 * z.im)) * Complex.I) := by
    have h := hderiv
    rw [conjQuad_eval_map z, zero_mul, add_zero, hpCder] at h
    rw [h, eq_div_iff h2im_ne]
    ring
  have hqCsep : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  have hqCder_ne : (q.map (algebraMap ℝ ℂ)).derivative.eval z ≠ 0 := by
    have h := hqCsep.aeval_derivative_ne_zero (x := z) (by
      simp only [Polynomial.coe_aeval_eq_eval]
      exact hz)
    simpa only [Polynomial.coe_aeval_eq_eval] using h
  obtain ⟨h, hhdeg, hhval⟩ := exists_linear_eval z
    (c * ((algebraMap ℝ ℂ (2 * z.im)) * Complex.I)
      / (q.map (algebraMap ℝ ℂ)).derivative.eval z) hzim
  have hfz : ((G * h).map (algebraMap ℝ ℂ)).eval z = c := by
    rw [Polynomial.map_mul, Polynomial.eval_mul, hGCeq, hhval]
    field_simp [h2im_ne, hqCder_ne]
  have hfbar : ((G * h).map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)
      = starRingEnd ℂ c := by
    rw [eval_map_conj, hfz]
  have hfother : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((G * h).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    have hpCx : ((conjQuad z).map (algebraMap ℝ ℂ)).eval x ≠ 0 := by
      rw [conjQuad_map_eq_prod]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact mul_ne_zero (sub_ne_zero.mpr hxz) (sub_ne_zero.mpr hxz')
    have hxprod : (((conjQuad z).map (algebraMap ℝ ℂ)).eval x)
        * ((G.map (algebraMap ℝ ℂ)).eval x) = 0 := by
      rw [← Polynomial.eval_mul, ← Polynomial.map_mul, hdiv]
      exact hx
    have hGCx : (G.map (algebraMap ℝ ℂ)).eval x = 0 :=
      (mul_eq_zero.mp hxprod).resolve_left hpCx
    rw [Polynomial.map_mul, Polynomial.eval_mul, hGCx, zero_mul]
  have hfdeg : (G * h).natDegree ≤ 6 := by
    have := Polynomial.natDegree_mul_le_of_le (p := G) (q := h) (m := 5) (n := 1)
      (by omega) hhdeg
    simpa using this
  exact ⟨G * h, hfdeg, hfz, hfbar, hfother⟩

/-! ### Summing a function over a nodup multiset supported on two points -/

-- Theorem: for a nodup multiset of complex numbers, if `g` vanishes off `z` and `z'`, its
-- sum is `g z + g z'`.
theorem multiset_sum_eq_two_of_vanish {g : ℂ → ℂ} {s : Multiset ℂ} (hs : s.Nodup)
    {z z' : ℂ} (hz : z ∈ s) (hz' : z' ∈ s) (hzz' : z ≠ z')
    (hv : ∀ x : ℂ, x ∈ s → x ≠ z → x ≠ z' → g x = 0) :
    (s.map g).sum = g z + g z' := by
  have hval : s.toFinset.val = s := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hs]
  have h1 : (s.map g).sum = ∑ x ∈ s.toFinset, g x := by
    show (s.map g).sum = (s.toFinset.val.map g).sum
    rw [hval]
  have hsub : ({z, z'} : Finset ℂ) ⊆ s.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Multiset.mem_toFinset.mpr hz
    · exact Multiset.mem_toFinset.mpr hz'
  have hv' : ∀ x ∈ s.toFinset, x ∉ ({z, z'} : Finset ℂ) → g x = 0 := by
    intro x hx hxnot
    exact hv x (Multiset.mem_toFinset.mp hx)
      (fun hxz => hxnot (by rw [hxz]; simp))
      (fun hxz' => hxnot (by rw [hxz']; simp))
  rw [h1, ← Finset.sum_subset hsub hv']
  simp [hzz']

/-! ### Trace consequences -/

-- Theorem: a real polynomial taking the value `c` at a non-real root `z` and vanishing at
-- every other root has companion-matrix trace `c + c̄`.
theorem algebraMap_trace_eq_of_value (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (F : ℝ[X]) (c : ℂ)
    (hFz : (F.map (algebraMap ℝ ℂ)).eval z = c)
    (hFother : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → (F.map (algebraMap ℝ ℂ)).eval x = 0) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companion7 q) F)) = c + starRingEnd ℂ c := by
  have hqCne : (q.map (algebraMap ℝ ℂ)) ≠ 0 := (hmon.map (algebraMap ℝ ℂ)).ne_zero
  have hqCsep : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  have hnodup : (q.map (algebraMap ℝ ℂ)).roots.Nodup := Polynomial.nodup_roots hqCsep
  have hzmem : z ∈ (q.map (algebraMap ℝ ℂ)).roots :=
    (Polynomial.mem_roots hqCne).mpr hz
  have hzbarmem : starRingEnd ℂ z ∈ (q.map (algebraMap ℝ ℂ)).roots :=
    (Polynomial.mem_roots hqCne).mpr (by
      change Polynomial.eval (starRingEnd ℂ z) (Polynomial.map (algebraMap ℝ ℂ) q) = 0
      rw [eval_map_conj q z, hz, map_zero])
  have hzzber : z ≠ starRingEnd ℂ z := by
    intro h
    have him : z.im = -z.im := by
      have := congrArg Complex.im h
      rwa [Complex.conj_im] at this
    exact hzim (by linarith)
  rw [companion7_trace_aeval q F hmon hnat hsep]
  have hsum := multiset_sum_eq_two_of_vanish hnodup hzmem hzbarmem hzzber
    (g := fun x => (F.map (algebraMap ℝ ℂ)).eval x)
    (fun x hx hxz hxz' => hFother x ((Polynomial.mem_roots hqCne).mp hx) hxz hxz')
  rw [hsum]
  show (F.map (algebraMap ℝ ℂ)).eval z
      + (F.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = c + starRingEnd ℂ c
  rw [hFz, eval_map_conj F z, hFz]

-- Theorem: a real polynomial whose complex evaluation vanishes at every root of `qC` has
-- companion-matrix trace zero.
theorem trace_aeval_eq_zero_of_vanishes (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) (F : ℝ[X])
    (hF : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 →
      (F.map (algebraMap ℝ ℂ)).eval x = 0) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companion7 q) F)) = 0 := by
  have hqCne : (q.map (algebraMap ℝ ℂ)) ≠ 0 := (hmon.map (algebraMap ℝ ℂ)).ne_zero
  rw [companion7_trace_aeval q F hmon hnat hsep]
  refine Multiset.sum_eq_zero fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  exact hF x ((Polynomial.mem_roots hqCne).mp hx)

-- Theorem: for a non-real root `z`, some real polynomial of degree at most six has trace
-- `0` and trace of square `-2` in the companion matrix.
theorem exists_neg_trace (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) :
    ∃ f : ℝ[X], f.natDegree ≤ 6 ∧ Matrix.trace (aeval (companion7 q) f) = 0 ∧
      Matrix.trace ((aeval (companion7 q) f) ^ 2) = -2 := by
  obtain ⟨f, hfdeg, hfz, _hfbar, hfother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hz hzim Complex.I
  have hfsq : ((f ^ 2).map (algebraMap ℝ ℂ)).eval z = Complex.I ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfz]
  have hfothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((f ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfother x hx hxz hxz']
    simp
  have ht := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim f Complex.I hfz hfother
  have htsq := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim (f ^ 2) (Complex.I ^ 2)
    hfsq hfothersq
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hIc : starRingEnd ℂ ((Complex.I : ℂ) ^ 2) = -1 := by rw [hI, map_neg, map_one]
  refine ⟨f, hfdeg, ?_, ?_⟩
  · rw [Complex.conj_I, add_neg_cancel] at ht
    exact (algebraMap ℝ ℂ).injective (by simpa using ht)
  · have h2 : (Complex.I : ℂ) ^ 2 + starRingEnd ℂ ((Complex.I : ℂ) ^ 2) = -2 := by
      rw [hIc, hI]; norm_num
    rw [h2, map_pow] at htsq
    exact (algebraMap ℝ ℂ).injective (by simpa using htsq)

-- Theorem: for a non-real root `z`, some real polynomial of degree at most six has trace
-- `2` and trace of square `2` in the companion matrix.
theorem exists_pos_trace (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) :
    ∃ f : ℝ[X], f.natDegree ≤ 6 ∧ Matrix.trace (aeval (companion7 q) f) = 2 ∧
      Matrix.trace ((aeval (companion7 q) f) ^ 2) = 2 := by
  obtain ⟨f, hfdeg, hfz, _hfbar, hfother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hz hzim 1
  have hfsq : ((f ^ 2).map (algebraMap ℝ ℂ)).eval z = (1 : ℂ) ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfz]
  have hfothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((f ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfother x hx hxz hxz']
    simp
  have ht := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim f 1 hfz hfother
  have htsq := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim (f ^ 2) ((1 : ℂ) ^ 2)
    hfsq hfothersq
  refine ⟨f, hfdeg, ?_, ?_⟩
  · have h2 : (1 : ℂ) + starRingEnd ℂ (1 : ℂ) = 2 := by rw [map_one]; norm_num
    rw [h2] at ht
    exact (algebraMap ℝ ℂ).injective (by simpa using ht)
  · have h2 : ((1 : ℂ) ^ 2) + starRingEnd ℂ ((1 : ℂ) ^ 2) = 2 := by
      rw [one_pow, map_one]; norm_num
    rw [h2, map_pow] at htsq
    exact (algebraMap ℝ ℂ).injective (by simpa using htsq)

/-! ### Two conjugate pairs

Two non-real roots `z`, `w` from distinct conjugate pairs give polynomials supported on
disjoint sets of roots, so their traces and cross trace can be computed independently. -/

-- Theorem: two non-real roots from distinct conjugate pairs yield real polynomials of
-- degree at most six with vanishing traces, square traces `-2`, and vanishing cross trace.
theorem exists_neg_pair (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ f g : ℝ[X], f.natDegree ≤ 6 ∧ g.natDegree ≤ 6 ∧
      Matrix.trace (aeval (companion7 q) f) = 0 ∧ Matrix.trace (aeval (companion7 q) g) = 0 ∧
      Matrix.trace ((aeval (companion7 q) f) ^ 2) = -2 ∧
      Matrix.trace ((aeval (companion7 q) g) ^ 2) = -2 ∧
      Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)) = 0 := by
  obtain ⟨f, hfdeg, hfz, _hfbar, hfother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hz hzim Complex.I
  obtain ⟨g, hgdeg, hgw, _hgbar, hgother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hw hwim Complex.I
  have hzbar : (q.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = 0 := by
    rw [eval_map_conj, hz, map_zero]
  have hz'w : starRingEnd ℂ z ≠ w := by
    intro h
    apply hzw'
    have := congrArg (starRingEnd ℂ) h
    rw [starRingEnd_apply, starRingEnd_apply, star_star] at this
    exact this
  have hz'w' : starRingEnd ℂ z ≠ starRingEnd ℂ w := by
    intro h
    exact hzw ((starRingEnd ℂ).injective h)
  have hfsq : ((f ^ 2).map (algebraMap ℝ ℂ)).eval z = Complex.I ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfz]
  have hfothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((f ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfother x hx hxz hxz']
    simp
  have hgsq : ((g ^ 2).map (algebraMap ℝ ℂ)).eval w = Complex.I ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hgw]
  have hgothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ w →
      x ≠ starRingEnd ℂ w → ((g ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxw hxw'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hgother x hx hxw hxw']
    simp
  have htf := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim f Complex.I hfz hfother
  have htf_sq := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim (f ^ 2) (Complex.I ^ 2)
    hfsq hfothersq
  have htg := algebraMap_trace_eq_of_value q hmon hnat hsep hw hwim g Complex.I hgw hgother
  have htg_sq := algebraMap_trace_eq_of_value q hmon hnat hsep hw hwim (g ^ 2) (Complex.I ^ 2)
    hgsq hgothersq
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hIc : starRingEnd ℂ ((Complex.I : ℂ) ^ 2) = -1 := by rw [hI, map_neg, map_one]
  have hcross := trace_aeval_eq_zero_of_vanishes q hmon hnat hsep (f * g) (by
    intro x hx
    rw [Polynomial.map_mul, Polynomial.eval_mul]
    by_cases hxz : x = z
    · rw [hxz]
      have hgz : (g.map (algebraMap ℝ ℂ)).eval z = 0 := hgother z hz hzw hzw'
      rw [hgz, mul_zero]
    · by_cases hxz' : x = starRingEnd ℂ z
      · rw [hxz']
        have hgz : (g.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = 0 :=
          hgother _ hzbar hz'w hz'w'
        rw [hgz, mul_zero]
      · rw [hfother x hx hxz hxz', zero_mul])
  have htrace : Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)) = 0 := by
    have h1 : (aeval (companion7 q) f) * (aeval (companion7 q) g)
        = aeval (companion7 q) (f * g) := by rw [map_mul]
    rw [h1]
    exact (algebraMap ℝ ℂ).injective (by simpa using hcross)
  refine ⟨f, g, hfdeg, hgdeg, ?_, ?_, ?_, ?_, htrace⟩
  · rw [Complex.conj_I, add_neg_cancel] at htf
    exact (algebraMap ℝ ℂ).injective (by simpa using htf)
  · rw [Complex.conj_I, add_neg_cancel] at htg
    exact (algebraMap ℝ ℂ).injective (by simpa using htg)
  · have h2 : (Complex.I : ℂ) ^ 2 + starRingEnd ℂ ((Complex.I : ℂ) ^ 2) = -2 := by
      rw [hIc, hI]; norm_num
    rw [h2, map_pow] at htf_sq
    exact (algebraMap ℝ ℂ).injective (by simpa using htf_sq)
  · have h2 : (Complex.I : ℂ) ^ 2 + starRingEnd ℂ ((Complex.I : ℂ) ^ 2) = -2 := by
      rw [hIc, hI]; norm_num
    rw [h2, map_pow] at htg_sq
    exact (algebraMap ℝ ℂ).injective (by simpa using htg_sq)

-- Theorem: two non-real roots from distinct conjugate pairs yield real polynomials of
-- degree at most six with traces `2`, square traces `2`, and vanishing cross trace.
theorem exists_pos_pair (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ f g : ℝ[X], f.natDegree ≤ 6 ∧ g.natDegree ≤ 6 ∧
      Matrix.trace (aeval (companion7 q) f) = 2 ∧ Matrix.trace (aeval (companion7 q) g) = 2 ∧
      Matrix.trace ((aeval (companion7 q) f) ^ 2) = 2 ∧
      Matrix.trace ((aeval (companion7 q) g) ^ 2) = 2 ∧
      Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)) = 0 := by
  obtain ⟨f, hfdeg, hfz, _hfbar, hfother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hz hzim 1
  obtain ⟨g, hgdeg, hgw, _hgbar, hgother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hw hwim 1
  have hzbar : (q.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = 0 := by
    rw [eval_map_conj, hz, map_zero]
  have hz'w : starRingEnd ℂ z ≠ w := by
    intro h
    apply hzw'
    have := congrArg (starRingEnd ℂ) h
    rw [starRingEnd_apply, starRingEnd_apply, star_star] at this
    exact this
  have hz'w' : starRingEnd ℂ z ≠ starRingEnd ℂ w := by
    intro h
    exact hzw ((starRingEnd ℂ).injective h)
  have hfsq : ((f ^ 2).map (algebraMap ℝ ℂ)).eval z = (1 : ℂ) ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfz]
  have hfothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((f ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfother x hx hxz hxz']
    simp
  have hgsq : ((g ^ 2).map (algebraMap ℝ ℂ)).eval w = (1 : ℂ) ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hgw]
  have hgothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ w →
      x ≠ starRingEnd ℂ w → ((g ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxw hxw'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hgother x hx hxw hxw']
    simp
  have htf := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim f 1 hfz hfother
  have htf_sq := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim (f ^ 2) ((1 : ℂ) ^ 2)
    hfsq hfothersq
  have htg := algebraMap_trace_eq_of_value q hmon hnat hsep hw hwim g 1 hgw hgother
  have htg_sq := algebraMap_trace_eq_of_value q hmon hnat hsep hw hwim (g ^ 2) ((1 : ℂ) ^ 2)
    hgsq hgothersq
  have hcross := trace_aeval_eq_zero_of_vanishes q hmon hnat hsep (f * g) (by
    intro x hx
    rw [Polynomial.map_mul, Polynomial.eval_mul]
    by_cases hxz : x = z
    · rw [hxz]
      have hgz : (g.map (algebraMap ℝ ℂ)).eval z = 0 := hgother z hz hzw hzw'
      rw [hgz, mul_zero]
    · by_cases hxz' : x = starRingEnd ℂ z
      · rw [hxz']
        have hgz : (g.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = 0 :=
          hgother _ hzbar hz'w hz'w'
        rw [hgz, mul_zero]
      · rw [hfother x hx hxz hxz', zero_mul])
  have htrace : Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)) = 0 := by
    have h1 : (aeval (companion7 q) f) * (aeval (companion7 q) g)
        = aeval (companion7 q) (f * g) := by rw [map_mul]
    rw [h1]
    exact (algebraMap ℝ ℂ).injective (by simpa using hcross)
  refine ⟨f, g, hfdeg, hgdeg, ?_, ?_, ?_, ?_, htrace⟩
  · have h2 : (1 : ℂ) + starRingEnd ℂ (1 : ℂ) = 2 := by rw [map_one]; norm_num
    rw [h2] at htf
    exact (algebraMap ℝ ℂ).injective (by simpa using htf)
  · have h2 : (1 : ℂ) + starRingEnd ℂ (1 : ℂ) = 2 := by rw [map_one]; norm_num
    rw [h2] at htg
    exact (algebraMap ℝ ℂ).injective (by simpa using htg)
  · have h2 : ((1 : ℂ) ^ 2) + starRingEnd ℂ ((1 : ℂ) ^ 2) = 2 := by
      rw [one_pow, map_one]; norm_num
    rw [h2, map_pow] at htf_sq
    exact (algebraMap ℝ ℂ).injective (by simpa using htf_sq)
  · have h2 : ((1 : ℂ) ^ 2) + starRingEnd ℂ ((1 : ℂ) ^ 2) = 2 := by
      rw [one_pow, map_one]; norm_num
    rw [h2, map_pow] at htg_sq
    exact (algebraMap ℝ ℂ).injective (by simpa using htg_sq)

end

end Pconstructible


/- ==================== inlined from Pptc.ScratchN ==================== -/


open Polynomial Matrix Module

namespace Pconstructible

noncomputable section

/-! ### Characteristic polynomial from an eigenbasis

The Newton-identity argument computes the low coefficients of the characteristic polynomial
from the traces of powers.  We first record the general fact that, in a basis of
eigenvectors, the characteristic polynomial is the product of the linear factors
`X - C (eigenvalue)`. -/

-- Theorem: in a basis `b` of eigenvectors of `F` with eigenvalues `z`, the characteristic
-- polynomial of `F` is `∏ i, (X - C (z i))`.
theorem charpoly_eq_prod_of_eigenbasis {K ι V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Free K V] [Module.Finite K V] [Fintype ι]
    (F : Module.End K V) (b : Basis ι K V) (z : ι → K)
    (hv : ∀ i, F (b i) = z i • b i) :
    F.charpoly = ∏ i, (Polynomial.X - Polynomial.C (z i)) := by
  classical
  have hmatrix : LinearMap.toMatrix b b F = Matrix.diagonal z := by
    ext i j
    rw [LinearMap.toMatrix_apply, hv j, map_smul, Basis.repr_self]
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [← LinearMap.charpoly_toMatrix F b, hmatrix, Matrix.charpoly_diagonal]

/-! ### Eigenvector lemmas over an arbitrary commutative ring

`ScratchD` proved these over `ℝ`; the same induction works over any commutative ring, which
is what lets us move the companion matrix to `ℂ`. -/

theorem pow_mulVec_eigenvector_gen {K : Type*} [CommRing K] {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) {β : K} {v : n → K} (hv : M *ᵥ v = β • v) :
    ∀ k : ℕ, (M ^ k) *ᵥ v = (β ^ k) • v
  | 0 => by rw [pow_zero, Matrix.one_mulVec, pow_zero, one_smul]
  | k + 1 => by
      rw [pow_succ, ← Matrix.mulVec_mulVec v (M ^ k) M, hv, Matrix.mulVec_smul,
        pow_mulVec_eigenvector_gen M hv k, smul_smul, pow_succ']

theorem aeval_mulVec_eigenvector_gen {K : Type*} [CommRing K] {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) {β : K} {v : n → K} (hv : M *ᵥ v = β • v)
    (p : K[X]) :
    (aeval M p) *ᵥ v = (p.eval β) • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_mulVec, pow_mulVec_eigenvector_gen M hv n,
        Polynomial.eval_monomial, smul_smul]

/-! ### The characteristic polynomial of a polynomial in the generic companion matrix

We reuse the eigenbasis construction of `companion7'_trace_pow`: the roots of `q` index a
basis in which `aeval (companion7' q) φ` is diagonal with entries `φ.eval z`.  Hence its
characteristic polynomial is the product of `X - C (φ.eval z)`. -/

-- Theorem: the characteristic polynomial of `φ` evaluated at the degree-7 companion matrix
-- is the product of `X - C (φ.eval z)` over the roots `z` of `q`.
set_option linter.style.haveILetI false in
theorem companion7'_charpoly_aeval_eq_prod {K : Type*} [Field K] [IsAlgClosed K]
    (q φ : K[X]) (hmon : q.Monic) (hnat : q.natDegree = 7) (hsep : q.Separable) :
    (aeval (companion7' q) φ).charpoly
      = (q.roots.map (fun z => Polynomial.X - Polynomial.C (φ.eval z))).prod := by
  classical
  set M : Matrix (Fin 7) (Fin 7) K := companion7' q with hM
  have h7 : q.coeff 7 = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ 7 := le_of_eq hnat
  have hnodup : q.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard : q.roots.card = 7 := by
    rw [← hnat]; exact (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  let idx := q.roots.toFinset
  haveI : Nonempty idx := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
      show 0 < q.roots.toFinset.card
      rw [Multiset.toFinset_card_of_nodup hnodup, hcard]; norm_num)
    exact ⟨⟨x, hx⟩⟩
  let v : idx → (Fin 7 → K) := fun z => companionVecC (z : K)
  have hv : ∀ z : idx, M *ᵥ v z = (z : K) • v z := by
    intro z
    have hz : q.eval (z : K) = 0 :=
      (Polynomial.mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp z.2)
    exact companion7'_mulVec_companionVecC hz h7 hdeg
  have hvne : ∀ z : idx, v z ≠ 0 := by
    intro z h0
    have h1 := congrFun h0 0
    simp [v, companionVecC] at h1
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' M.toLin' (fun z : idx => (z : K))
      Subtype.coe_injective v (fun z =>
        ⟨(Module.End.mem_eigenspace_iff).mpr (by rw [Matrix.toLin'_apply]; exact hv z), hvne z⟩)
  have hcardfin : Fintype.card idx = Module.finrank K (Fin 7 → K) := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcard]
    norm_num
  let b : Basis idx K (Fin 7 → K) := basisOfLinearIndependentOfCardEqFinrank hli hcardfin
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have heig : ∀ z : idx, (aeval M φ).mulVecLin (b z) = (φ.eval (z : K)) • b z := by
    intro z
    rw [Matrix.mulVecLin_apply, hb]
    exact aeval_mulVec_eigenvector_gen M (hv z) φ
  have hchar := charpoly_eq_prod_of_eigenbasis ((aeval M φ).mulVecLin) b
    (fun z : idx => φ.eval (z : K)) heig
  rw [Matrix.charpoly_mulVecLin] at hchar
  rw [hM] at hchar
  rw [hchar]
  rw [Finset.prod_coe_sort idx (fun z : K => Polynomial.X - Polynomial.C (φ.eval z))]
  have hval : idx.val = q.roots := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  rw [show (∏ i ∈ idx, (Polynomial.X - Polynomial.C (φ.eval i)))
      = (idx.val.map (fun z => Polynomial.X - Polynomial.C (φ.eval z))).prod from rfl, hval]

/-! ### Mapping `aeval` along `ℝ → ℂ` -/

-- Theorem: mapping `aeval (companion7 q) φ` along `ℝ → ℂ` is `aeval` of the mapped
-- companion matrix and the mapped polynomial.
theorem companion7_aeval_map_eq (q φ : ℝ[X]) :
    (aeval (companion7 q) φ).map (algebraMap ℝ ℂ)
      = aeval (companion7' (q.map (algebraMap ℝ ℂ))) (φ.map (algebraMap ℝ ℂ)) := by
  rw [show (aeval (companion7 q) φ).map (algebraMap ℝ ℂ)
        = RingHom.mapMatrix (algebraMap ℝ ℂ) (aeval (companion7 q) φ) from
      (RingHom.mapMatrix_apply _ _).symm,
    Polynomial.map_aeval_eq_aeval_map (R := ℝ) (S := Matrix (Fin 7) (Fin 7) ℝ)
      (T := ℂ) (U := Matrix (Fin 7) (Fin 7) ℂ) (φ := algebraMap ℝ ℂ)
      (ψ := RingHom.mapMatrix (algebraMap ℝ ℂ))
      (by ext r i j; by_cases h : i = j <;>
        simp [RingHom.mapMatrix_apply, Matrix.algebraMap_matrix_apply, h])
      φ (companion7 q),
    RingHom.mapMatrix_apply, companion7_map_eq]

/-! ### Trace of a power as a power sum of the eigenvalues -/

-- Theorem: the trace of the `k`-th power of `aeval (companion7 q) φ` maps to the sum of
-- the `k`-th powers of `φ.eval z` over the complex roots `z` of `q`.
theorem companion7_trace_pow_aeval (q φ : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) (k : ℕ) :
    algebraMap ℝ ℂ (Matrix.trace ((aeval (companion7 q) φ) ^ k))
      = ((q.map (algebraMap ℝ ℂ)).roots.map
          (fun z => ((φ.map (algebraMap ℝ ℂ)).eval z) ^ k)).sum := by
  have hpow : (aeval (companion7 q) φ) ^ k = aeval (companion7 q) (φ ^ k) := by
    rw [map_pow]
  rw [hpow, companion7_trace_aeval q (φ ^ k) hmon hnat hsep]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro z _
  rw [Polynomial.map_pow, Polynomial.eval_pow]

/-! ### Elementary symmetric functions from power sums

We prove the first three Newton identities directly for `Multiset.esymm`, by the recurrence
`(a ::ₘ s).esymm (n+1) = s.esymm (n+1) + a * s.esymm n`.  This avoids any deduplication
argument (`Multiset.esymm` is defined for multisets with repetitions). -/

theorem esymm_zero (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm, Multiset.powersetCard_zero_left]

theorem esymm_cons (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Multiset.prod_cons, Function.comp_apply, Multiset.sum_map_mul_left]

theorem esymm_one_eq_sum (s : Multiset ℂ) : s.esymm 1 = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
      rw [show (a ::ₘ s).esymm 1 = s.esymm 1 + a * s.esymm 0 from esymm_cons a s 0,
        esymm_zero, mul_one]
      rw [ih, Multiset.sum_cons]
      ring

-- Theorem: `2 e₂ = e₁ p₁ - p₂` for a multiset, where `eᵢ` are elementary and `pᵢ` power sums.
theorem two_mul_esymm_two (s : Multiset ℂ) :
    2 * s.esymm 2 = s.esymm 1 * s.sum - (s.map (fun z => z ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
      rw [show (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.esymm 1 from esymm_cons a s 1,
        show (a ::ₘ s).esymm 1 = s.esymm 1 + a * s.esymm 0 from esymm_cons a s 0,
        esymm_zero, mul_one]
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
      have h1 := esymm_one_eq_sum s
      rw [h1] at ih ⊢
      linear_combination ih

-- Theorem: `3 e₃ = p₃ - e₁ p₂ + e₂ p₁` for a multiset.
theorem three_mul_esymm_three (s : Multiset ℂ) :
    3 * s.esymm 3 = (s.map (fun z => z ^ 3)).sum - s.esymm 1 * (s.map (fun z => z ^ 2)).sum
      + s.esymm 2 * s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
      rw [show (a ::ₘ s).esymm 3 = s.esymm 3 + a * s.esymm 2 from esymm_cons a s 2,
        show (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.esymm 1 from esymm_cons a s 1,
        show (a ::ₘ s).esymm 1 = s.esymm 1 + a * s.esymm 0 from esymm_cons a s 0,
        esymm_zero, mul_one]
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
        Multiset.sum_cons]
      have h1 := esymm_one_eq_sum s
      have h2 := two_mul_esymm_two s
      rw [h1] at ih h2 ⊢
      linear_combination ih + a * h2

-- Theorem: the first three elementary symmetric functions of a multiset vanish when the first
-- three power sums do.
theorem esymm_eq_zero_of_powerSums_zero (s : Multiset ℂ)
    (h1 : s.sum = 0) (h2 : (s.map (fun z => z ^ 2)).sum = 0)
    (h3 : (s.map (fun z => z ^ 3)).sum = 0) :
    s.esymm 1 = 0 ∧ s.esymm 2 = 0 ∧ s.esymm 3 = 0 := by
  have e1 : s.esymm 1 = 0 := by rw [esymm_one_eq_sum, h1]
  have e2 : s.esymm 2 = 0 := by
    have h := two_mul_esymm_two s
    rw [e1, h1, h2] at h
    simpa using h
  have e3 : s.esymm 3 = 0 := by
    have h := three_mul_esymm_three s
    rw [e1, e2, h1, h2, h3] at h
    simpa using h
  exact ⟨e1, e2, e3⟩

/-! ### The characteristic polynomial of `φ(companion7 q)` has no `X^6, X^5, X^4` terms -/

-- Theorem: if `q` is a monic separable septic over `ℝ` and `φ` has vanishing first three
-- trace power sums at `companion7 q`, then `charpoly (aeval (companion7 q) φ)` has zero
-- `X^6`, `X^5`, `X^4` coefficients.  The eigenvalues of `aeval (companion7 q) φ` are the
-- values `φ z` at the roots `z` of `q`, so the coefficients are elementary symmetric
-- functions of those values; the trace hypotheses are the vanishing power sums.
theorem charpoly_aeval_coeff_6_5_4_eq_zero {q φ : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 7) (hsep : q.Separable)
    (hp1 : Matrix.trace (aeval (companion7 q) φ) = 0)
    (hp2 : Matrix.trace ((aeval (companion7 q) φ) ^ 2) = 0)
    (hp3 : Matrix.trace ((aeval (companion7 q) φ) ^ 3) = 0) :
    (aeval (companion7 q) φ).charpoly.coeff 6 = 0 ∧
    (aeval (companion7 q) φ).charpoly.coeff 5 = 0 ∧
    (aeval (companion7 q) φ).charpoly.coeff 4 = 0 := by
  classical
  set qC : ℂ[X] := q.map (algebraMap ℝ ℂ) with hqC
  set φC : ℂ[X] := φ.map (algebraMap ℝ ℂ) with hφC
  set y : Multiset ℂ := qC.roots.map (fun z => φC.eval z) with hy
  set N : Matrix (Fin 7) (Fin 7) ℝ := aeval (companion7 q) φ with hN
  set R : ℝ[X] := N.charpoly with hR
  have hmon' : qC.Monic := by rw [hqC]; exact hmon.map _
  have hnat' : qC.natDegree = 7 := by
    rw [hqC, Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]; exact hnat
  have hsep' : qC.Separable := by rw [hqC]; exact hsep.map
  have hchar : R.map (algebraMap ℝ ℂ)
      = (y.map (fun w => Polynomial.X - Polynomial.C w)).prod := by
    have h1 : R.map (algebraMap ℝ ℂ) = (N.map (algebraMap ℝ ℂ)).charpoly := by
      rw [hR]
      exact (Matrix.charpoly_map N (algebraMap ℝ ℂ)).symm
    have h2 : N.map (algebraMap ℝ ℂ) = aeval (companion7' qC) φC := by
      rw [hN, hqC, hφC]
      exact companion7_aeval_map_eq q φ
    rw [h1, h2]
    simpa only [hy, Multiset.map_map, Function.comp_apply] using
      companion7'_charpoly_aeval_eq_prod qC φC hmon' hnat' hsep'
  have hycard : y.card = 7 := by
    rw [hy, Multiset.card_map]
    rw [show qC.roots.card = qC.natDegree from
      (IsAlgClosed.splits qC).natDegree_eq_card_roots.symm, hnat']
  have hsum_pow (k : ℕ) (hk : Matrix.trace (N ^ k) = 0) :
      (y.map (fun w => w ^ k)).sum = 0 := by
    have h := companion7_trace_pow_aeval q φ hmon hnat hsep k
    rw [hk, map_zero] at h
    rw [h]
    congr 1
    rw [hy, Multiset.map_map]
    rfl
  have h1y : y.sum = 0 := by
    have h := hsum_pow 1 (by rw [pow_one]; exact hp1)
    simpa using h
  have h2y : (y.map (fun w => w ^ 2)).sum = 0 := hsum_pow 2 hp2
  have h3y : (y.map (fun w => w ^ 3)).sum = 0 := hsum_pow 3 hp3
  have he := esymm_eq_zero_of_powerSums_zero y h1y h2y h3y
  have coeff_eq (k : ℕ) (hk : k ≤ y.card) :
      algebraMap ℝ ℂ (R.coeff k) = (-1) ^ (y.card - k) * y.esymm (y.card - k) := by
    rw [← Polynomial.coeff_map, hchar, Multiset.prod_X_sub_C_coeff y hk]
  have hcoeff (j : ℕ) (hj : j ≤ y.card) (hjesymm : y.esymm j = 0) :
      R.coeff (y.card - j) = 0 := by
    have h := coeff_eq (y.card - j) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hj, hjesymm, mul_zero] at h
    exact (algebraMap ℝ ℂ).injective (by simpa using h)
  refine ⟨?_, ?_, ?_⟩
  · have h := hcoeff 1 (by rw [hycard]; norm_num) he.1
    rw [hycard] at h
    norm_num at h
    exact h
  · have h := hcoeff 2 (by rw [hycard]; norm_num) he.2.1
    rw [hycard] at h
    norm_num at h
    exact h
  · have h := hcoeff 3 (by rw [hycard]; norm_num) he.2.2
    rw [hycard] at h
    norm_num at h
    exact h

end

end Pconstructible


/- ==================== inlined from Pptc.ScratchE ==================== -/


open Polynomial Matrix

namespace Pconstructible

/-! ### E1: the Hermite matrix entries are P-constructible -/

-- Theorem: the trace of the `k`-th power of the companion matrix is P-constructible.
theorem trace_pow_companion7_Pconstructible (q : ℝ[X])
    (hq : ∀ k, PConstructible (q.coeff k)) (k : ℕ) :
    PConstructible (Matrix.trace ((companion7 q) ^ k)) := by
  rw [Matrix.trace]
  exact Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun i _ => matrix_pow_entries_Pconstructible
      (companion7_entries_Pconstructible hq) k i i)

-- Theorem: `H i j = trace (M ^ (i + j))` is P-constructible.
theorem traceH_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (i j : Fin 7) :
    PConstructible (Matrix.trace ((companion7 q) ^ (i.val + j.val))) :=
  trace_pow_companion7_Pconstructible q hq (i.val + j.val)

/-! ### The Hermite form built from the companion matrix -/

/-- The Hermite (trace) form of `q`, in the monomial basis `1, X, …, X⁶`. -/
noncomputable def hermiteForm (q : ℝ[X]) (v : Fin 7 → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * Matrix.trace ((companion7 q) ^ (i.val + j.val)) * v j

/-- The polynomial whose coefficient vector is `v`. -/
noncomputable def polyOfVec (v : Fin 7 → ℝ) : ℝ[X] :=
  ∑ i : Fin 7, Polynomial.monomial i.val (v i)

-- Theorem: `aeval` of the coefficient vector is the corresponding matrix polynomial.
theorem aeval_polyOfVec (q : ℝ[X]) (v : Fin 7 → ℝ) :
    aeval (companion7 q) (polyOfVec v) = ∑ i : Fin 7, v i • (companion7 q) ^ i.val := by
  rw [polyOfVec, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one]
  rw [Matrix.smul_mul, Matrix.one_mul]

-- Theorem: the square of that matrix polynomial expands into the Hermite basis.
theorem aeval_polyOfVec_sq (q : ℝ[X]) (v : Fin 7 → ℝ) :
    (aeval (companion7 q) (polyOfVec v)) ^ 2 =
      ∑ i : Fin 7, ∑ j : Fin 7, (v i * v j) • (companion7 q) ^ (i.val + j.val) := by
  rw [aeval_polyOfVec, pow_two, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]

-- Theorem: the Hermite form is the trace of the square of the matrix polynomial.
theorem trace_aeval_polyOfVec_sq (q : ℝ[X]) (v : Fin 7 → ℝ) :
    Matrix.trace ((aeval (companion7 q) (polyOfVec v)) ^ 2) = hermiteForm q v := by
  rw [aeval_polyOfVec_sq, hermiteForm, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul]
  ring

-- Theorem: conversely, the Hermite form equals that trace.
theorem hermiteForm_eq_trace_sq (q : ℝ[X]) (v : Fin 7 → ℝ) :
    hermiteForm q v = Matrix.trace ((aeval (companion7 q) (polyOfVec v)) ^ 2) :=
  (trace_aeval_polyOfVec_sq q v).symm

end Pconstructible


/- ==================== inlined from Pptc.ScratchK ==================== -/


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
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · ring
  · intro j _ hji
    rw [hdiag i j (Ne.symm hji), zero_mul]

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
    have hnn : 0 ≤ ∑ i, D i i * (1 * v1 i + 0 * v2 i) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hnonneg i) (sq_nonneg _)
    have hsum := hneg 1 0 (Or.inl one_ne_zero)
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
  obtain ⟨i, j, hij, hi, hj⟩ := two_neg_diag_of_pair (A := -A) (D := -D) (v1 := v1) (v2 := v2)
    (fun i j h => by simp [hdiag i j h]) (by simp [hUD]) hdet fun a b hab => by
      simpa only [qform, Matrix.neg_mulVec, dotProduct_neg, neg_neg_iff_pos] using hpos a b hab
  exact ⟨i, j, hij, neg_neg_iff_pos.mp hi, neg_neg_iff_pos.mp hj⟩

end Pconstructible




/- ==================== inlined from Pptc.ScratchC2 ==================== -/


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
    · rw [if_pos h, if_pos (h.symm.imp And.symm And.symm)]
    · rw [if_neg h, if_neg fun h' => h (h'.symm.imp And.symm And.symm)]

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


/- ==================== inlined from Pptc.ScratchAB ==================== -/


open Polynomial Filter

namespace Pconstructible

-- Theorem: a cubic `a + b x + c x² + d x³` with `0 < d` has a real root. Since the leading
-- coefficient is positive, the cubic tends to `+∞` at `+∞` and to `-∞` at `-∞`, so the
-- intermediate value theorem applied to it and the zero function produces a root.
theorem cubic_exists_root_of_pos {a b c d : ℝ} (hd : 0 < d) :
    ∃ x : ℝ, a + b * x + c * x ^ 2 + d * x ^ 3 = 0 := by
  set p : Polynomial ℝ := C a + C b * X + C c * X ^ 2 + C d * X ^ 3 with hp
  have heval : ∀ x, p.eval x = a + b * x + c * x ^ 2 + d * x ^ 3 := by
    intro x
    simp [hp]
  have hdeg3 : p.degree = 3 := by
    rw [hp]
    compute_degree!
    exact hd.ne'
  have hnat : p.natDegree = 3 := Polynomial.natDegree_eq_of_degree_eq_some hdeg3
  have hdeg : 0 < p.degree := by rw [hdeg3]; norm_num
  have hlc : p.leadingCoeff = d := by
    show p.coeff p.natDegree = d
    rw [hnat, hp]
    simp
  have hcont : Continuous (fun x : ℝ => p.eval x) := by
    convert (by fun_prop : Continuous (fun x : ℝ => a + b * x + c * x ^ 2 + d * x ^ 3))
      using 1
    funext x
    exact heval x
  have htop : Tendsto (fun x : ℝ => p.eval x) atTop atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg hdeg (by rw [hlc]; exact hd.le)
  have hcomp_deg : 0 < (p.comp (-X)).degree := by
    rw [Polynomial.degree_comp_neg_X, hdeg3]
    norm_num
  have hcomp_lc : (p.comp (-X)).leadingCoeff ≤ 0 := by
    rw [Polynomial.comp_neg_X_leadingCoeff_eq, hnat, hlc]
    nlinarith [hd]
  have hcomp_tend : Tendsto (fun x : ℝ => (p.comp (-X)).eval x) atTop atBot :=
    (p.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos hcomp_deg hcomp_lc
  have hbot : Tendsto (fun x : ℝ => p.eval x) atBot atBot := by
    convert hcomp_tend.comp tendsto_neg_atBot_atTop using 1
    funext x
    simp [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
  obtain ⟨x, hx⟩ :=
    intermediate_value_univ₂_eventually₂ (f := fun x : ℝ => p.eval x)
      (g := fun _ => (0 : ℝ)) (l₁ := atBot) (l₂ := atTop) hcont continuous_const
      (hbot.eventually_le_atBot 0) (htop.eventually_ge_atTop 0)
  exact ⟨x, by simpa [heval] using hx⟩

-- Theorem: every nonzero-degree cubic `a + b x + c x² + d x³` (with `d ≠ 0`) has a real
-- root. For `d < 0` we apply the positive case to the negated coefficients and negate back.
theorem cubic_exists_root {a b c d : ℝ} (hd : d ≠ 0) :
    ∃ x : ℝ, a + b * x + c * x ^ 2 + d * x ^ 3 = 0 := by
  rcases lt_or_gt_of_ne hd with hlt | hgt
  · obtain ⟨x, hx⟩ := cubic_exists_root_of_pos (a := -a) (b := -b) (c := -c) (d := -d)
      (by linarith)
    refine ⟨x, ?_⟩
    have hneg : a + b * x + c * x ^ 2 + d * x ^ 3 =
        -((-a) + (-b) * x + (-c) * x ^ 2 + (-d) * x ^ 3) := by ring
    rw [hneg, hx, neg_zero]
  · exact cubic_exists_root_of_pos hgt

-- Theorem: the binary cubic `a s³ + b s² t + c s t² + d t³` has a nonzero P-constructible
-- solution. It is homogeneous, so it suffices to set `s = 1` and solve the univariate cubic
-- in `t`; a root of a P-constructible cubic is P-constructible.
theorem binary_cubic_zero {a b c d : ℝ} (ha : PConstructible a) (hb : PConstructible b)
    (hc : PConstructible c) (hd : PConstructible d) :
    ∃ s t : ℝ, PConstructible s ∧ PConstructible t ∧ (s ≠ 0 ∨ t ≠ 0) ∧
      a * s ^ 3 + b * s ^ 2 * t + c * s * t ^ 2 + d * t ^ 3 = 0 := by
  by_cases hd0 : d = 0
  · refine ⟨0, 1, zero_Pconstructible, PConstructible.base_one, Or.inr one_ne_zero, ?_⟩
    rw [hd0]
    ring
  · obtain ⟨t, ht⟩ := cubic_exists_root (a := a) (b := b) (c := c) hd0
    have htP : PConstructible t :=
      cubicVal_root_Pconstructible ha hb hc hd (Or.inl hd0)
        (by rw [cubicVal]; linarith [ht])
    refine ⟨1, t, PConstructible.base_one, htP, Or.inl one_ne_zero, ?_⟩
    simpa using ht

end Pconstructible


/- ==================== inlined from Pptc.ScratchS ==================== -/


open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### Trace form data

`Hmat q` is the Hermite/trace form of `q` in the monomial basis: `H i j = trace (M ^ (i+j))`
with `M = companion7 q`.  `p1vec` is the associated linear functional `v ↦ ∑ sᵢ vᵢ =
trace (aeval M (polyOfVec v))`, so that `{p1vec = 0}` is the trace-zero hyperplane, and `p3vec`
is the cubic `v ↦ trace ((aeval M (polyOfVec v)) ^ 3)`.  The plan is to find a
P-constructible `v` on which all three of `p1vec`, `qform Hmat` (= `p2`) and `p3vec` vanish. -/

/-- The trace form of `q` in the monomial basis. -/
def Hmat (q : ℝ[X]) : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => Matrix.trace ((companion7 q) ^ (i.val + j.val))

/-- The first moment functional: `sᵢ = trace (M ^ i)`. -/
def svec (q : ℝ[X]) : Fin 7 → ℝ := fun i => Matrix.trace ((companion7 q) ^ i.val)

/-- The linear functional `v ↦ ∑ sᵢ vᵢ = trace (aeval M (polyOfVec v))`. -/
def p1vec (q : ℝ[X]) (v : Fin 7 → ℝ) : ℝ := ∑ i, svec q i * v i

/-- The cubic functional `v ↦ trace ((aeval M (polyOfVec v)) ^ 3)`. -/
def p3vec (q : ℝ[X]) (v : Fin 7 → ℝ) : ℝ :=
  Matrix.trace ((aeval (companion7 q) (polyOfVec v)) ^ 3)

theorem Hmat_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (i j : Fin 7) : PConstructible (Hmat q i j) :=
  traceH_Pconstructible q hq i j

theorem Hmat_symm (q : ℝ[X]) : (Hmat q)ᵀ = Hmat q := by
  ext i j
  simp only [Matrix.transpose_apply, Hmat]
  rw [Nat.add_comm]

theorem svec_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (i : Fin 7) : PConstructible (svec q i) :=
  trace_pow_companion7_Pconstructible q hq i.val

theorem svec_zero (q : ℝ[X]) : svec q 0 = 7 := by
  show Matrix.trace ((companion7 q) ^ 0) = 7
  rw [pow_zero, Matrix.trace_one]
  norm_num

theorem p1vec_eq_trace (q : ℝ[X]) (v : Fin 7 → ℝ) :
    p1vec q v = Matrix.trace (aeval (companion7 q) (polyOfVec v)) := by
  rw [p1vec, aeval_polyOfVec, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul]
  simp only [svec]
  ring

theorem qform_Hmat_eq_hermiteForm (q : ℝ[X]) (v : Fin 7 → ℝ) :
    qform (Hmat q) v = hermiteForm q v := by
  simp only [qform, Hmat, hermiteForm, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ### Basic bilinearity of `bilin` -/

theorem bilin_comm {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (x y : Fin n → ℝ) :
    bilin A x y = bilin A y x := by
  simp only [bilin, dotProduct, Matrix.mulVec_apply, Matrix.row, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have hji : A j i = A i j := by
    have h := congrFun (congrFun hA i) j
    simpa [Matrix.transpose_apply] using h
  rw [hji]
  ring

theorem bilin_add_left (A : Matrix (Fin n) (Fin n) ℝ) (x₁ x₂ y : Fin n → ℝ) :
    bilin A (x₁ + x₂) y = bilin A x₁ y + bilin A x₂ y := by
  unfold bilin dotProduct
  simp only [Matrix.mulVec_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem bilin_add_right (A : Matrix (Fin n) (Fin n) ℝ) (x y₁ y₂ : Fin n → ℝ) :
    bilin A x (y₁ + y₂) = bilin A x y₁ + bilin A x y₂ := by
  unfold bilin dotProduct
  simp only [Matrix.mulVec_apply, dotProduct_add, mul_add, Finset.sum_add_distrib]

theorem bilin_smul_left (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x y : Fin n → ℝ) :
    bilin A (c • x) y = c * bilin A x y := by
  unfold bilin dotProduct
  simp only [Matrix.mulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem bilin_smul_right (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x y : Fin n → ℝ) :
    bilin A x (c • y) = c * bilin A x y := by
  unfold bilin dotProduct
  simp only [Matrix.mulVec_apply, smul_eq_mul, dotProduct_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem qform_eq_bilin (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform A x = bilin A x x := rfl

theorem qform_add (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (x y : Fin n → ℝ) :
    qform A (x + y) = qform A x + 2 * bilin A x y + qform A y := by
  rw [qform_eq_bilin, qform_eq_bilin A x, qform_eq_bilin A y,
    bilin_add_left, bilin_add_right, bilin_add_right, bilin_comm hA y x]
  ring

theorem qform_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform A x = ∑ j, ∑ k, x j * A j k * x k := by
  simp only [qform, dotProduct, Matrix.mulVec_apply, Matrix.row]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem bilin_sum_left {A : Matrix (Fin n) (Fin n) ℝ} {ι : Type*} [Fintype ι]
    (f : ι → Fin n → ℝ) (y : Fin n → ℝ) :
    bilin A (∑ i, f i) y = ∑ i, bilin A (f i) y := by
  simp only [bilin, dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem bilin_sum_right {A : Matrix (Fin n) (Fin n) ℝ} {ι : Type*} [Fintype ι]
    (x : Fin n → ℝ) (f : ι → Fin n → ℝ) :
    bilin A x (∑ i, f i) = ∑ i, bilin A x (f i) := by
  rw [bilin, Matrix.mulVec_sum, dotProduct_sum]
  rfl

theorem bilin_Pconstructible {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, PConstructible (A i j)) {u v : Fin n → ℝ}
    (hu : ∀ i, PConstructible (u i)) (hv : ∀ i, PConstructible (v i)) :
    PConstructible (bilin A u v) := by
  simp only [bilin, dotProduct, Matrix.mulVec_apply, Matrix.row]
  refine Finset.sum_Pconstructible Finset.univ (fun i => u i * ∑ j, A i j * v j)
    (fun i _ => ?_)
  refine PConstructible.mul (hu i) ?_
  exact Finset.sum_Pconstructible Finset.univ (fun j => A i j * v j)
    (fun j _ => PConstructible.mul (hA i j) (hv j))

/-! ### A basis of the hyperplane `{p1 = 0}`

Since `s 0 = 7 ≠ 0`, the six vectors `bⱼ = e_{j+1} - (s_{j+1}/7) e₀` (`j : Fin 6`) are a
P-constructible basis of `{p1vec = 0}`.  Every `v` with `p1vec q v = 0` is `Lcomb q (coeff6 v)`
where `coeff6` reads off coordinates `1, …, 6`; this makes the restricted form computable as a
`6 × 6` Gram matrix with no kernel to avoid. -/

/-- The basis vector `bⱼ = e_{j+1} - (s_{j+1}/7) e₀`, `j : Fin 6`. -/
def bvec (q : ℝ[X]) (j : Fin 6) : Fin 7 → ℝ :=
  e7 (Fin.succ j) - (svec q (Fin.succ j) / 7) • e7 (0 : Fin 7)

/-- Coordinates `1, …, 6` of a vector, i.e. those not involving `e₀`. -/
def coeff6 (v : Fin 7 → ℝ) : Fin 6 → ℝ := fun k => v (Fin.succ k)

/-- The combination `∑ j, x j • bⱼ`. -/
def Lcomb (q : ℝ[X]) (x : Fin 6 → ℝ) : Fin 7 → ℝ := ∑ j : Fin 6, x j • bvec q j

/-- The Gram matrix of the trace form in the basis `b`. -/
def Gram (q : ℝ[X]) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun j k => bilin (Hmat q) (bvec q j) (bvec q k)

theorem bvec_apply_zero (q : ℝ[X]) (j : Fin 6) :
    bvec q j 0 = -svec q (Fin.succ j) / 7 := by
  simp [bvec, e7_apply_ne (Fin.succ_ne_zero j).symm]
  ring

theorem bvec_apply_succ (q : ℝ[X]) (j k : Fin 6) :
    bvec q j (Fin.succ k) = if k = j then 1 else 0 := by
  simp only [bvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    e7_apply_ne (Fin.succ_ne_zero k), mul_zero, sub_zero]
  by_cases h : k = j
  · subst h
    rw [e7_apply_self, if_pos rfl]
  · rw [e7_apply_ne (fun hh => h (by simpa using hh)), if_neg h]

theorem bvec_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (j : Fin 6) (i : Fin 7) : PConstructible (bvec q j i) := by
  rw [bvec]
  refine PConstructible.sub ?_ ?_
  · by_cases h : i = Fin.succ j
    · rw [h, e7_apply_self]; exact PConstructible.base_one
    · rw [e7_apply_ne h]; exact zero_Pconstructible
  · refine PConstructible.mul ?_ ?_
    · exact PConstructible.div (svec_Pconstructible q hq (Fin.succ j)) (by pconstructible)
    · by_cases h : i = (0 : Fin 7)
      · rw [h, e7_apply_self]; exact PConstructible.base_one
      · rw [e7_apply_ne h]; exact zero_Pconstructible

theorem p1vec_bvec (q : ℝ[X]) (j : Fin 6) : p1vec q (bvec q j) = 0 := by
  rw [p1vec, Fin.sum_univ_succ]
  simp only [bvec_apply_zero, bvec_apply_succ, svec_zero]
  rw [Finset.sum_eq_single j]
  · simp only [↓reduceIte, mul_one]
    ring
  · intro k _ hk
    rw [if_neg hk]
    simp
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem p1vec_Lcomb (q : ℝ[X]) (x : Fin 6 → ℝ) : p1vec q (Lcomb q x) = 0 := by
  rw [Lcomb, p1vec]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : (∑ i, svec q i * (x j * bvec q j i)) = x j * p1vec q (bvec q j) := by
    rw [p1vec, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [this, p1vec_bvec, mul_zero]

theorem Lcomb_coeff6 (q : ℝ[X]) {v : Fin 7 → ℝ} (hv : p1vec q v = 0) :
    Lcomb q (coeff6 v) = v := by
  have hsum : (∑ j : Fin 6, v (Fin.succ j) * svec q (Fin.succ j)) = -7 * v 0 := by
    have h := hv
    rw [p1vec, Fin.sum_univ_succ, svec_zero] at h
    have h2 : (∑ j : Fin 6, svec q (Fin.succ j) * v (Fin.succ j)) = -7 * v 0 := by
      linarith
    rw [← h2]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Lcomb, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, bvec_apply_zero, coeff6]
    have : (∑ j : Fin 6, v (Fin.succ j) * (-svec q (Fin.succ j) / 7))
        = -(1 / 7) * ∑ j : Fin 6, v (Fin.succ j) * svec q (Fin.succ j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [this, hsum]
    ring
  · intro i
    rw [Lcomb, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, bvec_apply_succ, coeff6]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [if_neg (Ne.symm hk)]
      ring
    · intro hi; exact absurd (Finset.mem_univ i) hi

theorem Lcomb_injective (q : ℝ[X]) {x : Fin 6 → ℝ} (h : Lcomb q x = 0) : x = 0 := by
  funext k
  have hk := congrFun h (Fin.succ k)
  rw [Lcomb, Finset.sum_apply] at hk
  simp only [Pi.smul_apply, smul_eq_mul, bvec_apply_succ, Pi.zero_apply] at hk
  rw [Finset.sum_eq_single k] at hk
  · simpa using hk
  · intro j _ hj
    rw [if_neg (Ne.symm hj), mul_zero]
  · intro hk'; exact absurd (Finset.mem_univ k) hk'

theorem bilin_Lcomb (q : ℝ[X]) (x y : Fin 6 → ℝ) :
    bilin (Hmat q) (Lcomb q x) (Lcomb q y)
      = ∑ j, ∑ k, x j * y k * bilin (Hmat q) (bvec q j) (bvec q k) := by
  rw [Lcomb, bilin_sum_left]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Lcomb, bilin_sum_right]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [bilin_smul_left, bilin_smul_right]
  ring

theorem qform_Hmat_Lcomb (q : ℝ[X]) (x : Fin 6 → ℝ) :
    qform (Hmat q) (Lcomb q x) = qform (Gram q) x := by
  rw [qform_eq_bilin (Hmat q) (Lcomb q x), bilin_Lcomb, qform_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  simp only [Gram]
  ring

theorem Gram_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (j k : Fin 6) : PConstructible (Gram q j k) :=
  bilin_Pconstructible (Hmat_Pconstructible q hq) (bvec_Pconstructible q hq j)
    (bvec_Pconstructible q hq k)

theorem Gram_symm (q : ℝ[X]) : (Gram q)ᵀ = Gram q := by
  ext j k
  simp only [Matrix.transpose_apply, Gram]
  rw [bilin_comm (Hmat_symm q)]

/-! ### From polynomials to coefficient vectors

`vecOf f = (f.coeff 0, …, f.coeff 6)` reads off the coefficients of a degree-`≤ 6` polynomial.
It makes `p1vec`, `qform Hmat` and `p3vec` computable in terms of `trace`/`hermiteForm`, which
is what turns the abstract sign results `exists_neg_pair` / `exists_pos_pair` into explicit
directions for the Gram matrix. -/

/-- The coefficient vector `(f.coeff 0, …, f.coeff 6)` of a polynomial. -/
def vecOf (f : ℝ[X]) : Fin 7 → ℝ := fun i => f.coeff i.val

theorem polyOfVec_vecOf {f : ℝ[X]} (hf : f.natDegree ≤ 6) : polyOfVec (vecOf f) = f := by
  rw [polyOfVec]
  simp only [vecOf]
  rw [Fin.sum_univ_eq_sum_range (fun k => Polynomial.monomial k (f.coeff k)) 7]
  exact (Polynomial.as_sum_range' f 7 (by omega)).symm

theorem polyOfVec_smul_add {a b : ℝ} {f g : ℝ[X]} (hf : f.natDegree ≤ 6)
    (hg : g.natDegree ≤ 6) :
    polyOfVec (a • vecOf f + b • vecOf g) = C a * f + C b * g := by
  have h1 : a • vecOf f + b • vecOf g = vecOf (C a * f + C b * g) := by
    ext i
    simp only [vecOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
  rw [h1, polyOfVec_vecOf]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  exact max_le (le_trans (Polynomial.natDegree_C_mul_le a f) hf)
    (le_trans (Polynomial.natDegree_C_mul_le b g) hg)

theorem p1vec_vecOf (q : ℝ[X]) (f : ℝ[X]) (hf : f.natDegree ≤ 6) :
    p1vec q (vecOf f) = Matrix.trace (aeval (companion7 q) f) := by
  rw [p1vec_eq_trace, polyOfVec_vecOf hf]

theorem aeval_C_mul_smul (q : ℝ[X]) (a b : ℝ) (f g : ℝ[X]) :
    aeval (companion7 q) (C a * f + C b * g)
      = a • aeval (companion7 q) f + b • aeval (companion7 q) g := by
  rw [map_add, map_mul, map_mul]
  simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul]

theorem qform_Hmat_smul_add_vecOf (q : ℝ[X]) (a b : ℝ) (f g : ℝ[X])
    (hf : f.natDegree ≤ 6) (hg : g.natDegree ≤ 6) :
    qform (Hmat q) (a • vecOf f + b • vecOf g) =
      Matrix.trace ((aeval (companion7 q) (C a * f + C b * g)) ^ 2) := by
  rw [qform_Hmat_eq_hermiteForm, hermiteForm_eq_trace_sq, polyOfVec_smul_add hf hg]

theorem smul_mul_smul (a b : ℝ) (A B : Matrix (Fin 7) (Fin 7) ℝ) :
    (a • A) * (b • B) = (a * b) • (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem trace_sq_smul_add (A B : Matrix (Fin 7) (Fin 7) ℝ) (a b : ℝ) :
    Matrix.trace ((a • A + b • B) ^ 2) =
      a ^ 2 * Matrix.trace (A ^ 2) + 2 * a * b * Matrix.trace (A * B)
        + b ^ 2 * Matrix.trace (B ^ 2) := by
  rw [sq, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [smul_mul_smul, Matrix.trace_add, Matrix.trace_smul]
  rw [Matrix.trace_mul_comm B A]
  simp only [pow_two, smul_eq_mul]
  ring

theorem qform_smul (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    qform A (c • x) = c ^ 2 * qform A x := by
  rw [qform_eq_bilin, qform_eq_bilin A x, bilin_smul_left, bilin_smul_right]
  ring

theorem bilin_smul_smul (A : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) (u v : Fin n → ℝ) :
    bilin A (a • u) (b • v) = a * b * bilin A u v := by
  rw [bilin_smul_left, bilin_smul_right]
  ring

theorem qform_smul_add (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (a b : ℝ)
    (u v : Fin n → ℝ) :
    qform A (a • u + b • v) =
      a ^ 2 * qform A u + 2 * a * b * bilin A u v + b ^ 2 * qform A v := by
  rw [qform_add A hA, qform_smul, qform_smul, bilin_smul_smul]
  ring

theorem Lcomb_smul_add (q : ℝ[X]) (a b : ℝ) (x y : Fin 6 → ℝ) :
    Lcomb q (a • x + b • y) = a • Lcomb q x + b • Lcomb q y := by
  rw [Lcomb, Lcomb, Lcomb, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, add_smul]
  module

theorem bilin_congr (A U : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    bilin (Uᵀ * A * U) x y = bilin A (U *ᵥ x) (U *ᵥ y) := by
  unfold bilin
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem bilin_diag {D : Matrix (Fin n) (Fin n) ℝ} (hdiag : ∀ i j, i ≠ j → D i j = 0)
    (v w : Fin n → ℝ) :
    bilin D v w = ∑ i, D i i * v i * w i := by
  simp only [bilin, dotProduct, Matrix.mulVec_apply, Matrix.row]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    simp [hdiag i j (Ne.symm hji)]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ### Negative and positive two-planes in `{p1 = 0}`

`exists_neg_pair` / `exists_pos_pair` produce polynomials supported on two distinct conjugate
pairs.  Their coefficient vectors land in `{p1vec = 0}` (after subtracting the mean in the
positive case), which lets us read them as coordinates in the `b`-basis; the trace identities
then say the restricted form `Gram` is negative definite (resp. positive definite) on the
spanned plane. -/

theorem neg_dir_of_pair (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z w : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ v1 v2 : Fin 6 → ℝ,
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → qform (Gram q) (a • v1 + b • v2) < 0 := by
  obtain ⟨f, g, hfdeg, hgdeg, htrf, htrg, hsqf, hsqg, hcross⟩ :=
    exists_neg_pair q hmon hnat hsep hz hzim hw hwim hzw hzw'
  refine ⟨coeff6 (vecOf f), coeff6 (vecOf g), ?_⟩
  have hpf : p1vec q (vecOf f) = 0 := by rw [p1vec_vecOf q f hfdeg, htrf]
  have hpg : p1vec q (vecOf g) = 0 := by rw [p1vec_vecOf q g hgdeg, htrg]
  intro a b hab
  rw [← qform_Hmat_Lcomb q, Lcomb_smul_add, Lcomb_coeff6 q hpf, Lcomb_coeff6 q hpg]
  rw [qform_Hmat_smul_add_vecOf q a b f g hfdeg hgdeg, aeval_C_mul_smul,
    trace_sq_smul_add, hsqf, hcross, hsqg]
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb]
  nlinarith

theorem aeval_sub_C (q : ℝ[X]) (c : ℝ) (f : ℝ[X]) :
    aeval (companion7 q) (f - C c)
      = aeval (companion7 q) f - c • (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
  rw [map_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

theorem trace_sq_sub_scalar (A : Matrix (Fin 7) (Fin 7) ℝ) (c : ℝ) :
    Matrix.trace ((A - c • 1) ^ 2) =
      Matrix.trace (A ^ 2) - 2 * c * Matrix.trace A + c ^ 2 * 7 := by
  have h : A - c • 1 = (1 : ℝ) • A + (-c) • (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
    rw [one_smul, neg_smul, sub_eq_add_neg]
  rw [h, trace_sq_smul_add, Matrix.mul_one]
  simp only [pow_two, one_mul, mul_one, Matrix.trace_one]
  norm_num
  ring

theorem aeval_sub_C_smul_add (q : ℝ[X]) (a b c : ℝ) (f g : ℝ[X]) :
    aeval (companion7 q) (C a * (f - C c) + C b * (g - C c))
      = a • aeval (companion7 q) f + b • aeval (companion7 q) g - ((a + b) * c) • 1 := by
  rw [aeval_C_mul_smul, aeval_sub_C, aeval_sub_C]
  module

theorem pos_dir_of_pair (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z w : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ v1 v2 : Fin 6 → ℝ,
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < qform (Gram q) (a • v1 + b • v2) := by
  obtain ⟨f, g, hfdeg, hgdeg, htrf, htrg, hsqf, hsqg, hcross⟩ :=
    exists_pos_pair q hmon hnat hsep hz hzim hw hwim hzw hzw'
  refine ⟨coeff6 (vecOf (f - C (2 / 7))), coeff6 (vecOf (g - C (2 / 7))), ?_⟩
  have hf'deg : (f - C (2 / 7)).natDegree ≤ 6 := by
    refine le_trans (Polynomial.natDegree_sub_le f (C (2 / 7))) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hfdeg
  have hg'deg : (g - C (2 / 7)).natDegree ≤ 6 := by
    refine le_trans (Polynomial.natDegree_sub_le g (C (2 / 7))) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hgdeg
  have hpf : p1vec q (vecOf (f - C (2 / 7))) = 0 := by
    rw [p1vec_vecOf q (f - C (2 / 7)) hf'deg, aeval_sub_C, Matrix.trace_sub,
      Matrix.trace_smul, htrf, Matrix.trace_one]
    norm_num
  have hpg : p1vec q (vecOf (g - C (2 / 7))) = 0 := by
    rw [p1vec_vecOf q (g - C (2 / 7)) hg'deg, aeval_sub_C, Matrix.trace_sub,
      Matrix.trace_smul, htrg, Matrix.trace_one]
    norm_num
  intro a b hab
  rw [← qform_Hmat_Lcomb q, Lcomb_smul_add, Lcomb_coeff6 q hpf, Lcomb_coeff6 q hpg]
  rw [qform_Hmat_smul_add_vecOf q a b (f - C (2 / 7)) (g - C (2 / 7)) hf'deg hg'deg,
    aeval_sub_C_smul_add, trace_sq_sub_scalar]
  have htrA : Matrix.trace (a • aeval (companion7 q) f + b • aeval (companion7 q) g)
      = 2 * a + 2 * b := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htrf, htrg]
    simp only [smul_eq_mul]
    ring
  have hsqA : Matrix.trace ((a • aeval (companion7 q) f + b • aeval (companion7 q) g) ^ 2)
      = 2 * a ^ 2 + 2 * b ^ 2 := by
    rw [trace_sq_smul_add, hsqf, hcross, hsqg]
    ring
  rw [htrA, hsqA]
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb]
  nlinarith [sq_nonneg (a - 2 * b), sq_nonneg a, sq_nonneg b]

theorem cube_add (X Y : Matrix (Fin 7) (Fin 7) ℝ) :
    (X + Y) ^ 3 = X ^ 3 + X ^ 2 * Y + X * Y * X + Y * X ^ 2 + X * Y ^ 2
      + Y * X * Y + Y ^ 2 * X + Y ^ 3 := by
  noncomm_ring

theorem smul_pow (c : ℝ) (M : Matrix (Fin 7) (Fin 7) ℝ) (n : ℕ) :
    (c • M) ^ n = (c ^ n) • M ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, smul_mul_smul, ← pow_succ, ← pow_succ]

theorem cube_smul_add (A B : Matrix (Fin 7) (Fin 7) ℝ) (a b : ℝ) :
    (a • A + b • B) ^ 3 =
      (a * a * a) • (A * A * A) + (a * a * b) • (A * A * B) + (a * a * b) • (A * B * A)
        + (a * b * b) • (A * B * B) + (a * a * b) • (B * A * A)
        + (a * b * b) • (B * A * B) + (a * b * b) • (B * B * A) + (b * b * b) • (B * B * B) := by
  rw [show (a • A + b • B) ^ 3 = _ from cube_add (a • A) (b • B)]
  simp only [smul_mul_smul, pow_succ, pow_zero, Matrix.one_mul, mul_assoc, mul_comm,
    mul_left_comm]
  abel

theorem trace_cube_smul_add (A B : Matrix (Fin 7) (Fin 7) ℝ) (a b : ℝ) :
    Matrix.trace ((a • A + b • B) ^ 3) = a ^ 3 * Matrix.trace (A ^ 3)
      + 3 * a ^ 2 * b * Matrix.trace (A ^ 2 * B) + 3 * a * b ^ 2 * Matrix.trace (A * B ^ 2)
      + b ^ 3 * Matrix.trace (B ^ 3) := by
  rw [cube_smul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul]
  rw [show Matrix.trace (A * A * A) = Matrix.trace (A ^ 3) by rw [← pow_two, ← pow_succ],
    show Matrix.trace (A * A * B) = Matrix.trace (A ^ 2 * B) by rw [← pow_two],
    show Matrix.trace (A * B * A) = Matrix.trace (A ^ 2 * B) by
      rw [Matrix.trace_mul_comm (A * B) A, ← Matrix.mul_assoc, ← pow_two],
    show Matrix.trace (A * B * B) = Matrix.trace (A * B ^ 2) by rw [Matrix.mul_assoc, ← pow_two],
    show Matrix.trace (B * A * A) = Matrix.trace (A ^ 2 * B) by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm B (A * A), ← pow_two],
    show Matrix.trace (B * A * B) = Matrix.trace (A * B ^ 2) by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm B (A * B), Matrix.mul_assoc, ← pow_two],
    show Matrix.trace (B * B * A) = Matrix.trace (A * B ^ 2) by
      rw [Matrix.trace_mul_comm (B * B) A, ← pow_two],
    show Matrix.trace (B * B * B) = Matrix.trace (B ^ 3) by rw [← pow_two, ← pow_succ]]
  simp only [smul_eq_mul]
  ring

/-! ### Remaining transport helpers -/

theorem Lcomb_smul (q : ℝ[X]) (c : ℝ) (x : Fin 6 → ℝ) :
    Lcomb q (c • x) = c • Lcomb q x := by
  rw [Lcomb, Lcomb, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, smul_smul]

theorem Lcomb_sub (q : ℝ[X]) (x y : Fin 6 → ℝ) :
    Lcomb q (x - y) = Lcomb q x - Lcomb q y := by
  rw [Lcomb, Lcomb, Lcomb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.sub_apply, sub_smul]

theorem mulVec_Pconstructible {U : Matrix (Fin 6) (Fin 6) ℝ}
    (hU : ∀ i j, PConstructible (U i j)) {x : Fin 6 → ℝ}
    (hx : ∀ j, PConstructible (x j)) (i : Fin 6) :
    PConstructible ((U *ᵥ x) i) := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_Pconstructible Finset.univ (fun j => U i j * x j)
    (fun j _ => PConstructible.mul (hU i j) (hx j))

theorem Lcomb_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {x : Fin 6 → ℝ} (hx : ∀ j, PConstructible (x j)) :
    ∀ i, PConstructible (Lcomb q x i) := by
  intro i
  rw [Lcomb, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_Pconstructible Finset.univ (fun j => x j * bvec q j i)
    (fun j _ => PConstructible.mul (hx j) (bvec_Pconstructible q hq j i))

theorem mulVec_eq_zero_of_det_ne_zero {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.det ≠ 0)
    {z : Fin n → ℝ} (h : U *ᵥ z = 0) : z = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero hU h

theorem bilin_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    bilin A x y = ∑ j, ∑ k, x j * A j k * y k := by
  simp only [bilin, dotProduct, Matrix.mulVec_apply, Matrix.row]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem bilin_Hmat_Lcomb (q : ℝ[X]) (x y : Fin 6 → ℝ) :
    bilin (Hmat q) (Lcomb q x) (Lcomb q y) = bilin (Gram q) x y := by
  rw [bilin_Lcomb, bilin_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  simp only [Gram]
  ring

theorem trace_pow_Pconstructible {M : Matrix (Fin 7) (Fin 7) ℝ}
    (hM : ∀ i j, PConstructible (M i j)) (k : ℕ) :
    PConstructible (Matrix.trace (M ^ k)) := by
  rw [Matrix.trace]
  exact Finset.sum_Pconstructible Finset.univ (fun i => (M ^ k) i i)
    (fun i _ => matrix_pow_entries_Pconstructible hM k i i)

theorem trace_mul_Pconstructible {A B : Matrix (Fin 7) (Fin 7) ℝ}
    (hA : ∀ i j, PConstructible (A i j)) (hB : ∀ i j, PConstructible (B i j)) :
    PConstructible (Matrix.trace (A * B)) := by
  rw [Matrix.trace]
  exact Finset.sum_Pconstructible Finset.univ (fun i => (A * B) i i)
    (fun i _ => matrix_mul_entries_Pconstructible hA hB i i)

theorem coeff_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ[X]) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

theorem polyOfVec_coeff_Pconstructible (v : Fin 7 → ℝ) (hv : ∀ i, PConstructible (v i))
    (k : ℕ) : PConstructible ((polyOfVec v).coeff k) := by
  rw [polyOfVec, coeff_finset_sum]
  refine Finset.sum_Pconstructible Finset.univ
    (fun i => (Polynomial.monomial i.val (v i)).coeff k) (fun i _ => ?_)
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · exact hv i
  · exact zero_Pconstructible

theorem polyOfVec_natDegree_le (v : Fin 7 → ℝ) : (polyOfVec v).natDegree ≤ 6 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => ?_)
  rw [polyOfVec, coeff_finset_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

theorem polyOfVec_ne_zero {v : Fin 7 → ℝ} (hv : v ≠ 0) : polyOfVec v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hc : (polyOfVec v).coeff i.val = 0 := by rw [h, Polynomial.coeff_zero]
  rw [polyOfVec, coeff_finset_sum] at hc
  rw [Finset.sum_eq_single i] at hc
  · simpa [Polynomial.coeff_monomial] using hc
  · intro j _ hji
    rw [Polynomial.coeff_monomial]
    split_ifs with h'
    · exact absurd (Fin.ext h') hji
    · rfl
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem aeval_polyOfVec_smul_add (q : ℝ[X]) (s t : ℝ) (x y : Fin 7 → ℝ) :
    aeval (companion7 q) (polyOfVec (s • x + t • y))
      = s • aeval (companion7 q) (polyOfVec x)
        + t • aeval (companion7 q) (polyOfVec y) := by
  rw [aeval_polyOfVec, aeval_polyOfVec, aeval_polyOfVec, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, add_smul, smul_smul,
    smul_smul]

theorem p1vec_smul_add (q : ℝ[X]) (s t : ℝ) (x y : Fin 7 → ℝ) :
    p1vec q (s • x + t • y) = s * p1vec q x + t * p1vec q y := by
  rw [p1vec_eq_trace, aeval_polyOfVec_smul_add, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, p1vec_eq_trace q x, p1vec_eq_trace q y]
  simp only [smul_eq_mul]


/-! ### The main trace-killing Tschirnhaus polynomial

Assembly of the `s ≥ 2` construction: the two definite two-planes from `neg_dir_of_pair` and
`pos_dir_of_pair` produce, via inertia and diagonalisation, a totally isotropic plane for the
quadratic part on `{p1 = 0}`; the cubic part restricted to that plane is a binary cubic, and
`binary_cubic_zero` picks a P-constructible zero `s • cv + t • cw`. The resulting `φ` has
vanishing first three trace power sums. -/

-- Theorem: if `w` is not a scalar multiple of a nonzero `v`, then `s • v + t • w = 0` forces
-- `s = t = 0` (used to show the constructed `φ` is nonzero).
theorem smul_add_smul_eq_zero_of_not_parallel {V : Type*} [AddCommGroup V] [Module ℝ V]
    {v w : V} (hv : v ≠ 0) (h : ¬ ∃ c : ℝ, w = c • v) {s t : ℝ}
    (hst : s • v + t • w = 0) : s = 0 ∧ t = 0 := by
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h1 | h1
    · exact ⟨h1, rfl⟩
    · exact absurd h1 hv
  · exfalso
    apply h
    refine ⟨-(s * t⁻¹), ?_⟩
    have h1 : t • w = -(s • v) := eq_neg_of_add_eq_zero_right hst
    calc w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = t⁻¹ • (-(s • v)) := by rw [h1]
      _ = (-(s * t⁻¹)) • v := by rw [smul_neg, smul_smul, ← neg_smul, mul_comm]

theorem exists_tschirnhaus_traces (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k)) {z w : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ φ : ℝ[X], (∀ k, PConstructible (φ.coeff k)) ∧ φ.natDegree ≤ 6 ∧ φ ≠ 0 ∧
      Matrix.trace (aeval (companion7 q) φ) = 0 ∧
      Matrix.trace ((aeval (companion7 q) φ) ^ 2) = 0 ∧
      Matrix.trace ((aeval (companion7 q) φ) ^ 3) = 0 := by
  obtain ⟨v1, v2, hneg⟩ := neg_dir_of_pair q hmon hnat hsep hz hzim hw hwim hzw hzw'
  obtain ⟨w1, w2, hpos⟩ := pos_dir_of_pair q hmon hnat hsep hz hzim hw hwim hzw hzw'
  obtain ⟨U, D, hUP, hDP, hDdiag, hUD, hUdet⟩ :=
    exists_diag_congruence (Gram q) (Gram_symm q) (Gram_Pconstructible q hq)
  obtain ⟨i1, i2, hi12, hi1, hi2⟩ := two_neg_diag_of_pair hDdiag hUD hUdet hneg
  obtain ⟨j1, j2, hj12, hj1, hj2⟩ := two_pos_diag_of_pair hDdiag hUD hUdet hpos
  obtain ⟨v, wv, hvP, hwP, hvne, hwne, hqv, hqw, hbvw, hindep⟩ :=
    exists_diagonal_isotropic_vectors (fun i => D i i) (fun i => hDP i i) (by norm_num)
      ⟨j1, j2, hj12, hj1, hj2⟩ ⟨i1, i2, hi12, hi1, hi2⟩
  set cv : Fin 7 → ℝ := Lcomb q (U *ᵥ v) with hcv
  set cw : Fin 7 → ℝ := Lcomb q (U *ᵥ wv) with hcw
  have hcvP : ∀ i, PConstructible (cv i) :=
    Lcomb_Pconstructible q hq (mulVec_Pconstructible hUP hvP)
  have hcwP : ∀ i, PConstructible (cw i) :=
    Lcomb_Pconstructible q hq (mulVec_Pconstructible hUP hwP)
  have hqformv : qform (Hmat q) cv = 0 := by
    rw [hcv, qform_Hmat_Lcomb, ← qform_congr, hUD, qform_diag hDdiag, hqv]
  have hqformw : qform (Hmat q) cw = 0 := by
    rw [hcw, qform_Hmat_Lcomb, ← qform_congr, hUD, qform_diag hDdiag, hqw]
  have hbilinc : bilin (Hmat q) cv cw = 0 := by
    rw [hcv, hcw, bilin_Hmat_Lcomb, ← bilin_congr, hUD, bilin_diag hDdiag, hbvw]
  have hp1v : p1vec q cv = 0 := by rw [hcv, p1vec_Lcomb]
  have hp1w : p1vec q cw = 0 := by rw [hcw, p1vec_Lcomb]
  have hindep' : ¬ ∃ c : ℝ, cw = c • cv := by
    rintro ⟨c, hc⟩
    have h1 : Lcomb q (U *ᵥ wv - c • (U *ᵥ v)) = 0 := by
      rw [Lcomb_sub, Lcomb_smul, ← hcw, ← hcv, hc, sub_self]
    have h2 : U *ᵥ wv - c • (U *ᵥ v) = 0 := Lcomb_injective q h1
    have h3 : U *ᵥ (wv - c • v) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h2]
    have h4 : wv - c • v = 0 := mulVec_eq_zero_of_det_ne_zero hUdet h3
    exact hindep ⟨c, sub_eq_zero.mp h4⟩
  have hcvne : cv ≠ 0 := by
    intro h0
    have h1 : U *ᵥ v = 0 := Lcomb_injective q (by rw [hcv] at h0; exact h0)
    exact hvne (mulVec_eq_zero_of_det_ne_zero hUdet h1)
  have hcwne : cw ≠ 0 := by
    intro h0
    have h1 : U *ᵥ wv = 0 := Lcomb_injective q (by rw [hcw] at h0; exact h0)
    exact hwne (mulVec_eq_zero_of_det_ne_zero hUdet h1)
  set Ncv : Matrix (Fin 7) (Fin 7) ℝ := aeval (companion7 q) (polyOfVec cv) with hNcv
  set Ncw : Matrix (Fin 7) (Fin 7) ℝ := aeval (companion7 q) (polyOfVec cw) with hNcw
  have hNcvP : ∀ i j, PConstructible (Ncv i j) := by
    intro i j
    rw [hNcv]
    exact aeval_entries_Pconstructible _ (companion7_entries_Pconstructible hq) _
      (polyOfVec_coeff_Pconstructible cv hcvP) i j
  have hNcwP : ∀ i j, PConstructible (Ncw i j) := by
    intro i j
    rw [hNcw]
    exact aeval_entries_Pconstructible _ (companion7_entries_Pconstructible hq) _
      (polyOfVec_coeff_Pconstructible cw hcwP) i j
  have hA : PConstructible (p3vec q cv) := by
    rw [p3vec, ← hNcv]; exact trace_pow_Pconstructible hNcvP 3
  have hDc : PConstructible (p3vec q cw) := by
    rw [p3vec, ← hNcw]; exact trace_pow_Pconstructible hNcwP 3
  have hB : PConstructible (3 * Matrix.trace (Ncv ^ 2 * Ncw)) :=
    PConstructible.mul (by pconstructible)
      (trace_mul_Pconstructible (matrix_pow_entries_Pconstructible hNcvP 2) hNcwP)
  have hC : PConstructible (3 * Matrix.trace (Ncv * Ncw ^ 2)) :=
    PConstructible.mul (by pconstructible)
      (trace_mul_Pconstructible hNcvP (matrix_pow_entries_Pconstructible hNcwP 2))
  obtain ⟨s, t, hsP, htP, _hstne, hcub⟩ :=
    binary_cubic_zero (a := p3vec q cv) (b := 3 * Matrix.trace (Ncv ^ 2 * Ncw))
      (c := 3 * Matrix.trace (Ncv * Ncw ^ 2)) (d := p3vec q cw) hA hB hC hDc
  set ψ : Fin 7 → ℝ := s • cv + t • cw with hψ
  have hψP : ∀ i, PConstructible (ψ i) := by
    intro i
    rw [hψ, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact PConstructible.add (PConstructible.mul hsP (hcvP i))
      (PConstructible.mul htP (hcwP i))
  have hψne : ψ ≠ 0 := by
    intro h0
    have hcomb : s • cv + t • cw = 0 := by rw [← hψ]; exact h0
    obtain ⟨hs0, ht0⟩ := smul_add_smul_eq_zero_of_not_parallel hcvne hindep' hcomb
    rcases _hstne with h | h
    · exact h hs0
    · exact h ht0
  refine ⟨polyOfVec ψ, polyOfVec_coeff_Pconstructible ψ hψP, polyOfVec_natDegree_le ψ,
    polyOfVec_ne_zero hψne, ?_, ?_, ?_⟩
  · rw [← p1vec_eq_trace, hψ, p1vec_smul_add, hp1v, hp1w]
    ring
  · rw [← hermiteForm_eq_trace_sq q ψ, ← qform_Hmat_eq_hermiteForm, hψ,
      qform_smul_add (Hmat q) (Hmat_symm q), hqformv, hbilinc, hqformw]
    ring
  · have haeval : aeval (companion7 q) (polyOfVec ψ) = s • Ncv + t • Ncw := by
      rw [hψ, aeval_polyOfVec_smul_add, hNcv, hNcw]
    have hAc : p3vec q cv = Matrix.trace (Ncv ^ 3) := by rw [p3vec, ← hNcv]
    have hDc' : p3vec q cw = Matrix.trace (Ncw ^ 3) := by rw [p3vec, ← hNcw]
    rw [haeval, trace_cube_smul_add]
    rw [hAc, hDc'] at hcub
    ring_nf at hcub ⊢
    linarith

end

end Pconstructible


/- ==================== inlined from Pptc.ScratchSep ==================== -/


open Polynomial

namespace Pconstructible

/-! ### Separability is free for the degree-7 problem

The `s ≥ 2` theorem `root_Pconstructible_of_two_conjugate_pairs` currently assumes
`q.Separable`, because the spectral identity that produces the Tschirnhaus map needs seven
distinct roots.  This file removes that hypothesis: a non-separable polynomial of degree at
most `7` has a repeated root, so its gcd with its derivative is nonconstant, and every real
root is a root of one of two polynomials of degree at most `6` (the gcd itself, or the exact
quotient of `q` by its monic normalization).  Both have P-constructible coefficients, so the
sextic engine `root_Pconstructible_le_six_coeffs` finishes.

The work is the coefficient constructibility of `gcd` and of division with remainder by a
monic polynomial, which is what the Euclidean algorithm is built from. -/

-- Theorem: the constant polynomial `C c` has P-constructible coefficients whenever `c` is
-- P-constructible.
theorem coeff_C_Pconstructible {c : ℝ} (hc : PConstructible c) (i : ℕ) :
    PConstructible ((Polynomial.C c).coeff i) := by
  rw [Polynomial.coeff_C]
  split_ifs with h
  · exact hc
  · exact zero_Pconstructible

-- Theorem: multiplying by `C c` with `c` P-constructible preserves coefficient
-- P-constructibility.
theorem C_mul_coeff_Pconstructible {c : ℝ} (hc : PConstructible c) {p : Polynomial ℝ}
    (hp : ∀ k, PConstructible (p.coeff k)) (i : ℕ) :
    PConstructible ((Polynomial.C c * p).coeff i) := by
  rw [Polynomial.coeff_C_mul]
  exact PConstructible.mul hc (hp i)

-- Theorem: a product of polynomials all of whose coefficients are P-constructible again
-- has P-constructible coefficients.
theorem coeff_mul_Pconstructible {p q : Polynomial ℝ}
    (hp : ∀ i, PConstructible (p.coeff i)) (hq : ∀ i, PConstructible (q.coeff i))
    (n : ℕ) : PConstructible ((p * q).coeff n) := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun x _ => ?_)
  exact PConstructible.mul (hp x.1) (hq x.2)

-- Theorem: if `d` is monic with P-constructible coefficients, then both the quotient and
-- the remainder of any P-constructible `p` by `d` have P-constructible coefficients.
--
-- The proof is strong induction on `p.natDegree`.  In the recursive step one removes the
-- leading term of `p` with `z = C (leadingCoeff p) * X ^ (natDegree p - natDegree d)`, so
-- that `p' = p - d * z` has strictly smaller degree; the quotient and remainder of `p` are
-- then `z + p' /ₘ d` and `p' %ₘ d` by `div_modByMonic_unique`.  The case `d = 1` is handled
-- separately because then `p'` can equal `0` without the degree dropping.
theorem divModByMonic_coeff_Pconstructible {d : Polynomial ℝ} (hd : d.Monic)
    (hdc : ∀ i, PConstructible (d.coeff i)) :
    ∀ p, (∀ i, PConstructible (p.coeff i)) →
      (∀ i, PConstructible ((p /ₘ d).coeff i)) ∧
      (∀ i, PConstructible ((p %ₘ d).coeff i)) := by
  by_cases hd1 : d = 1
  · subst hd1
    intro p hp
    refine ⟨?_, ?_⟩
    · simpa using hp
    · intro i
      rw [Polynomial.modByMonic_one, Polynomial.coeff_zero]
      exact zero_Pconstructible
  · have hdne : d ≠ 0 := hd.ne_zero
    have hdpos : 0 < d.natDegree := by
      rcases Nat.eq_zero_or_pos d.natDegree with h | h
      · exact absurd (Polynomial.eq_one_of_monic_natDegree_zero hd h) hd1
      · exact h
    have hddegpos : (0 : WithBot ℕ) < d.degree := by
      rw [Polynomial.degree_eq_natDegree hdne]
      exact WithBot.coe_lt_coe.mpr hdpos
    intro p hp
    suffices H : ∀ n, ∀ p, p.natDegree = n → (∀ i, PConstructible (p.coeff i)) →
        (∀ i, PConstructible ((p /ₘ d).coeff i)) ∧
        (∀ i, PConstructible ((p %ₘ d).coeff i)) from H p.natDegree p rfl hp
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hpdeg hp
      by_cases hlt : p.degree < d.degree
      · have hdiv0 : p /ₘ d = 0 := (Polynomial.divByMonic_eq_zero_iff hd).mpr hlt
        have hmodp : p %ₘ d = p := (Polynomial.modByMonic_eq_self_iff hd).mpr hlt
        exact ⟨fun i => by rw [hdiv0, Polynomial.coeff_zero]; exact zero_Pconstructible,
          fun i => by rw [hmodp]; exact hp i⟩
      · have hge : d.degree ≤ p.degree := not_lt.mp hlt
        have hpdegpos : (0 : WithBot ℕ) < p.degree := lt_of_lt_of_le hddegpos hge
        have hpne : p ≠ 0 := by
          intro h0
          rw [h0, Polynomial.degree_zero] at hpdegpos
          exact absurd hpdegpos (not_lt_of_ge bot_le)
        set z : Polynomial ℝ :=
          Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - d.natDegree)
          with hzdef
        set pp : Polynomial ℝ := p - d * z with hppdef
        have hzcoeff : ∀ i, PConstructible (z.coeff i) := by
          intro i
          rw [hzdef, Polynomial.coeff_C_mul_X_pow]
          split_ifs with h
          · exact hp p.natDegree
          · exact zero_Pconstructible
        have hppcoeff : ∀ i, PConstructible (pp.coeff i) := by
          intro i
          rw [hppdef, Polynomial.coeff_sub]
          exact PConstructible.sub (hp i) (coeff_mul_Pconstructible hdc hzcoeff i)
        have hppdeg : pp.degree < p.degree := by
          rw [hppdef, hzdef]
          exact Polynomial.div_wf_lemma ⟨hge, hpne⟩ hd
        have hpplt : pp.natDegree < p.natDegree := by
          rcases eq_or_ne pp 0 with h0 | h0
          · rw [h0, Polynomial.natDegree_zero]
            exact Polynomial.natDegree_pos_iff_degree_pos.mpr hpdegpos
          · exact Polynomial.natDegree_lt_natDegree h0 hppdeg
        obtain ⟨hq', hr'⟩ := ih pp.natDegree (hpdeg ▸ hpplt) pp rfl hppcoeff
        have hkey : p /ₘ d = z + pp /ₘ d ∧ p %ₘ d = pp %ₘ d :=
          Polynomial.div_modByMonic_unique (z + pp /ₘ d) (pp %ₘ d) hd
            ⟨?_, Polynomial.degree_modByMonic_lt pp hd⟩
        · exact ⟨fun i => by
              rw [hkey.1, Polynomial.coeff_add]
              exact PConstructible.add (hzcoeff i) (hq' i),
            fun i => by rw [hkey.2]; exact hr' i⟩
        · have hmid : pp %ₘ d + d * (pp /ₘ d) = pp := Polynomial.modByMonic_add_div pp d
          calc pp %ₘ d + d * (z + pp /ₘ d)
              = (pp %ₘ d + d * (pp /ₘ d)) + d * z := by ring
            _ = pp + d * z := by rw [hmid]
            _ = p := by rw [hppdef]; ring

-- Theorem: the remainder of a P-constructible polynomial modulo a monic P-constructible one
-- has P-constructible coefficients.
theorem modByMonic_coeff_Pconstructible {d : Polynomial ℝ} (hd : d.Monic)
    (hdc : ∀ i, PConstructible (d.coeff i)) {p : Polynomial ℝ}
    (hp : ∀ i, PConstructible (p.coeff i)) :
    ∀ i, PConstructible ((p %ₘ d).coeff i) :=
  (divModByMonic_coeff_Pconstructible hd hdc p hp).2

-- Theorem: the gcd of two polynomials with P-constructible coefficients has
-- P-constructible coefficients.  This follows the Euclidean recursion `gcd a b = if a = 0
-- then b else gcd (b % a) a` (`EuclideanDomain.GCD.induction`), using that the remainder
-- `b % a = b %ₘ (a * C a.leadingCoeff⁻¹)` is division by a monic polynomial.
theorem gcd_coeff_Pconstructible (a b : Polynomial ℝ)
    (ha : ∀ i, PConstructible (a.coeff i)) (hb : ∀ i, PConstructible (b.coeff i)) :
    ∀ i, PConstructible ((EuclideanDomain.gcd a b).coeff i) := by
  revert ha hb
  refine EuclideanDomain.GCD.induction a b ?_ ?_
  · intro x _ hx i
    rw [EuclideanDomain.gcd_zero_left]
    exact hx i
  · intro a b ha0 ih ha hb i
    rw [EuclideanDomain.gcd_val]
    refine ih ?_ ha i
    intro j
    rw [Polynomial.mod_def]
    refine modByMonic_coeff_Pconstructible
      (Polynomial.monic_mul_leadingCoeff_inv ha0) ?_ hb j
    intro k
    exact coeff_mul_Pconstructible ha
      (fun l => coeff_C_Pconstructible (inv_Pconstructible (ha a.natDegree)) l) k

/-! ### The non-separable case of the septic problem

If `q` is a monic polynomial of degree at most `7` that is not separable, then it has a
repeated root and `gcd q q'` is nonconstant.  Every real root of `q` is either a root of
`d := gcd q q'` (degree `≤ 6` because `d ∣ q'`) or of the quotient `q / d`, and the quotient
also has degree `≤ 6` because `d` is nonconstant.  Since `d` can be normalised to a monic
polynomial `d₀` without changing its degree or root set and the quotient by `d₀` still has
degree `≤ 6`, the sextic engine applies in either branch. -/

-- Theorem: a non-separable monic polynomial `q` of degree at most `7` with P-constructible
-- coefficients has P-constructible real roots.
theorem root_Pconstructible_of_nonSeparable {q : Polynomial ℝ} (hmon : q.Monic)
    (hcoeff : ∀ k, PConstructible (q.coeff k)) (hdeg : q.natDegree ≤ 7)
    (hns : ¬ q.Separable) {β : ℝ} (hβ : q.eval β = 0) : PConstructible β := by
  have hq0 : q ≠ 0 := hmon.ne_zero
  have hnat_ne : q.natDegree ≠ 0 := by
    intro h0
    exact hns (by
      rw [Polynomial.eq_one_of_monic_natDegree_zero hmon h0]
      exact Polynomial.separable_one)
  have hderiv_ne : q.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hnat_ne
  have hdcoeff : ∀ i, PConstructible (q.derivative.coeff i) := by
    intro i
    rw [Polynomial.coeff_derivative]
    exact PConstructible.mul (hcoeff (i + 1))
      (PConstructible.add (nat_Pconstructible i) PConstructible.base_one)
  set d : Polynomial ℝ := EuclideanDomain.gcd q q.derivative with hddef
  have hdcoeffd : ∀ i, PConstructible (d.coeff i) := by
    rw [hddef]
    exact gcd_coeff_Pconstructible q q.derivative hcoeff hdcoeff
  have hdvd_q : d ∣ q := by
    rw [hddef]; exact EuclideanDomain.gcd_dvd_left q q.derivative
  have hdvd_dq : d ∣ q.derivative := by
    rw [hddef]; exact EuclideanDomain.gcd_dvd_right q q.derivative
  have hdne : d ≠ 0 := by
    rw [hddef]
    intro hzero
    exact hq0 ((EuclideanDomain.gcd_eq_zero_iff).mp hzero).1
  have hddeg : d.natDegree ≤ 6 := by
    have hderiv_deg : q.derivative.natDegree ≤ 6 := by
      have := Polynomial.natDegree_derivative_le q
      omega
    rw [hddef]
    exact le_trans
      (Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right q q.derivative)
        hderiv_ne) hderiv_deg
  have hdpos : 0 < d.natDegree := by
    have hnotunit : ¬ IsUnit d := by
      intro hu
      rw [hddef] at hu
      exact hns ((Polynomial.separable_def q).mpr (EuclideanDomain.gcd_isUnit_iff.mp hu))
    rw [Polynomial.isUnit_iff_degree_eq_zero] at hnotunit
    apply Nat.pos_of_ne_zero
    intro h0
    exact hnotunit (by simp [Polynomial.degree_eq_natDegree hdne, h0])
  have hlc_ne : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hdne
  have hlc_inv_ne : d.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero hlc_ne
  set d0 : Polynomial ℝ := d * Polynomial.C d.leadingCoeff⁻¹ with hd0def
  have hd0monic : d0.Monic := by
    rw [hd0def]; exact Polynomial.monic_mul_leadingCoeff_inv hdne
  have hd0coeff : ∀ i, PConstructible (d0.coeff i) := by
    intro i
    rw [hd0def]
    exact coeff_mul_Pconstructible hdcoeffd
      (fun j => coeff_C_Pconstructible (inv_Pconstructible (hdcoeffd d.natDegree)) j) i
  have hd0ne : d0 ≠ 0 := by
    rw [hd0def]
    exact mul_ne_zero hdne (Polynomial.C_ne_zero.mpr hlc_inv_ne)
  have hd0nat : d0.natDegree = d.natDegree := by
    rw [hd0def]
    exact Polynomial.natDegree_mul_C hlc_inv_ne
  have hd0deg : d0.natDegree ≤ 6 := by rw [hd0nat]; exact hddeg
  have hd0pos : 1 ≤ d0.natDegree := by rw [hd0nat]; omega
  by_cases hd0β : d0.eval β = 0
  · exact root_Pconstructible_le_six_coeffs hd0ne hd0deg hd0coeff hd0β
  · have h0dvd_d : d0 ∣ d := ⟨Polynomial.C d.leadingCoeff, by
        rw [hd0def, mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlc_ne,
          Polynomial.C_1, mul_one]⟩
    have h0dvd_q : d0 ∣ q := dvd_trans h0dvd_d hdvd_q
    have hq_eq : d0 * (q /ₘ d0) = q := by
      have hmod0 : q %ₘ d0 = 0 :=
        (Polynomial.modByMonic_eq_zero_iff_dvd hd0monic).mpr h0dvd_q
      have h := Polynomial.modByMonic_add_div q d0
      rw [hmod0, zero_add] at h
      exact h
    have hrcoeff : ∀ i, PConstructible ((q /ₘ d0).coeff i) :=
      fun i => (divModByMonic_coeff_Pconstructible hd0monic hd0coeff q hcoeff).1 i
    have hrdeg : (q /ₘ d0).natDegree ≤ 6 := by
      rw [Polynomial.natDegree_divByMonic q hd0monic]
      omega
    have hrne : q /ₘ d0 ≠ 0 := by
      intro h0
      have : q = 0 := by rw [← hq_eq, h0, mul_zero]
      exact hq0 this
    have hrβ : (q /ₘ d0).eval β = 0 := by
      have h := congrArg (fun p : Polynomial ℝ => p.eval β) hq_eq
      rw [Polynomial.eval_mul, hβ] at h
      exact (mul_eq_zero.mp h).resolve_left hd0β
    exact root_Pconstructible_le_six_coeffs hrne hrdeg hrcoeff hrβ

end Pconstructible


/- ==================== inlined from Pptc.DegreeSeven ==================== -/


open Polynomial Matrix


namespace Pconstructible

/-! ### The recovery step, isolated

Whatever eventually produces the value `y = φ β` of a degree-`≤ 6` Tschirnhaus map `φ`,
recovering `β` from it is always degree `≤ 6`: `β` is a root of `φ - C y`, which has the
same coefficients as `φ` except at `X ^ 0` and so is still P-constructible whenever `φ`
is. This is the last row of the issue's table, and it is unconditional. -/

-- Theorem: a nonconstant polynomial `φ` of degree at most 6 with P-constructible
-- coefficients has P-constructible roots over P-constructible values: if `φ β = y` and
-- `y` is P-constructible, then `β` is P-constructible.
theorem eval_root_Pconstructible {φ : Polynomial ℝ}
    (hcoeff : ∀ i, PConstructible (φ.coeff i)) (hdeg : φ.natDegree ≤ 6)
    (hne : φ.natDegree ≠ 0) {β y : ℝ} (hy : PConstructible y)
    (h : φ.eval β = y) :
    PConstructible β := by
  set ψ : Polynomial ℝ := φ - Polynomial.C y with hψ
  have hψcoeff : ∀ i, PConstructible (ψ.coeff i) := by
    intro i
    rw [hψ, Polynomial.coeff_sub]
    by_cases hi : i = 0
    · subst hi
      simp only [Polynomial.coeff_C, if_pos]
      exact PConstructible.sub (hcoeff 0) hy
    · simp only [Polynomial.coeff_C, if_neg hi, sub_zero]
      exact hcoeff i
  have hψdeg : ψ.natDegree ≤ 6 := by
    rw [hψ]
    refine le_trans (Polynomial.natDegree_sub_le φ (Polynomial.C y)) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hdeg
  have hψne : ψ ≠ 0 := by
    intro h0
    have hC : φ = Polynomial.C y := by rw [hψ, sub_eq_zero] at h0; exact h0
    rw [hC, Polynomial.natDegree_C] at hne
    exact hne rfl
  have hψroot : ψ.eval β = 0 := by
    rw [hψ, Polynomial.eval_sub, Polynomial.eval_C, h, sub_self]
  exact root_Pconstructible_le_six_coeffs hψne hψdeg hψcoeff hψroot

-- Theorem: the two steps that finish a degree-7 reduction once the Tschirnhaus map `φ`
-- and its power-law relation are in hand. If `φ` has P-constructible coefficients and
-- degree between `1` and `6`, and `y = φ β` satisfies `y ^ 7 = cubicVal c₀ c₁ c₂ c₃ y`
-- with P-constructible cubic coefficients, then `β` is P-constructible: first the
-- power-law engine makes `y` P-constructible, then `eval_root_Pconstructible` recovers
-- `β` from `φ - C y`.
theorem root_Pconstructible_of_powerLaw {φ : Polynomial ℝ}
    (hcoeff : ∀ i, PConstructible (φ.coeff i)) (hdeg : φ.natDegree ≤ 6)
    (hne : φ.natDegree ≠ 0) {β c₀ c₁ c₂ c₃ : ℝ}
    (h₀ : PConstructible c₀) (h₁ : PConstructible c₁) (h₂ : PConstructible c₂)
    (h₃ : PConstructible c₃)
    (h : (φ.eval β) ^ 7 = cubicVal c₀ c₁ c₂ c₃ (φ.eval β)) :
    PConstructible β :=
  eval_root_Pconstructible hcoeff hdeg hne
    (powerLaw_cubic_root_Pconstructible (by norm_num) h₀ h₁ h₂ h₃ h) rfl

/-! ### The isotropic-vector step, in the scalar form the construction uses

The constructive route the issue asks for works on the *line* joining a direction `v` on
which the trace form is negative to a direction `u` on which it is positive. Along
`v + t u` the form is the quadratic `a t² + 2 b t + c` with `a = p₂ u > 0` and `c = p₂ v <
0`, so it crosses zero at a positive `t` given by the quadratic formula. That root involves
only a square root of a rational function of `a, b, c`, and is therefore P-constructible as
soon as `a, b, c` are. This is the step labelled "diagonalise an indefinite real quadratic
form and read off an isotropic vector — square roots only" in the issue. -/

-- Theorem: a real quadratic `a t² + 2 b t + c` with positive leading coefficient `a` and
-- negative constant term `c` has a positive, P-constructible root whenever `a, b, c` are
-- P-constructible.
theorem exists_pos_quadratic_root {a b c : ℝ} (ha : PConstructible a)
    (hb : PConstructible b) (hc : PConstructible c) (hapos : 0 < a) (hcneg : c < 0) :
    ∃ t : ℝ, PConstructible t ∧ 0 < t ∧ a * t ^ 2 + 2 * b * t + c = 0 := by
  have hD : 0 < b ^ 2 - a * c := by nlinarith [sq_nonneg b, mul_pos hapos (neg_pos.mpr hcneg)]
  have hs : PConstructible (Real.sqrt (b ^ 2 - a * c)) :=
    sqrt_Pconstructible (PConstructible.sub (sq_Pconstructible hb) (PConstructible.mul ha hc))
  refine ⟨(-b + Real.sqrt (b ^ 2 - a * c)) / a, ?_, ?_, ?_⟩
  · exact PConstructible.div (PConstructible.add (neg_Pconstructible hb) hs) ha
  · have hb2 : b ^ 2 < b ^ 2 - a * c := by
      nlinarith [mul_pos hapos (neg_pos.mpr hcneg)]
    have habs : |b| < Real.sqrt (b ^ 2 - a * c) := by
      calc |b| = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
        _ < Real.sqrt (b ^ 2 - a * c) := Real.sqrt_lt_sqrt (sq_nonneg b) hb2
    have hnum : 0 < -b + Real.sqrt (b ^ 2 - a * c) := by
      have := (abs_lt.mp habs).2
      linarith
    exact div_pos hnum hapos
  · have hsq : Real.sqrt (b ^ 2 - a * c) ^ 2 = b ^ 2 - a * c := Real.sq_sqrt hD.le
    have hane : a ≠ 0 := ne_of_gt hapos
    field_simp
    linear_combination hsq

/-! ### The `s ≥ 2` case: the Bring–Jerrard reduction is constructible

The algebraic engine is in `Pptc.ScratchS` (`exists_tschirnhaus_traces`) and
`Pptc.ScratchN` (`charpoly_aeval_coeff_6_5_4_eq_zero`): from two non-real roots in distinct
conjugate classes, a degree-`≤ 6` Tschirnhaus map `φ` with P-constructible coefficients and
vanishing first three trace power sums is produced, and its resolvent loses the `X⁶, X⁵, X⁴`
terms.  `resolvent_powerLaw` then gives the power-law relation `(φ β)⁷ = cubic…`, whose root
`φ β` is P-constructible by `powerLaw_cubic_root_Pconstructible`; `φ - C (φ β)` finally
recovers `β`. -/

-- Theorem: if a nonzero polynomial `φ` has `trace (aeval (companion7 q) φ) = 0`, then `φ` is
-- nonconstant. If `φ` were the nonzero constant `C c`, the trace would be `7 c ≠ 0`.
theorem natDegree_ne_zero_of_trace_zero {q φ : ℝ[X]}
    (hp1 : Matrix.trace (aeval (companion7 q) φ) = 0) (hφne : φ ≠ 0) :
    φ.natDegree ≠ 0 := by
  intro hdeg0
  obtain ⟨c, hc⟩ := (Polynomial.natDegree_eq_zero).mp hdeg0
  have htrace : Matrix.trace (aeval (companion7 q) φ) = 7 * c := by
    rw [← hc, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul,
      Matrix.trace_one, smul_eq_mul]
    norm_num
    ring
  rw [htrace] at hp1
  have hc0 : c = 0 := by linarith
  rw [hc0, Polynomial.C_0] at hc
  exact hφne hc.symm

-- Theorem: a real root `β` of a monic septic `q` with P-constructible coefficients and two
-- non-real roots `z, w` in distinct conjugate classes is P-constructible. This is the `s ≥ 2`
-- case of issue #6.  Separability is not assumed: if `q` is not separable, either the
-- normalised `gcd q q'` or the quotient of `q` by it has degree at most `6` and kills `β`,
-- and the sextic engine already recovers `β` (`ScratchSep`); only the separable case goes
-- through the Bring–Jerrard reduction.
theorem root_Pconstructible_of_two_conjugate_pairs_monic {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 7) (hq : ∀ k, PConstructible (q.coeff k))
    {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β := by
  by_cases hsep : q.Separable
  · obtain ⟨φ, hφc, hφdeg, hφne, hp1, hp2, hp3⟩ :=
      exists_tschirnhaus_traces q hmon hnat hsep hq hz hzim hw hwim hzw hzw'
    have hkill := charpoly_aeval_coeff_6_5_4_eq_zero hmon hnat hsep hp1 hp2 hp3
    have h7 : q.coeff 7 = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
    have hdeg : q.natDegree ≤ 7 := le_of_eq hnat
    obtain ⟨c₀, c₁, c₂, c₃, hc₀, hc₁, hc₂, hc₃, hpow⟩ :=
      resolvent_powerLaw hq hβ h7 hdeg hφc hkill
    exact root_Pconstructible_of_powerLaw hφc hφdeg
      (natDegree_ne_zero_of_trace_zero hp1 hφne) hc₀ hc₁ hc₂ hc₃ hpow
  · exact root_Pconstructible_of_nonSeparable hmon hq (le_of_eq hnat) hsep hβ

end Pconstructible


/- ==================== inlined from Pptc.DegreeSevenOnePair ==================== -/


open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! # The one-conjugate-pair case of degree 7 (issue #6)

Implementation of `PLAN-degree7-s1.md`.  The route parametrises the light cone
`{p₂ = 0}` stereographically from a P-constructible cone point `P₀`, uses the
conjugation symmetry `σ` (only in the proof, never as a construction) to certify that
the reduced cubic changes sign on the cone, then rounds the witnesses to rational
directions and reads off a root of the resulting sextic with the sextic engine.

Sections A–E1 below are the independent algebraic/analytic pieces. -/

/-! ### A. The Tschirnhaus tail, factored out

Once a degree-`≤ 6` Tschirnhaus map `φ` with P-constructible coefficients and vanishing
first three trace power sums is in hand, the root `β` follows from the resolvent power
law.  This is exactly the tail of `root_Pconstructible_of_two_conjugate_pairs_monic`,
isolated so the `s = 1` construction can reuse it. -/

-- Theorem: a real root `β` of a monic separable septic `q` with P-constructible
-- coefficients is P-constructible, provided there is a nonzero degree-`≤ 6` polynomial `φ`
-- with P-constructible coefficients whose first three trace power sums at `companion7 q`
-- vanish.
theorem root_Pconstructible_of_tschirnhaus {q φ : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 7) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    (hφc : ∀ k, PConstructible (φ.coeff k)) (hφdeg : φ.natDegree ≤ 6) (hφne : φ ≠ 0)
    (hp1 : Matrix.trace (aeval (companion7 q) φ) = 0)
    (hp2 : Matrix.trace ((aeval (companion7 q) φ) ^ 2) = 0)
    (hp3 : Matrix.trace ((aeval (companion7 q) φ) ^ 3) = 0)
    {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β := by
  have hkill := charpoly_aeval_coeff_6_5_4_eq_zero hmon hnat hsep hp1 hp2 hp3
  have h7 : q.coeff 7 = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ 7 := le_of_eq hnat
  obtain ⟨c₀, c₁, c₂, c₃, hc₀, hc₁, hc₂, hc₃, hpow⟩ :=
    resolvent_powerLaw hq hβ h7 hdeg hφc hkill
  exact root_Pconstructible_of_powerLaw hφc hφdeg
    (natDegree_ne_zero_of_trace_zero hp1 hφne) hc₀ hc₁ hc₂ hc₃ hpow

/-! ### C. The stereographic parametrisation of the light cone

For a vector `x` on the cone `{Q = 0}` through `P₀`, the second intersection of the line
`P₀ + t x` with the cone is `v x / Q x`, where
`v x = Q x • P₀ - 2 B P₀ x • x`.  No square root is needed because the `t = 0` root is
already known. -/

/-- The second intersection of the cone through `P₀` with the line `P₀ + t x`, scaled by
`Q x`: `Q x • P₀ - 2 B P₀ x • x`. -/
def stereo (A : Matrix (Fin 6) (Fin 6) ℝ) (P₀ x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  qform A x • P₀ - (2 * bilin A P₀ x) • x

-- Theorem (S1): `stereo` always lands on the cone.
theorem qform_stereo_eq_zero {A : Matrix (Fin 6) (Fin 6) ℝ} (hA : Aᵀ = A)
    {P₀ : Fin 6 → ℝ} (hP₀ : qform A P₀ = 0) (x : Fin 6 → ℝ) :
    qform A (stereo A P₀ x) = 0 := by
  rw [show stereo A P₀ x = qform A x • P₀ + (-(2 * bilin A P₀ x)) • x by
    rw [stereo, sub_eq_add_neg, ← neg_smul]]
  rw [qform_smul_add A hA (qform A x) (-(2 * bilin A P₀ x)) P₀ x]
  simp only [hP₀, mul_zero, zero_add]
  ring

-- Theorem (S2): `stereo` vanishes to order two along the ray of `P₀`: shifting `δ` by any
-- multiple of `P₀` only rescales `stereo`.
theorem stereo_smul_add_smul {A : Matrix (Fin 6) (Fin 6) ℝ} (hA : Aᵀ = A)
    {P₀ : Fin 6 → ℝ} (hP₀ : qform A P₀ = 0) (c ε : ℝ) (δ : Fin 6 → ℝ) :
    stereo A P₀ (c • P₀ + ε • δ) = ε ^ 2 • stereo A P₀ δ := by
  have hBsym : bilin A P₀ P₀ = 0 := by
    rw [show bilin A P₀ P₀ = qform A P₀ from rfl, hP₀]
  have hQx : qform A (c • P₀ + ε • δ) = 2 * c * ε * bilin A P₀ δ + ε ^ 2 * qform A δ := by
    rw [qform_smul_add A hA c ε P₀ δ, hP₀]
    ring
  have hBx : bilin A P₀ (c • P₀ + ε • δ) = ε * bilin A P₀ δ := by
    rw [bilin_add_right, bilin_smul_right, bilin_smul_right, hBsym]
    ring
  rw [show stereo A P₀ (c • P₀ + ε • δ)
      = qform A (c • P₀ + ε • δ) • P₀
        + (-(2 * bilin A P₀ (c • P₀ + ε • δ))) • (c • P₀ + ε • δ) by
    rw [stereo, sub_eq_add_neg, ← neg_smul]]
  rw [hQx, hBx]
  rw [show stereo A P₀ δ
      = qform A δ • P₀ + (-(2 * bilin A P₀ δ)) • δ by
    rw [stereo, sub_eq_add_neg, ← neg_smul]]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

-- Theorem: `p3vec` is homogeneous of degree three.
theorem p3vec_smul (q : ℝ[X]) (c : ℝ) (x : Fin 7 → ℝ) :
    p3vec q (c • x) = c ^ 3 * p3vec q x := by
  rw [p3vec, p3vec]
  have h : aeval (companion7 q) (polyOfVec (c • x))
      = c • aeval (companion7 q) (polyOfVec x) := by
    have := aeval_polyOfVec_smul_add q c 0 x 0
    simpa using this
  rw [h, smul_pow, Matrix.trace_smul, smul_eq_mul]

-- Theorem (S3): on the cone, `stereo` is a scalar multiple of `x`, and the reduced cubic
-- scales by the cube of that multiple: `Cf (stereo x) = -8 (B P₀ x)^3 Cf x`.
theorem p3vec_Lcomb_stereo_of_qform_zero (q : ℝ[X]) {P₀ x : Fin 6 → ℝ}
    (hx : qform (Gram q) x = 0) :
    p3vec q (Lcomb q (stereo (Gram q) P₀ x))
      = -8 * (bilin (Gram q) P₀ x) ^ 3 * p3vec q (Lcomb q x) := by
  have hvec : stereo (Gram q) P₀ x = (-2 * bilin (Gram q) P₀ x) • x := by
    rw [stereo, hx]
    module
  rw [hvec, Lcomb_smul, p3vec_smul]
  ring

/-! ### B. The triple-sum formula and continuity of the cubic

`p3vec q w = trace ((aeval M (polyOfVec w)) ^ 3)` expands, in the monomial basis, into the
triple sum `∑ i j k wᵢ wⱼ wₖ trace (M ^ (i + j + k))`.  This makes `p3vec` a polynomial
function of `w`, hence continuous, and is the bridge that turns the parametrised cone into a
sextic in the line parameter. -/

-- Theorem: `p3vec` is the triple sum of `wᵢ wⱼ wₖ trace (M ^ (i + j + k))`.
theorem p3vec_eq_sum (q : ℝ[X]) (w : Fin 7 → ℝ) :
    p3vec q w = ∑ i, ∑ j, ∑ k,
      w i * w j * w k
        * Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val)) := by
  have hcube : (aeval (companion7 q) (polyOfVec w)) ^ 3 =
      ∑ i, ∑ j, ∑ k, (w i * w j * w k) •
        (companion7 q) ^ (i.val + j.val + k.val) := by
    rw [pow_succ, aeval_polyOfVec_sq, aeval_polyOfVec]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]
  rw [p3vec, hcube, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul]

-- Theorem: `p3vec` is continuous in its vector argument.
theorem continuous_p3vec (q : ℝ[X]) : Continuous (p3vec q) := by
  rw [show p3vec q = fun w : Fin 7 → ℝ => ∑ i, ∑ j, ∑ k,
      w i * w j * w k
        * Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val)) from
    funext (p3vec_eq_sum q)]
  fun_prop

/-! ### D. A P-constructible cone point

Given P-constructible directions `e` (negative) and `f` (positive) for the trace form,
the light cone meets the segment between them at a P-constructible point `P₀`. -/

-- Theorem: if `e` is P-constructible with `Q e < 0` and `f` is P-constructible with
-- `Q f > 0`, then the cone `{Q = 0}` contains a P-constructible nonzero point, namely the
-- second intersection of the line `e + t f` with the cone.
theorem exists_isotropic_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {e f : Fin 6 → ℝ} (he : ∀ i, PConstructible (e i)) (hf : ∀ i, PConstructible (f i))
    (heQ : qform (Gram q) e < 0) (hfQ : 0 < qform (Gram q) f) :
    ∃ P₀ : Fin 6 → ℝ,
      (∀ i, PConstructible (P₀ i)) ∧ qform (Gram q) P₀ = 0 ∧ P₀ ≠ 0 := by
  have hG : ∀ i j, PConstructible (Gram q i j) := Gram_Pconstructible q hq
  have hQe : PConstructible (qform (Gram q) e) := bilin_Pconstructible hG he he
  have hQf : PConstructible (qform (Gram q) f) := bilin_Pconstructible hG hf hf
  have hB : PConstructible (bilin (Gram q) e f) := bilin_Pconstructible hG he hf
  obtain ⟨t, htP, htpos, htroot⟩ := exists_pos_quadratic_root hQf hB hQe hfQ heQ
  refine ⟨e + t • f, ?_, ?_, ?_⟩
  · intro i
    exact PConstructible.add (he i) (PConstructible.mul htP (hf i))
  · have hqform : qform (Gram q) (e + t • f) =
        qform (Gram q) e + 2 * t * bilin (Gram q) e f + t ^ 2 * qform (Gram q) f := by
      rw [show e + t • f = (1 : ℝ) • e + t • f by rw [one_smul]]
      rw [qform_smul_add (Gram q) (Gram_symm q) 1 t e f]
      ring
    rw [hqform]
    linear_combination htroot
  · intro h0
    have heq : e = -(t • f) := eq_neg_of_add_eq_zero_left h0
    have hQe' : qform (Gram q) (-(t • f)) < 0 := by rw [← heq]; exact heQ
    have hneg : qform (Gram q) (-(t • f)) = qform (Gram q) (t • f) := by
      rw [show -(t • f) = (-1 : ℝ) • (t • f) by rw [neg_one_smul], qform_smul]
      norm_num
    rw [hneg, qform_smul] at hQe'
    nlinarith [hfQ, sq_pos_of_pos htpos]

/-! ### E1. Rational witnesses by density

The sign certificate only shows that some direction gives `Φ` a given sign; density of
`ℚⁿ` in `ℝⁿ` then supplies a rational (hence P-constructible) direction with the same
strict sign. -/

-- Theorem: a continuous function positive at one point is positive at a rational vector.
theorem exists_rat_vec_pos (n : ℕ) {g : (Fin n → ℝ) → ℝ} (hg : Continuous g)
    {x : Fin n → ℝ} (hx : 0 < g x) :
    ∃ r : Fin n → ℚ, 0 < g (fun i => (r i : ℝ)) := by
  have hopen : IsOpen {y : Fin n → ℝ | 0 < g y} := isOpen_lt continuous_const hg
  have hne : ({y : Fin n → ℝ | 0 < g y}).Nonempty := ⟨x, hx⟩
  have hdense : Dense (Set.range (fun r : Fin n → ℚ => fun i => (r i : ℝ))) :=
    DenseRange.piMap (fun _ : Fin n => (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)))
  obtain ⟨y, hys, hyU⟩ := hdense.exists_mem_open hopen hne
  obtain ⟨r, rfl⟩ := hys
  exact ⟨r, hyU⟩

end

end Pconstructible


/- ==================== inlined from Pptc.S1Roots ==================== -/


open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### F1. The root decomposition of a septic with one conjugate pair

For a monic separable real septic `q` whose only non-real roots are `z` and `z̄`, the
complex roots split as `z`, `z̄`, and the images of five distinct real roots.  The real
roots are collected as a `Multiset ℝ` by filtering the complex roots on `im = 0` and
reading off `.re`. -/

-- Theorem: under `hsep` and `hone`, the roots of `q` over `ℂ` are `z`, `z̄` and the five
-- real roots, which form a nodup `Multiset ℝ` of cardinality five.
theorem roots_eq_pair_add_real {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z) :
    ∃ R : Multiset ℝ, R.Nodup ∧ R.card = 5 ∧
      (q.map (algebraMap ℝ ℂ)).roots
        = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)) := by
  classical
  set qC : ℂ[X] := q.map (algebraMap ℝ ℂ) with hqC
  have hqCne : qC ≠ 0 := by rw [hqC]; exact (hmon.map _).ne_zero
  have hnodup : qC.roots.Nodup := by
    rw [hqC]; exact Polynomial.nodup_roots (hsep.map)
  have hcard : qC.roots.card = 7 := by
    rw [show qC.roots.card = qC.natDegree from
      (IsAlgClosed.splits qC).natDegree_eq_card_roots.symm]
    rw [hqC, Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, hnat]
  have hzmem : z ∈ qC.roots := by
    rw [hqC] at hz ⊢; exact (Polynomial.mem_roots hqCne).mpr hz
  have hzbar : starRingEnd ℂ z ∈ qC.roots := by
    refine (Polynomial.mem_roots hqCne).mpr ?_
    rw [Polynomial.IsRoot, hqC]
    rw [eval_map_conj q z, hz, map_zero]
  have hzbarim : (starRingEnd ℂ z).im ≠ 0 := by
    change -z.im ≠ 0
    exact neg_ne_zero.mpr hzim
  have hznez : z ≠ starRingEnd ℂ z := by
    intro h
    exact hzim (Complex.conj_eq_iff_im.mp h.symm)
  set nonR : Multiset ℂ := qC.roots.filter (fun w => w.im ≠ 0) with hnonR
  set realC : Multiset ℂ := qC.roots.filter (fun w => w.im = 0) with hrealC
  have hsplit : realC + nonR = qC.roots := by
    have h := Multiset.filter_add_not (p := fun w : ℂ => w.im = 0) qC.roots
    rw [hrealC, hnonR]
    simpa using h
  have hnonR_eq : nonR = z ::ₘ starRingEnd ℂ z ::ₘ (0 : Multiset ℂ) := by
    have hnonRnodup : nonR.Nodup := by
      rw [hnonR]; exact hnodup.filter _
    have hpairnodup : (z ::ₘ starRingEnd ℂ z ::ₘ (0 : Multiset ℂ)).Nodup := by
      simp [Multiset.nodup_cons, hznez]
    refine (Multiset.Nodup.ext hnonRnodup hpairnodup).mpr ?_
    intro w
    rw [hnonR]
    simp only [Multiset.mem_filter, Multiset.mem_cons, Multiset.notMem_zero, or_false]
    constructor
    · rintro ⟨hwr, hwim⟩
      have hroot : qC.eval w = 0 := (Polynomial.mem_roots hqCne).mp hwr
      exact hone w hroot hwim
    · rintro (h | h)
      · subst h; exact ⟨hzmem, hzim⟩
      · subst h; exact ⟨hzbar, hzbarim⟩
  set R : Multiset ℝ := realC.map (fun w => w.re) with hR
  have hRmap : R.map (algebraMap ℝ ℂ) = realC := by
    rw [hR, Multiset.map_map]
    nth_rewrite 2 [← Multiset.map_id realC]
    apply Multiset.map_congr rfl
    intro w hw
    have him : w.im = 0 := (Multiset.mem_filter.mp hw).2
    exact Complex.ext (by simp) (by simp [him])
  have hcardR : R.card = 5 := by
    have hnc : nonR.card = 2 := by rw [hnonR_eq]; simp
    have hsum : realC.card + nonR.card = qC.roots.card := by
      rw [← hsplit, Multiset.card_add]
    rw [hR, Multiset.card_map]
    omega
  have hRnodup : R.Nodup := by
    rw [hR]
    refine Multiset.Nodup.map_on ?_ (Multiset.Nodup.filter _ hnodup)
    intro a ha b hb hab
    have hai : a.im = 0 := (Multiset.mem_filter.mp ha).2
    have hbi : b.im = 0 := (Multiset.mem_filter.mp hb).2
    exact Complex.ext hab (by rw [hai, hbi])
  refine ⟨R, hRnodup, hcardR, ?_⟩
  rw [← hsplit, hnonR_eq, hRmap]
  rw [Multiset.add_cons, Multiset.add_cons, Multiset.add_zero]

end

end Pconstructible


/- ==================== inlined from Pptc.S1Cert ==================== -/


open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### The cubic certificate for the one-conjugate-pair septic

Given a monic separable real septic `q` with a single non-real conjugate pair `{z, z̄}` and a
prescribed complex value `c` with `c + c̄ = -1`, `c c̄ = 1`, we build a real polynomial `P` of
degree at most six whose values at `z`, `z̄` are `c`, `c̄`, which equals `1` at the chosen real
root `x` and vanishes at every other real root of `q`.  Because the non-real values sum to
`c^k + c̄^k` and the real ones contribute `1` for the root `x` and `0` elsewhere, the first
three trace power sums of `P(companion7 q)` are `0`, `0`, `3`.

The construction is the Lagrange base `L = (q'(x))⁻¹ · (q /ₘ (X - C x))`, normalised to `1`
at `x` and `0` at the other roots, corrected at `z` by `exists_poly_value_at_root`. -/

-- Theorem: for a monic separable septic `q` with one non-real conjugate pair `{z, z̄}` and a
-- complex `c` with `c + c̄ = -1`, `c c̄ = 1`, there is a real polynomial `P` of degree at most
-- six attaining `c`, `c̄` at `z`, `z̄`, equal to `1` at the real root `x`, vanishing at the
-- other real roots, and whose first three trace power sums at `companion7 q` are `0`, `0`, `3`.
theorem exists_lagrange_value {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {x : ℝ} (hx : q.eval x = 0) (hxz : (x : ℂ) ≠ z) (hxz' : (x : ℂ) ≠ starRingEnd ℂ z)
    {c : ℂ} (hc1 : c + starRingEnd ℂ c = -1) (hc2 : c * starRingEnd ℂ c = 1) :
    ∃ X : ℝ[X], X.natDegree ≤ 6 ∧
      (X.map (algebraMap ℝ ℂ)).eval z = c ∧
      (X.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = starRingEnd ℂ c ∧
      X.eval x = 1 ∧
      (∀ r : ℝ, q.eval r = 0 → r ≠ x → X.eval r = 0) ∧
      Matrix.trace (aeval (companion7 q) X) = 0 ∧
      Matrix.trace ((aeval (companion7 q) X) ^ 2) = 0 ∧
      Matrix.trace ((aeval (companion7 q) X) ^ 3) = 3 := by
  classical
  have hqCne : (q.map (algebraMap ℝ ℂ)) ≠ 0 := (hmon.map (algebraMap ℝ ℂ)).ne_zero
  have hxrootC : (q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hx, map_zero]
  have hxzC : (algebraMap ℝ ℂ x) ≠ z := by simpa using hxz
  have hxzC' : (algebraMap ℝ ℂ x) ≠ starRingEnd ℂ z := by simpa using hxz'
  -- Lagrange base at the real root `x`
  set m : ℝ[X] := Polynomial.X - C x with hm
  have hmmon : m.Monic := by rw [hm]; exact Polynomial.monic_X_sub_C x
  have hmdvd : m ∣ q := by
    rw [hm]
    exact (Polynomial.dvd_iff_isRoot).mpr hx
  have hmod : q %ₘ m = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hmmon).mpr hmdvd
  have hdiv : m * (q /ₘ m) = q := by
    have h := Polynomial.modByMonic_add_div q m
    rw [hmod, zero_add] at h
    exact h
  have hd : (q /ₘ m).eval x = q.derivative.eval x := by
    have h := congrArg (fun p : ℝ[X] => p.derivative.eval x) hdiv
    rw [Polynomial.derivative_mul, hm] at h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.derivative_X_sub_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_self, zero_mul, add_zero, one_mul] at h
    exact h
  have hdne : q.derivative.eval x ≠ 0 := by
    have h := hsep.aeval_derivative_ne_zero (x := x) (by simpa using hx)
    simpa using h
  set L : ℝ[X] := C ((q.derivative.eval x)⁻¹) * (q /ₘ m) with hL
  have hLdeg : L.natDegree ≤ 6 := by
    rw [hL]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_divByMonic q (Polynomial.monic_X_sub_C x),
      Polynomial.natDegree_X_sub_C, hnat]
  have hLx : L.eval x = 1 := by
    rw [hL, Polynomial.eval_mul, Polynomial.eval_C, hd, inv_mul_cancel₀ hdne]
  have hLother : ∀ r : ℝ, q.eval r = 0 → r ≠ x → L.eval r = 0 := by
    intro r hr hrx
    have hmr : m.eval r ≠ 0 := by
      rw [hm]
      simpa using sub_ne_zero.mpr hrx
    have hq0 : m.eval r * (q /ₘ m).eval r = 0 := by
      rw [← Polynomial.eval_mul, hdiv]
      exact hr
    have hdiv0 : (q /ₘ m).eval r = 0 := (mul_eq_zero.mp hq0).resolve_left hmr
    rw [hL, Polynomial.eval_mul, Polynomial.eval_C, hdiv0, mul_zero]
  -- correction at `z` via the Bring–Jerrard direction
  obtain ⟨A, hAdeg, hAz, hAzbar, hAother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hz hzim (c - (L.map (algebraMap ℝ ℂ)).eval z)
  set P : ℝ[X] := L + A with hP
  have hPdeg : P.natDegree ≤ 6 := by
    rw [hP]
    exact (Polynomial.natDegree_add_le L A).trans (max_le hLdeg hAdeg)
  have hPz : (P.map (algebraMap ℝ ℂ)).eval z = c := by
    rw [hP, Polynomial.map_add, Polynomial.eval_add, hAz]
    ring
  have hPzbar : (P.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = starRingEnd ℂ c := by
    rw [hP, Polynomial.map_add, Polynomial.eval_add, eval_map_conj L z, hAzbar, map_sub]
    ring
  have hPx : P.eval x = 1 := by
    have hAx : A.eval x = 0 := by
      have h := hAother (algebraMap ℝ ℂ x) hxrootC hxzC hxzC'
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply] at h
      exact (algebraMap ℝ ℂ).injective (by simpa using h)
    rw [hP, Polynomial.eval_add, hLx, hAx, add_zero]
  have hPother : ∀ r : ℝ, q.eval r = 0 → r ≠ x → P.eval r = 0 := by
    intro r hr hrx
    have hAr : A.eval r = 0 := by
      have hrC : (q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = 0 := by
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]
      have hrz : (algebraMap ℝ ℂ r) ≠ z := fun h => hzim (by rw [← h]; simp)
      have hrz' : (algebraMap ℝ ℂ r) ≠ starRingEnd ℂ z := fun h => by
        have hc := congrArg Complex.im h
        simp at hc
        exact hzim (by linarith)
      have h := hAother (algebraMap ℝ ℂ r) hrC hrz hrz'
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply] at h
      exact (algebraMap ℝ ℂ).injective (by simpa using h)
    rw [hP, Polynomial.eval_add, hLother r hr hrx, hAr, add_zero]
  -- the root multiset decomposes into the conjugate pair and the real roots
  obtain ⟨R, hRnodup, _hRcard, hroots⟩ :=
    roots_eq_pair_add_real hmon hnat hsep hz hzim hone
  have hxmemC : (algebraMap ℝ ℂ x) ∈ (q.map (algebraMap ℝ ℂ)).roots :=
    (Polynomial.mem_roots hqCne).mpr hxrootC
  have hxmemC' : (algebraMap ℝ ℂ x) ∈ R.map (algebraMap ℝ ℂ) := by
    have h := hxmemC
    rw [hroots] at h
    simp only [Multiset.mem_cons] at h
    rcases h with h | h | h
    · exact absurd h hxzC
    · exact absurd h hxzC'
    · exact h
  have hxmem : x ∈ R := by
    rwa [Multiset.mem_map_of_injective (algebraMap ℝ ℂ).injective] at hxmemC'
  have hRroot : ∀ r ∈ R, q.eval r = 0 := by
    intro r hr
    have hmemR : (algebraMap ℝ ℂ r) ∈ R.map (algebraMap ℝ ℂ) :=
      (Multiset.mem_map_of_injective (algebraMap ℝ ℂ).injective).mpr hr
    have hmem : (algebraMap ℝ ℂ r) ∈ (q.map (algebraMap ℝ ℂ)).roots := by
      rw [hroots]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hmemR)
    have hroot := (Polynomial.mem_roots hqCne).mp hmem
    change (q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = 0 at hroot
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply] at hroot
    exact (algebraMap ℝ ℂ).injective (by simpa using hroot)
  set S : Multiset ℝ := R.erase x with hS
  have hR_eq : R = x ::ₘ S := by
    rw [hS]
    exact (Multiset.cons_erase hxmem).symm
  have hS_mem : ∀ r ∈ S, r ∈ R.erase x := fun r hr => by rwa [hS] at hr
  have hS_root : ∀ r ∈ S, q.eval r = 0 := fun r hr =>
    hRroot r (hRnodup.mem_erase_iff.mp (hS_mem r hr)).2
  have hS_ne : ∀ r ∈ S, r ≠ x := fun r hr =>
    (hRnodup.mem_erase_iff.mp (hS_mem r hr)).1
  have hPeval : ∀ r ∈ S, P.eval r = 0 := fun r hr =>
    hPother r (hS_root r hr) (hS_ne r hr)
  -- power sum of `P` over the complex roots
  have hsum (k : ℕ) (hk : k ≠ 0) :
      ((q.map (algebraMap ℝ ℂ)).roots.map
        (fun w => ((P.map (algebraMap ℝ ℂ)).eval w) ^ k)).sum
        = c ^ k + (starRingEnd ℂ c) ^ k + 1 := by
    have hrest : ((R.map (algebraMap ℝ ℂ)).map
          (fun w => ((P.map (algebraMap ℝ ℂ)).eval w) ^ k)).sum = 1 := by
      rw [hR_eq, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons]
      have hhead : ((P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x)) ^ k = 1 := by
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hPx]
        simp
      have htail : ((S.map (algebraMap ℝ ℂ)).map
            (fun w => ((P.map (algebraMap ℝ ℂ)).eval w) ^ k)).sum = 0 := by
        have hmap0 : (S.map (algebraMap ℝ ℂ)).map
              (fun w => ((P.map (algebraMap ℝ ℂ)).eval w) ^ k)
            = S.map (fun _ => (0 : ℂ)) := by
          rw [Multiset.map_map]
          exact Multiset.map_congr rfl (fun r hr => by
            change ((P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r)) ^ k = (0 : ℂ)
            rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hPeval r hr]
            simp [zero_pow hk])
        rw [hmap0, Multiset.sum_map_zero]
      simp only [hhead, htail, add_zero]
    rw [hroots, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
    simp only [hPz, hPzbar, hrest]
    ring
  have ht1 : Matrix.trace (aeval (companion7 q) P) = 0 := by
    have h := companion7_trace_pow_aeval q P hmon hnat hsep 1
    rw [hsum 1 (by norm_num)] at h
    rw [pow_one] at h
    refine (algebraMap ℝ ℂ).injective ?_
    rw [h, map_zero]
    linear_combination hc1
  have ht2 : Matrix.trace ((aeval (companion7 q) P) ^ 2) = 0 := by
    have h := companion7_trace_pow_aeval q P hmon hnat hsep 2
    rw [hsum 2 (by norm_num)] at h
    refine (algebraMap ℝ ℂ).injective ?_
    rw [h, map_zero]
    linear_combination (c + starRingEnd ℂ c - 1) * hc1 - 2 * hc2
  have ht3 : Matrix.trace ((aeval (companion7 q) P) ^ 3) = 3 := by
    have h := companion7_trace_pow_aeval q P hmon hnat hsep 3
    rw [hsum 3 (by norm_num)] at h
    have h3 : (algebraMap ℝ ℂ (3 : ℝ)) = (3 : ℂ) := by norm_num
    refine (algebraMap ℝ ℂ).injective ?_
    rw [h, h3]
    linear_combination ((c + starRingEnd ℂ c + 1) ^ 2
        - 3 * (c + starRingEnd ℂ c + 1) - 3 * (c * starRingEnd ℂ c - 1)) * hc1
      + 3 * hc2
  exact ⟨P, hPdeg, hPz, hPzbar, hPx, hPother, ht1, ht2, ht3⟩

end

end Pconstructible


/- ==================== inlined from Pptc.S1Iso ==================== -/


open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### F5. There is no totally isotropic plane when `s = 1`

With a single conjugate pair `{z, z̄}`, the trace form `Q = qform (Gram q)` has no totally
isotropic plane: `Q x = Q y = B x y = 0` with `y ≠ 0` forces `x ∥ y`.

For `a b : ℝ` put `H = a F + b G`, where `F, G` are the degree-`≤ 6` polynomials of `x, y`.
The second power sum identity `companion7_trace_pow_aeval` and the root decomposition
`roots_eq_pair_add_real` give, over `ℂ`, that the sum of the squares of `H` over the roots
of `q` vanishes.  The conjugate pair contributes `2 Re (H(z)²)` and the other five roots are
real, so
`∑_r H(r)² + 2 Re (H(z)²) = 0`
for every `a, b`.  If `F(z), G(z)` are `ℝ`-dependent there is a nonzero `(a, b)` with
`H(z) = 0`, so the sum of squares vanishes termwise and `H`, of degree `≤ 6`, vanishes at the
seven distinct roots of `q`; hence `H = 0`.  Otherwise some `H` realises `H(z) = 1`, forcing the
sum of squares to be `-2 < 0`, a contradiction. -/

/-- `vecOf` is a left inverse of `polyOfVec`. -/
private lemma vecOf_polyOfVec (v : Fin 7 → ℝ) : vecOf (polyOfVec v) = v := by
  funext i
  have hc : (polyOfVec v).coeff i.val = v i := by
    rw [polyOfVec, coeff_finset_sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Polynomial.coeff_monomial]
      split_ifs with h
      · exact absurd (Fin.ext h) hji
      · rfl
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simpa [vecOf] using hc

/-- Evaluation of a mapped real polynomial at a real point. -/
private lemma eval_map_ofReal (f : ℝ[X]) (r : ℝ) :
    (f.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = ((f.eval r : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (f := algebraMap ℝ ℂ) (r := r) (p := f)

/-- Coercing the sum of the squared evaluations equals the complex multiset sum. -/
private lemma ofReal_sum_sq (R : Multiset ℝ) (H : ℝ[X]) :
    ((R.map (fun r => ((H.eval r) ^ 2 : ℂ))).sum)
      = (((R.map (fun r => (H.eval r) ^ 2)).sum : ℝ) : ℂ) := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih]
      push_cast
      ring

/-- The evaluation at `z` of `(C a * F + C b * G).map` is `a * F(z) + b * G(z)`. -/
private lemma eval_C_mul_add (F G : ℝ[X]) (z : ℂ) (a b : ℝ) :
    (((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval z)
      = (a : ℂ) * ((F.map (algebraMap ℝ ℂ)).eval z)
        + (b : ℂ) * ((G.map (algebraMap ℝ ℂ)).eval z) := by
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_C]
  simp

/-- The real sum of squares identity attached to the trace power sum. -/
private theorem sum_sq_add_pair_re {q H : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)))
    (htrace : Matrix.trace ((aeval (companion7 q) H) ^ 2) = 0) :
    (R.map (fun r => (H.eval r) ^ 2)).sum
      + 2 * ((((H.map (algebraMap ℝ ℂ)).eval z) ^ 2).re) = 0 := by
  have htr := companion7_trace_pow_aeval q H hmon hnat hsep 2
  rw [htrace, map_zero] at htr
  have hsum : ((q.map (algebraMap ℝ ℂ)).roots.map
      (fun w => ((H.map (algebraMap ℝ ℂ)).eval w) ^ 2)).sum = 0 := htr.symm
  rw [hroots] at hsum
  simp only [Multiset.map_cons, Multiset.sum_cons] at hsum
  set w : ℂ := (H.map (algebraMap ℝ ℂ)).eval z with hw
  set S : ℝ := (R.map (fun r => (H.eval r) ^ 2)).sum with hS
  have hzbar : ((H.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)) ^ 2
      = starRingEnd ℂ (w ^ 2) := by
    rw [hw, eval_map_conj, map_pow]
  have hRmap : ((R.map (algebraMap ℝ ℂ)).map
      (fun w => ((H.map (algebraMap ℝ ℂ)).eval w) ^ 2)).sum = ((S : ℝ) : ℂ) := by
    rw [Multiset.map_map]
    have hcongr : R.map ((fun w => ((H.map (algebraMap ℝ ℂ)).eval w) ^ 2)
        ∘ algebraMap ℝ ℂ) = R.map (fun r => ((H.eval r) ^ 2 : ℂ)) := by
      apply Multiset.map_congr rfl
      intro r _
      simp only [Function.comp_apply]
      rw [eval_map_ofReal]
    rw [hcongr]
    rw [ofReal_sum_sq, hS]
  rw [hzbar, hRmap] at hsum
  have hmain : (2 * (w ^ 2).re + S : ℝ) = 0 := by
    rw [← add_assoc, Complex.add_conj] at hsum
    exact_mod_cast hsum
  rw [hS]
  linarith

/-- If `H` of degree `≤ 6` vanishes at all complex roots of a separable septic `q`, then
`H = 0`. -/
private lemma eq_zero_of_eval_zero_on_roots {q H : ℝ[X]} (_hmon : q.Monic)
    (hnat : q.natDegree = 7) (hsep : q.Separable) (hHdeg : H.natDegree ≤ 6)
    (h : ∀ w : ℂ, w ∈ (q.map (algebraMap ℝ ℂ)).roots →
      (H.map (algebraMap ℝ ℂ)).eval w = 0) : H = 0 := by
  have hnodup : (q.map (algebraMap ℝ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots (hsep.map)
  have hcardC : (q.map (algebraMap ℝ ℂ)).roots.card = 7 := by
    rw [show (q.map (algebraMap ℝ ℂ)).roots.card = (q.map (algebraMap ℝ ℂ)).natDegree from
      (IsAlgClosed.splits (q.map (algebraMap ℝ ℂ))).natDegree_eq_card_roots.symm]
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, hnat]
  have hcardfin : Fintype.card ((q.map (algebraMap ℝ ℂ)).roots.toFinset) = 7 := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcardC]
  have hdegC : (H.map (algebraMap ℝ ℂ)).natDegree < 7 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    omega
  refine (Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective).mp ?_
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (H.map (algebraMap ℝ ℂ)) (ι := (q.map (algebraMap ℝ ℂ)).roots.toFinset)
    (f := Subtype.val) Subtype.val_injective ?_ ?_
  · intro w
    exact h (w : ℂ) (Multiset.mem_toFinset.mp w.2)
  · rw [hcardfin]; exact hdegC

-- Theorem: with a single conjugate pair the trace form on `{p1 = 0}` has no totally isotropic
-- plane: `Q x = Q y = B x y = 0` and `y ≠ 0` force `x` to be a scalar multiple of `y`.
theorem isotropic_plane_trivial {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z) :
    ∀ x y : Fin 6 → ℝ, qform (Gram q) x = 0 → qform (Gram q) y = 0 →
      bilin (Gram q) x y = 0 → y ≠ 0 → ∃ c : ℝ, x = c • y := by
  intro x y hQx hQy hBxy hyne
  set F : ℝ[X] := polyOfVec (Lcomb q x) with hF
  set G : ℝ[X] := polyOfVec (Lcomb q y) with hG
  have hFdeg : F.natDegree ≤ 6 := by rw [hF]; exact polyOfVec_natDegree_le _
  have hGdeg : G.natDegree ≤ 6 := by rw [hG]; exact polyOfVec_natDegree_le _
  have hvecF : vecOf F = Lcomb q x := by rw [hF]; exact vecOf_polyOfVec _
  have hvecG : vecOf G = Lcomb q y := by rw [hG]; exact vecOf_polyOfVec _
  obtain ⟨R, _hRnodup, _hRcard, hroots⟩ :=
    roots_eq_pair_add_real hmon hnat hsep hz hzim hone
  have hpoly : ∀ a b : ℝ,
      C a * F + C b * G = polyOfVec (Lcomb q (a • x + b • y)) := by
    intro a b
    rw [← polyOfVec_smul_add hFdeg hGdeg, hvecF, hvecG, Lcomb_smul_add]
  have hHdeg : ∀ a b : ℝ, (C a * F + C b * G).natDegree ≤ 6 := by
    intro a b
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_C_mul_le a F) hFdeg
    · exact le_trans (Polynomial.natDegree_C_mul_le b G) hGdeg
  have key : ∀ a b : ℝ,
      (R.map (fun r => ((C a * F + C b * G).eval r) ^ 2)).sum
        + 2 * (((((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval z) ^ 2).re) = 0 := by
    intro a b
    have hQab : qform (Gram q) (a • x + b • y) = 0 := by
      rw [qform_smul_add (Gram q) (Gram_symm q) a b x y, hQx, hQy, hBxy]
      ring
    have htrace : Matrix.trace ((aeval (companion7 q) (C a * F + C b * G)) ^ 2) = 0 := by
      calc Matrix.trace ((aeval (companion7 q) (C a * F + C b * G)) ^ 2)
          = Matrix.trace ((aeval (companion7 q)
              (polyOfVec (Lcomb q (a • x + b • y)))) ^ 2) := by rw [hpoly a b]
        _ = hermiteForm q (Lcomb q (a • x + b • y)) :=
              (hermiteForm_eq_trace_sq q _).symm
        _ = qform (Hmat q) (Lcomb q (a • x + b • y)) :=
              (qform_Hmat_eq_hermiteForm q _).symm
        _ = qform (Gram q) (a • x + b • y) := qform_Hmat_Lcomb q _
        _ = 0 := hQab
    exact sum_sq_add_pair_re hmon hnat hsep hroots htrace
  set u : ℂ := (F.map (algebraMap ℝ ℂ)).eval z with hu
  set v : ℂ := (G.map (algebraMap ℝ ℂ)).eval z with hv
  set D : ℝ := u.re * v.im - u.im * v.re with hD
  by_cases hD0 : D = 0
  · -- dependent case: a nonzero `(a, b)` with `a u + b v = 0`
    have hex : ∃ a b : ℝ, (a, b) ≠ (0, 0) ∧ (a : ℂ) * u + (b : ℂ) * v = 0 := by
      by_cases hu0 : u = 0
      · exact ⟨1, 0, by simp, by simp [hu0]⟩
      · refine ⟨u.re * v.re + u.im * v.im, -(u.re ^ 2 + u.im ^ 2), ?_, ?_⟩
        · intro h
          have hB : -(u.re ^ 2 + u.im ^ 2) = 0 := by
            have := congrArg Prod.snd h
            simpa using this
          have hsum0 : u.re ^ 2 + u.im ^ 2 = 0 := by linarith
          have hre : u.re = 0 := by nlinarith [sq_nonneg u.re, sq_nonneg u.im]
          have him : u.im = 0 := by nlinarith [sq_nonneg u.re, sq_nonneg u.im]
          exact hu0 (Complex.ext hre him)
        · have hd : u.re * v.im = u.im * v.re := by
            have := hD0; rw [hD] at this; linarith
          apply Complex.ext
          · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              Complex.zero_re]
            ring_nf
            linear_combination (u.im) * hd
          · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.zero_im]
            ring_nf
            linear_combination (-u.re) * hd
    obtain ⟨a, b, habne, huv0⟩ := hex
    have hHz : (((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval z) = 0 := by
      rw [eval_C_mul_add, ← hu, ← hv]
      exact huv0
    have hkey := key a b
    rw [hHz] at hkey
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), Complex.zero_re, mul_zero, add_zero]
      at hkey
    have hpoint : ∀ r ∈ R, (C a * F + C b * G).eval r = 0 := by
      have hnn : ∀ s ∈ R.map (fun r => ((C a * F + C b * G).eval r) ^ 2), (0 : ℝ) ≤ s := by
        intro s hs
        obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hs
        exact sq_nonneg _
      have hall := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hnn hkey
      intro r hr
      exact sq_eq_zero_iff.mp (hall _ (Multiset.mem_map_of_mem _ hr))
    have hrootzero : ∀ w : ℂ, w ∈ (q.map (algebraMap ℝ ℂ)).roots →
        ((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval w = 0 := by
      intro w hw
      rw [hroots] at hw
      rcases Multiset.mem_cons.mp hw with hwz | hw
      · subst hwz; exact hHz
      · rcases Multiset.mem_cons.mp hw with hwz | hw
        · subst hwz
          rw [eval_map_conj, hHz, map_zero]
        · obtain ⟨r, hr, hrw⟩ := Multiset.mem_map.mp hw
          rw [← hrw, eval_map_ofReal, hpoint r hr]
          simp
    have hH0 : C a * F + C b * G = 0 :=
      eq_zero_of_eval_zero_on_roots hmon hnat hsep (hHdeg a b) hrootzero
    have hL0 : Lcomb q (a • x + b • y) = 0 := by
      rw [hpoly a b] at hH0
      by_contra hne
      exact polyOfVec_ne_zero hne hH0
    have hab0 : a • x + b • y = 0 := Lcomb_injective q hL0
    have ha0 : a ≠ 0 := by
      intro ha
      rw [ha, zero_smul, zero_add] at hab0
      rcases smul_eq_zero.mp hab0 with hb | hy
      · exact habne (Prod.ext ha hb)
      · exact hyne hy
    refine ⟨-(b / a), ?_⟩
    have h1 : a • x = -(b • y) := eq_neg_of_add_eq_zero_left hab0
    calc x = a⁻¹ • (a • x) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
      _ = a⁻¹ • (-(b • y)) := by rw [h1]
      _ = (-(b / a)) • y := by
          rw [smul_neg, smul_smul, div_eq_mul_inv, neg_smul, mul_comm b a⁻¹]
  · -- independent case: some `(a, b)` realises `H(z) = 1`
    have hvnd : ((v.im / D : ℝ) : ℂ) * u + ((-u.im / D : ℝ) : ℂ) * v = 1 := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.one_re]
        field_simp [hD0]
        rw [hD]; ring
      · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.one_im]
        field_simp [hD0]; ring
    have hHz : (((C (v.im / D) * F + C (-u.im / D) * G).map
        (algebraMap ℝ ℂ)).eval z) = 1 := by
      rw [eval_C_mul_add, ← hu, ← hv]
      exact hvnd
    have hkey := key (v.im / D) (-u.im / D)
    rw [hHz] at hkey
    simp only [one_pow, Complex.one_re, mul_one] at hkey
    have hnn : 0 ≤ (R.map (fun r => ((C (v.im / D) * F + C (-u.im / D) * G).eval r) ^ 2)).sum :=
      Multiset.sum_nonneg (fun s hs => by
        obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hs
        exact sq_nonneg _)
    linarith

end

end Pconstructible


/- ==================== inlined from Pptc.S1Sign ==================== -/


open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### The sign certificate for the one-conjugate-pair septic

With a single non-real conjugate pair `{z, z̄}` the trace form `Q = qform (Gram q)` has no
totally isotropic plane (`isotropic_plane_trivial`).  The plan of `PLAN-degree7-s1.md` turns
that into a strict sign change of the reduced cubic `p3vec` on the light cone, using the
conjugation symmetry only inside the proof.  This file formalises the sign certificate: on the
cone `{Q = 0}` through a nonzero `P₀`, the stereographic parametrisation `stereo` produces
directions on which `p3vec` takes both signs.

The lynchpin is a Lagrange polynomial `X` with `X(x_j) = 1` at one real root, `0` at the other
real roots, and `ω = -1/2 + (√3/2) i` at `z`.  Its conjugate has `ω̄` at `z`.  Writing
`b = bilin (Gram q) P₀ (coeff6 (vecOf X))`, the trace split identity gives
`b = y_j + u ω + ū ω̄` with `y_j` the value of `F₀ = polyOfVec (Lcomb q P₀)` at `x_j` and `u =
F₀(z)`, so the two `b`'s multiply to `(y_j - Re u)² - 3 (Im u)²`, which is negative for some
`j` because `Q P₀ = 0` forces `(Im u)² = (Re u)² + S/2`. -/

/-- The primitive sixth root of unity `-1/2 + (√3/2) i`. -/
noncomputable def omegaC : ℂ := ⟨-1/2, Real.sqrt 3 / 2⟩

lemma omegaC_add_conj : omegaC + starRingEnd ℂ omegaC = -1 := by
  apply Complex.ext
  · simp [omegaC]
  · simp [omegaC]

lemma omegaC_mul_conj : omegaC * starRingEnd ℂ omegaC = 1 := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.one_re, Complex.conj_re, Complex.conj_im, omegaC]
    ring_nf
    rw [show (Real.sqrt 3) ^ 2 = 3 from Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  · simp only [Complex.mul_im, Complex.one_im, Complex.conj_re, Complex.conj_im, omegaC]
    ring

/-! ### Transport helpers

`vecOf` is a left inverse of `polyOfVec`, and evaluations of a mapped real polynomial at a
real point are the real evaluations cast to `ℂ`.  These are used to move between polynomials
and their coefficient vectors in the trace identities. -/

/-- Coercing a multiset sum of real values into `ℂ`. -/
lemma ofReal_multiset_sum (R : Multiset ℝ) (F : ℝ → ℝ) :
    (R.map (fun r => (F r : ℂ))).sum = (((R.map F).sum : ℝ) : ℂ) := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih]
      push_cast
      ring

/-! ### The trace split identity

`trace (N_f N_g)` is the sum of `f(w) g(w)` over the complex roots `w` of `q`.  Under the
root decomposition `z ::ₘ z̄ ::ₘ R` this is the real sum over `R` plus the terms at `z` and
`z̄`.  This is the computational core of the sign certificate. -/

-- Theorem: the trace of `N_f N_g` splits as the sum over the five real roots plus the two
-- non-real terms `f(z) g(z)` and `f(z̄) g(z̄)`.
lemma ofReal_trace_mul_eq_sum (q f g : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ))) :
    algebraMap ℝ ℂ (Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)))
      = ((R.map (fun r => f.eval r * g.eval r)).sum : ℂ)
        + ((f.map (algebraMap ℝ ℂ)).eval z) * ((g.map (algebraMap ℝ ℂ)).eval z)
        + ((f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z))
            * ((g.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)) := by
  have h := companion7_trace_pow_aeval q (f * g) hmon hnat hsep 1
  rw [pow_one, map_mul] at h
  rw [hroots, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons] at h
  simp only [Polynomial.map_mul, Polynomial.eval_mul, pow_one] at h
  have hR : ((R.map (algebraMap ℝ ℂ)).map
      (fun w => ((f.map (algebraMap ℝ ℂ)).eval w)
        * ((g.map (algebraMap ℝ ℂ)).eval w))).sum
      = (((R.map (fun r => f.eval r * g.eval r)).sum : ℝ) : ℂ) := by
    rw [Multiset.map_map]
    have hcongr : (R.map (((fun w => ((f.map (algebraMap ℝ ℂ)).eval w)
          * ((g.map (algebraMap ℝ ℂ)).eval w)) ∘ (algebraMap ℝ ℂ))))
        = R.map (fun r => ((f.eval r * g.eval r : ℝ) : ℂ)) := by
      apply Multiset.map_congr rfl
      intro r _
      simp only [Function.comp_apply]
      rw [eval_map_ofReal, eval_map_ofReal]
      exact (map_mul (algebraMap ℝ ℂ) (f.eval r) (g.eval r)).symm
    rw [hcongr, ofReal_multiset_sum]
  rw [hR] at h
  rw [h]
  ring

-- Theorem: every element of `R` is a real root of `q`.
lemma root_of_mem_R {q : ℝ[X]} (hmon : q.Monic) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ))) :
    ∀ r ∈ R, q.eval r = 0 := by
  intro r hr
  have hqCne : (q.map (algebraMap ℝ ℂ)) ≠ 0 := (hmon.map (algebraMap ℝ ℂ)).ne_zero
  have hmemR : (algebraMap ℝ ℂ r) ∈ R.map (algebraMap ℝ ℂ) :=
    (Multiset.mem_map_of_injective (algebraMap ℝ ℂ).injective).mpr hr
  have hmem : (algebraMap ℝ ℂ r) ∈ (q.map (algebraMap ℝ ℂ)).roots := by
    rw [hroots]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hmemR)
  have hroot := (Polynomial.mem_roots hqCne).mp hmem
  change (q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = 0 at hroot
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply] at hroot
  exact (algebraMap ℝ ℂ).injective (by simpa using hroot)

-- Theorem: a degree-`≤ 6` real polynomial vanishing at all complex roots of a separable
-- septic `q` is zero.
lemma eq_zero_of_vanishes_on_roots {q H : ℝ[X]} (hnat : q.natDegree = 7) (hsep : q.Separable)
    (hHdeg : H.natDegree ≤ 6)
    (h : ∀ w : ℂ, w ∈ (q.map (algebraMap ℝ ℂ)).roots →
      (H.map (algebraMap ℝ ℂ)).eval w = 0) : H = 0 := by
  have hnodup : (q.map (algebraMap ℝ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots (hsep.map)
  have hcardC : (q.map (algebraMap ℝ ℂ)).roots.card = 7 := by
    rw [show (q.map (algebraMap ℝ ℂ)).roots.card
        = (q.map (algebraMap ℝ ℂ)).natDegree from
      (IsAlgClosed.splits (q.map (algebraMap ℝ ℂ))).natDegree_eq_card_roots.symm]
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, hnat]
  have hcardfin : Fintype.card ((q.map (algebraMap ℝ ℂ)).roots.toFinset) = 7 := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcardC]
  have hdegC : (H.map (algebraMap ℝ ℂ)).natDegree < 7 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    omega
  refine (Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective).mp ?_
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (H.map (algebraMap ℝ ℂ)) (ι := (q.map (algebraMap ℝ ℂ)).roots.toFinset)
    (f := Subtype.val) Subtype.val_injective ?_ ?_
  · intro w
    exact h (w : ℂ) (Multiset.mem_toFinset.mp w.2)
  · rw [hcardfin]; exact hdegC

-- Theorem: `bilin (Hmat q) (vecOf f) (vecOf g) = trace (N_f N_g)`.
lemma bilin_Hmat_vecOf (q : ℝ[X]) (f g : ℝ[X]) (hf : f.natDegree ≤ 6)
    (hg : g.natDegree ≤ 6) :
    bilin (Hmat q) (vecOf f) (vecOf g)
      = Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)) := by
  have hfg : (f + g).natDegree ≤ 6 :=
    le_trans (Polynomial.natDegree_add_le f g) (max_le hf hg)
  have h1 := qform_add (Hmat q) (Hmat_symm q) (vecOf f) (vecOf g)
  have hv : vecOf f + vecOf g = vecOf (f + g) := by
    ext i
    simp [vecOf, Polynomial.coeff_add]
  rw [hv] at h1
  have hqf : qform (Hmat q) (vecOf f)
      = Matrix.trace ((aeval (companion7 q) f) ^ 2) := by
    rw [qform_Hmat_eq_hermiteForm, hermiteForm_eq_trace_sq, polyOfVec_vecOf hf]
  have hqg : qform (Hmat q) (vecOf g)
      = Matrix.trace ((aeval (companion7 q) g) ^ 2) := by
    rw [qform_Hmat_eq_hermiteForm, hermiteForm_eq_trace_sq, polyOfVec_vecOf hg]
  have hqfg : qform (Hmat q) (vecOf (f + g))
      = Matrix.trace ((aeval (companion7 q) (f + g)) ^ 2) := by
    rw [qform_Hmat_eq_hermiteForm, hermiteForm_eq_trace_sq, polyOfVec_vecOf hfg]
  rw [hqfg, hqf, hqg] at h1
  have htr := trace_sq_smul_add (aeval (companion7 q) f) (aeval (companion7 q) g) 1 1
  have hmap : aeval (companion7 q) (f + g)
      = (1 : ℝ) • aeval (companion7 q) f + (1 : ℝ) • aeval (companion7 q) g := by
    rw [map_add]; simp
  rw [hmap] at h1
  rw [h1] at htr
  simp only [one_pow, one_mul] at htr
  linarith

/-! ### The complex product identity

For `ω = -1/2 + (√3/2) i` and any `u`, the two numbers `y + u ω + ū ω̄` and
`y + u ω̄ + ū ω` multiply to `(y - Re u)² - 3 (Im u)²`. -/

/-- The conjugate-free part of the product identity. -/
lemma omegaC_prod_aux (y : ℝ) (u : ℂ) :
    (y - starRingEnd ℂ u) * (y - u) + (u - starRingEnd ℂ u) ^ 2
      = (((y - u.re) ^ 2 - 3 * u.im ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, pow_two]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.sub_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, pow_two]
    ring

-- Theorem: `(y + u ω + ū ω̄)(y + u ω̄ + ū ω) = (y - Re u)² - 3 (Im u)²`.
lemma omegaC_prod (y : ℝ) (u : ℂ) :
    ((y : ℂ) + u * omegaC + starRingEnd ℂ u * starRingEnd ℂ omegaC)
      * ((y : ℂ) + u * starRingEnd ℂ omegaC + starRingEnd ℂ u * omegaC)
      = (((y - u.re) ^ 2 - 3 * u.im ^ 2 : ℝ) : ℂ) := by
  have hw' : starRingEnd ℂ omegaC = -1 - omegaC := by
    rw [← omegaC_add_conj]; ring
  have hwsq : omegaC + omegaC ^ 2 = -1 := by
    have h := omegaC_mul_conj
    rw [hw'] at h
    linear_combination -h
  have hmain : ((y : ℂ) + u * omegaC + starRingEnd ℂ u * starRingEnd ℂ omegaC)
      * ((y : ℂ) + u * starRingEnd ℂ omegaC + starRingEnd ℂ u * omegaC)
      = (y - starRingEnd ℂ u) * (y - u) + (u - starRingEnd ℂ u) ^ 2 := by
    rw [hw']
    linear_combination (-(u - starRingEnd ℂ u) ^ 2) * hwsq
  rw [hmain, omegaC_prod_aux]

/-! ### One direction from one prescribed value at `z`

For a real root `x_j ∈ R` and a complex value `c` with `c + c̄ = -1`, `c c̄ = 1`, the
Lagrange polynomial `X` of `exists_lagrange_value` gives a direction `d = coeff6 (vecOf X)`
on the cone with `p3vec q (Lcomb q d) = 3`, together with `b = bilin (Gram q) P₀ d` satisfying
`b = F₀(x_j) + u c + ū c̄` with `u = F₀(z)`. -/

-- Theorem: for a prescribed value `c` at `z` on the unit circle with `Re c = -1/2`, the
-- Lagrange polynomial yields a cone direction `d` with `p3vec = 3` and the stated bilinear
-- value against `P₀`.
lemma exists_direction_of_value {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)))
    (hRroot : ∀ r ∈ R, q.eval r = 0) (hRnodup : R.Nodup)
    {P₀ : Fin 6 → ℝ} {xj : ℝ} (hxjmem : xj ∈ R)
    {c : ℂ} (hc1 : c + starRingEnd ℂ c = -1) (hc2 : c * starRingEnd ℂ c = 1) :
    ∃ (d : Fin 6 → ℝ) (b : ℝ),
      qform (Gram q) d = 0 ∧
      p3vec q (Lcomb q d) = 3 ∧
      (b : ℂ) = (((polyOfVec (Lcomb q P₀)).eval xj : ℝ) : ℂ)
        + ((polyOfVec (Lcomb q P₀)).map (algebraMap ℝ ℂ)).eval z * c
        + starRingEnd ℂ (((polyOfVec (Lcomb q P₀)).map (algebraMap ℝ ℂ)).eval z)
          * starRingEnd ℂ c ∧
      bilin (Gram q) P₀ d = b := by
  classical
  set F0 : ℝ[X] := polyOfVec (Lcomb q P₀) with hF0
  have hF0deg : F0.natDegree ≤ 6 := by rw [hF0]; exact polyOfVec_natDegree_le _
  have hvecF0 : vecOf F0 = Lcomb q P₀ := by rw [hF0, vecOf_polyOfVec]
  have hxjroot : q.eval xj = 0 := hRroot xj hxjmem
  have hxjz : (algebraMap ℝ ℂ xj) ≠ z := fun h => hzim (by rw [← h]; simp)
  have hxjz' : (algebraMap ℝ ℂ xj) ≠ starRingEnd ℂ z := fun h => by
    have hc := congrArg Complex.im h
    simp at hc
    exact hzim (by linarith)
  obtain ⟨X, hXdeg, hXz, hXzbar, hXxj, hXother, ht1, ht2, ht3⟩ :=
    exists_lagrange_value hmon hnat hsep hz hzim hone hxjroot hxjz hxjz' hc1 hc2
  have hp1X : p1vec q (vecOf X) = 0 := by
    rw [p1vec_vecOf q X hXdeg, ht1]
  have hLcombX : Lcomb q (coeff6 (vecOf X)) = vecOf X := Lcomb_coeff6 q hp1X
  have hqform_d : qform (Gram q) (coeff6 (vecOf X)) = 0 := by
    rw [← qform_Hmat_Lcomb q (coeff6 (vecOf X)), hLcombX, qform_Hmat_eq_hermiteForm,
      hermiteForm_eq_trace_sq, polyOfVec_vecOf hXdeg, ht2]
  have hp3_d : p3vec q (Lcomb q (coeff6 (vecOf X))) = 3 := by
    rw [hLcombX, p3vec, polyOfVec_vecOf hXdeg, ht3]
  have hRval : (R.map (fun r => F0.eval r * X.eval r)).sum = F0.eval xj := by
    have hReq : R = xj ::ₘ R.erase xj := (Multiset.cons_erase hxjmem).symm
    rw [hReq]
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have hhead : F0.eval xj * X.eval xj = F0.eval xj := by rw [hXxj, mul_one]
    have htail : ((R.erase xj).map (fun r => F0.eval r * X.eval r)).sum = 0 := by
      have hmap0 : (R.erase xj).map (fun r => F0.eval r * X.eval r)
          = (R.erase xj).map (fun _ => (0 : ℝ)) := by
        apply Multiset.map_congr rfl
        intro r hr
        have hrne : r ≠ xj := (hRnodup.mem_erase_iff.mp hr).1
        have hroot : q.eval r = 0 := hRroot r (Multiset.mem_of_mem_erase hr)
        rw [hXother r hroot hrne, mul_zero]
      rw [hmap0, Multiset.sum_map_zero]
    rw [hhead, htail, add_zero]
  have htrace_eq : Matrix.trace ((aeval (companion7 q) F0) * (aeval (companion7 q) X))
      = bilin (Gram q) P₀ (coeff6 (vecOf X)) := by
    rw [← bilin_Hmat_vecOf q F0 X hF0deg hXdeg]
    conv_lhs => rw [hvecF0, ← hLcombX]
    rw [bilin_Hmat_Lcomb]
  have hsplit := ofReal_trace_mul_eq_sum q F0 X hmon hnat hsep hroots
  rw [hRval, hXz, hXzbar, eval_map_conj F0 z] at hsplit
  refine ⟨coeff6 (vecOf X), bilin (Gram q) P₀ (coeff6 (vecOf X)), hqform_d, hp3_d, ?_,
    rfl⟩
  rw [← htrace_eq]
  exact hsplit

-- Theorem: the real arithmetic behind the sign certificate.  If `y₁² + y₂² ≤ S` and
-- `γ² = α² + S/2`, then either one of the two products `b_j = (y_j - α)² - 3γ²` is negative,
-- or `S = α = γ = 0` (the degenerate case excluded by `F₀ ≠ 0`).
set_option maxHeartbeats 400000 in
-- the `nlinarith` chain on the products `(y - α)² - 3γ²` needs more than the default budget
private lemma sign_neg_aux {y1 y2 α γ S b1 b2 : ℝ}
    (hS : y1 ^ 2 + y2 ^ 2 ≤ S) (hg : γ ^ 2 = α ^ 2 + S / 2)
    (h1 : b1 = (y1 - α) ^ 2 - 3 * γ ^ 2) (h2 : b2 = (y2 - α) ^ 2 - 3 * γ ^ 2) :
    b1 < 0 ∨ b2 < 0 ∨ (S = 0 ∧ α = 0 ∧ γ = 0) := by
  by_cases hb1 : b1 < 0
  · exact Or.inl hb1
  by_cases hb2 : b2 < 0
  · exact Or.inr (Or.inl hb2)
  push Not at hb1 hb2
  have hb1' : b1 = y1 ^ 2 - 2 * α * y1 - 2 * α ^ 2 - (3 / 2) * S := by rw [h1, hg]; ring
  have hb2' : b2 = y2 ^ 2 - 2 * α * y2 - 2 * α ^ 2 - (3 / 2) * S := by rw [h2, hg]; ring
  have hbd1 : b1 ≤ -((1 / 2) * (y1 + 2 * α) ^ 2 + (3 / 2) * y2 ^ 2) := by
    rw [hb1']; nlinarith [hS]
  have hbd2 : b2 ≤ -((1 / 2) * (y2 + 2 * α) ^ 2 + (3 / 2) * y1 ^ 2) := by
    rw [hb2']; nlinarith [hS]
  have e1 : (1 / 2) * (y1 + 2 * α) ^ 2 + (3 / 2) * y2 ^ 2 = 0 := by
    nlinarith [hb1, hbd1, sq_nonneg (y1 + 2 * α), sq_nonneg y2]
  have e2 : (1 / 2) * (y2 + 2 * α) ^ 2 + (3 / 2) * y1 ^ 2 = 0 := by
    nlinarith [hb2, hbd2, sq_nonneg (y2 + 2 * α), sq_nonneg y1]
  have hy1 : y1 = 0 := by
    have h2' : y1 ^ 2 = 0 := by nlinarith [e2, sq_nonneg (y2 + 2 * α), sq_nonneg y1]
    exact sq_eq_zero_iff.mp h2'
  have hy2 : y2 = 0 := by
    have h2' : y2 ^ 2 = 0 := by nlinarith [e1, sq_nonneg (y1 + 2 * α), sq_nonneg y2]
    exact sq_eq_zero_iff.mp h2'
  have hα0 : α = 0 := by
    have h2' : (2 * α) ^ 2 = 0 := by nlinarith [e1, hy1, hy2]
    have h3 : 2 * α = 0 := sq_eq_zero_iff.mp h2'
    linarith
  have hb1zero : b1 = 0 := by nlinarith [hb1, hbd1, e1]
  have hS0 : S = 0 := by nlinarith [hb1', hb1zero, hy1, hy2, hα0]
  have hγ0 : γ = 0 := by
    have h1' : γ ^ 2 = 0 := by rw [hg, hS0, hα0]; ring
    exact sq_eq_zero_iff.mp h1'
  exact Or.inr (Or.inr ⟨hS0, hα0, hγ0⟩)

-- Theorem: on the light cone through a nonzero `P₀` the reduced cubic `p3vec` takes both
-- signs.  This is the sign certificate of `PLAN-degree7-s1.md` §3 Step 3.
theorem exists_sign_change {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable)
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {P₀ : Fin 6 → ℝ} (hQ₀ : qform (Gram q) P₀ = 0) (hP₀ne : P₀ ≠ 0) :
    ∃ dplus dminus : Fin 6 → ℝ,
      0 < p3vec q (Lcomb q (stereo (Gram q) P₀ dplus)) ∧
      p3vec q (Lcomb q (stereo (Gram q) P₀ dminus)) < 0 := by
  classical
  obtain ⟨R, hRnodup, hRcard, hroots⟩ :=
    roots_eq_pair_add_real hmon hnat hsep hz hzim hone
  have hRroot : ∀ r ∈ R, q.eval r = 0 := root_of_mem_R hmon hroots
  have hne1 : R ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hRcard; omega
  obtain ⟨x1, hx1mem⟩ := Multiset.exists_mem_of_ne_zero hne1
  have hx1erase : 0 < (R.erase x1).card := by
    rw [Multiset.card_erase_of_mem hx1mem, hRcard]; norm_num
  have hne2 : R.erase x1 ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hx1erase; omega
  obtain ⟨x2, hx2erase⟩ := Multiset.exists_mem_of_ne_zero hne2
  have hx2mem : x2 ∈ R := Multiset.mem_of_mem_erase hx2erase
  have hx21 : x2 ≠ x1 := (hRnodup.mem_erase_iff.mp hx2erase).1
  set F0 : ℝ[X] := polyOfVec (Lcomb q P₀) with hF0
  have hF0deg : F0.natDegree ≤ 6 := by rw [hF0]; exact polyOfVec_natDegree_le _
  have hF0ne : F0 ≠ 0 := by
    rw [hF0]
    exact polyOfVec_ne_zero (fun h => hP₀ne (Lcomb_injective q h))
  have hvecF0 : vecOf F0 = Lcomb q P₀ := by rw [hF0, vecOf_polyOfVec]
  set S : ℝ := (R.map (fun r => (F0.eval r) ^ 2)).sum with hS
  set u : ℂ := (F0.map (algebraMap ℝ ℂ)).eval z with hu
  set α : ℝ := u.re with hα
  set γ : ℝ := u.im with hγ
  have htrF0sq : Matrix.trace ((aeval (companion7 q) F0) ^ 2) = 0 := by
    have h1 : qform (Hmat q) (vecOf F0) = 0 := by
      rw [hvecF0, qform_Hmat_Lcomb q P₀, hQ₀]
    rw [qform_Hmat_eq_hermiteForm, hermiteForm_eq_trace_sq,
      polyOfVec_vecOf hF0deg] at h1
    exact h1
  have hsplit2 := ofReal_trace_mul_eq_sum q F0 F0 hmon hnat hsep hroots
  have hzero : algebraMap ℝ ℂ
      (Matrix.trace ((aeval (companion7 q) F0) * (aeval (companion7 q) F0))) = 0 := by
    rw [← pow_two, htrF0sq, map_zero]
  rw [hzero, eval_map_conj F0 z, ← hu] at hsplit2
  have hSsum : (R.map (fun r => F0.eval r * F0.eval r)).sum = S := by
    rw [hS]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro r _
    rw [sq]
  have hpair : u * u + starRingEnd ℂ u * starRingEnd ℂ u
      = ((2 * (u ^ 2).re : ℝ) : ℂ) := by
    have h2 : starRingEnd ℂ u * starRingEnd ℂ u = starRingEnd ℂ (u * u) := by
      rw [map_mul]
    rw [h2, ← sq, Complex.add_conj]
  have hSreal : S + 2 * (u ^ 2).re = 0 := by
    have h5 : ((R.map (fun r => F0.eval r * F0.eval r)).sum : ℂ)
        + (u * u + starRingEnd ℂ u * starRingEnd ℂ u) = 0 := by
      rw [← add_assoc]; exact hsplit2.symm
    rw [hSsum, hpair] at h5
    exact_mod_cast h5
  have hu2re : (u ^ 2).re = u.re ^ 2 - u.im ^ 2 := by
    rw [sq, Complex.mul_re]; ring
  have hgamma : γ ^ 2 = α ^ 2 + S / 2 := by
    rw [hu2re, ← hα, ← hγ] at hSreal
    linarith
  have hSbound : (F0.eval x1) ^ 2 + (F0.eval x2) ^ 2 ≤ S := by
    have hR1 : R = x1 ::ₘ R.erase x1 := (Multiset.cons_erase hx1mem).symm
    have hx2e : x2 ∈ R.erase x1 := hRnodup.mem_erase_iff.mpr ⟨hx21, hx2mem⟩
    have hR2 : R.erase x1 = x2 ::ₘ (R.erase x1).erase x2 :=
      (Multiset.cons_erase hx2e).symm
    rw [hS, hR1, hR2]
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have hnn : 0 ≤ (((R.erase x1).erase x2).map (fun r => (F0.eval r) ^ 2)).sum :=
      Multiset.sum_nonneg (fun s hs => by
        obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hs
        exact sq_nonneg _)
    linarith
  have homega1c : starRingEnd ℂ omegaC + starRingEnd ℂ (starRingEnd ℂ omegaC) = -1 := by
    simpa [star_star, add_comm] using omegaC_add_conj
  have homega2c : starRingEnd ℂ omegaC * starRingEnd ℂ (starRingEnd ℂ omegaC) = 1 := by
    simpa [star_star, mul_comm] using omegaC_mul_conj
  obtain ⟨d1w, b1w, hd1w, hp1w, hb1w, hbl1w⟩ :=
    exists_direction_of_value (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup hx1mem
      omegaC_add_conj omegaC_mul_conj
  obtain ⟨d1c, b1c, hd1c, hp1c, hb1c, hbl1c⟩ :=
    exists_direction_of_value (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup hx1mem
      homega1c homega2c
  obtain ⟨d2w, b2w, hd2w, hp2w, hb2w, hbl2w⟩ :=
    exists_direction_of_value (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup hx2mem
      omegaC_add_conj omegaC_mul_conj
  obtain ⟨d2c, b2c, hd2c, hp2c, hb2c, hbl2c⟩ :=
    exists_direction_of_value (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup hx2mem
      homega1c homega2c
  have hss : (starRingEnd ℂ) ((starRingEnd ℂ) omegaC) = omegaC := by
    rw [starRingEnd_apply, starRingEnd_apply, star_star]
  have hQ1 : b1w * b1c = (F0.eval x1 - α) ^ 2 - 3 * γ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul]
    rw [hb1w, hb1c, hss]
    rw [← hF0, ← hu]
    rw [omegaC_prod (F0.eval x1) u]
  have hQ2 : b2w * b2c = (F0.eval x2 - α) ^ 2 - 3 * γ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul]
    rw [hb2w, hb2c, hss]
    rw [← hF0, ← hu]
    rw [omegaC_prod (F0.eval x2) u]
  have mk : ∀ (d : Fin 6 → ℝ) (b : ℝ), qform (Gram q) d = 0 →
      p3vec q (Lcomb q d) = 3 → bilin (Gram q) P₀ d = b →
      p3vec q (Lcomb q (stereo (Gram q) P₀ d)) = -24 * b ^ 3 := by
    intro d b hd hp hb
    rw [p3vec_Lcomb_stereo_of_qform_zero q hd, hb, hp]
    ring
  have hsome : b1w * b1c < 0 ∨ b2w * b2c < 0 := by
    rcases sign_neg_aux hSbound hgamma hQ1 hQ2 with h | h | ⟨hS0, hα0, hγ0⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hu0 : u = 0 := by
        apply Complex.ext
        · change u.re = 0; rw [← hα]; exact hα0
        · change u.im = 0; rw [← hγ]; exact hγ0
      have hFr : ∀ r ∈ R, F0.eval r = 0 := by
        intro r hr
        have hnn : ∀ s ∈ R.map (fun r => (F0.eval r) ^ 2), (0 : ℝ) ≤ s := by
          intro s hs
          obtain ⟨r', _, rfl⟩ := Multiset.mem_map.mp hs
          exact sq_nonneg _
        have hsum0 : (R.map (fun r => (F0.eval r) ^ 2)).sum = 0 := by
          rw [← hS]; exact hS0
        exact sq_eq_zero_iff.mp
          (Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hnn hsum0 _
            (Multiset.mem_map_of_mem _ hr))
      have hF00 : F0 = 0 := by
        refine eq_zero_of_vanishes_on_roots hnat hsep hF0deg ?_
        intro w hw
        rw [hroots] at hw
        rcases Multiset.mem_cons.mp hw with hw | hw
        · subst hw; rw [← hu]; exact hu0
        · rcases Multiset.mem_cons.mp hw with hw | hw
          · subst hw; rw [eval_map_conj F0 z, ← hu, hu0, map_zero]
          · obtain ⟨r, hr, hrw⟩ := Multiset.mem_map.mp hw
            rw [← hrw, eval_map_ofReal, hFr r hr]; simp
      exact hF0ne hF00
  have key1 : ∀ b : ℝ, b < 0 → (0 : ℝ) < -24 * b ^ 3 := by
    intro b hb; nlinarith [hb, sq_pos_of_ne_zero (ne_of_lt hb)]
  have key2 : ∀ b : ℝ, 0 < b → -24 * b ^ 3 < 0 := by
    intro b hb; nlinarith [hb, sq_pos_of_ne_zero (ne_of_gt hb)]
  rcases hsome with hneg | hneg
  · rcases mul_neg_iff.mp hneg with ⟨hbw, hbc⟩ | ⟨hbw, hbc⟩
    · refine ⟨d1c, d1w, ?_, ?_⟩
      · rw [mk d1c b1c hd1c hp1c hbl1c]; exact key1 b1c hbc
      · rw [mk d1w b1w hd1w hp1w hbl1w]; exact key2 b1w hbw
    · refine ⟨d1w, d1c, ?_, ?_⟩
      · rw [mk d1w b1w hd1w hp1w hbl1w]; exact key1 b1w hbw
      · rw [mk d1c b1c hd1c hp1c hbl1c]; exact key2 b1c hbc
  · rcases mul_neg_iff.mp hneg with ⟨hbw, hbc⟩ | ⟨hbw, hbc⟩
    · refine ⟨d2c, d2w, ?_, ?_⟩
      · rw [mk d2c b2c hd2c hp2c hbl2c]; exact key1 b2c hbc
      · rw [mk d2w b2w hd2w hp2w hbl2w]; exact key2 b2w hbw
    · refine ⟨d2w, d2c, ?_, ?_⟩
      · rw [mk d2w b2w hd2w hp2w hbl2w]; exact key1 b2w hbw
      · rw [mk d2c b2c hd2c hp2c hbl2c]; exact key2 b2c hbc

end

end Pconstructible


/- ==================== inlined from Pptc.S1Sextic ==================== -/


open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### Coefficient-closure helpers

`PConstructible` is closed under the polynomial operations used to assemble the
sextic, but Mathlib only provides the product and constant-multiple closures in
`Pptc.ScratchSep`.  The two `add`/`sub` helpers and the monomial closures below fill
the remaining gaps. -/

private theorem coeff_add_Pc {p r : ℝ[X]}
    (hp : ∀ k, PConstructible (p.coeff k)) (hr : ∀ k, PConstructible (r.coeff k)) :
    ∀ k, PConstructible ((p + r).coeff k) :=
  fun k => by rw [Polynomial.coeff_add]; exact PConstructible.add (hp k) (hr k)

private theorem coeff_sub_Pc {p r : ℝ[X]}
    (hp : ∀ k, PConstructible (p.coeff k)) (hr : ∀ k, PConstructible (r.coeff k)) :
    ∀ k, PConstructible ((p - r).coeff k) :=
  fun k => by rw [Polynomial.coeff_sub]; exact PConstructible.sub (hp k) (hr k)

private theorem coeff_X_Pc : ∀ k, PConstructible (((X : ℝ[X])).coeff k) := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs with h
  · exact PConstructible.base_one
  · exact zero_Pconstructible

private theorem coeff_X_sq_Pc : ∀ k, PConstructible (((X : ℝ[X]) ^ 2).coeff k) := by
  intro k
  rw [pow_two]
  exact coeff_mul_Pconstructible coeff_X_Pc coeff_X_Pc k

/-! ### Degree helpers for the line polynomials -/

private theorem natDegree_C_le' (a : ℝ) : (C a : ℝ[X]).natDegree ≤ 0 := by
  have h := Polynomial.natDegree_C_mul_le a (1 : ℝ[X])
  rwa [mul_one, Polynomial.natDegree_one] at h

private theorem natDegree_lin_le (a b : ℝ) :
    (C a + C b * X : ℝ[X]).natDegree ≤ 1 := by
  refine Polynomial.natDegree_add_le_of_degree_le ?_ ?_
  · exact le_trans (natDegree_C_le' a) (by norm_num)
  · have hX : (X : ℝ[X]).natDegree ≤ 1 := by
      rw [← pow_one (X : ℝ[X])]
      exact Polynomial.natDegree_X_pow_le 1
    exact le_trans (Polynomial.natDegree_C_mul_le b X) hX

private theorem natDegree_quad_le (a b c : ℝ) :
    (C a + C b * X + C c * X ^ 2 : ℝ[X]).natDegree ≤ 2 := by
  refine Polynomial.natDegree_add_le_of_degree_le ?_ ?_
  · exact le_trans (natDegree_lin_le a b) (by norm_num)
  · exact le_trans (Polynomial.natDegree_C_mul_le c (X ^ 2))
      (le_trans (Polynomial.natDegree_X_pow_le 2) (by norm_num))

/-! ### The sextic along the stereographic line

For a fixed P-constructible cone point `P₀` and directions `d`, `δ`, the parametrised
vector `v(m) = stereo (Gram q) P₀ (d + m • δ)` has each coordinate a polynomial of
degree `≤ 2` in `m`, and each `b`-coordinate of `Lcomb q v(m)` likewise.  Substituting
these into the triple-sum formula `p3vec_eq_sum` for the cubic produces a sextic `Ψ`
whose coefficients are P-constructible. -/

-- Theorem: along the stereographic line through a fixed P-constructible cone point,
-- the cubic `p3vec q ∘ Lcomb q ∘ stereo (Gram q) P₀` is a polynomial of degree at most
-- `6` in the line parameter, with P-constructible coefficients.
theorem exists_sextic_along_line (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {P₀ d δ : Fin 6 → ℝ} (hP₀ : ∀ i, PConstructible (P₀ i))
    (hd : ∀ i, PConstructible (d i)) (hδ : ∀ i, PConstructible (δ i)) :
    ∃ Ψ : ℝ[X], (∀ k, PConstructible (Ψ.coeff k)) ∧ Ψ.natDegree ≤ 6 ∧
      ∀ m : ℝ, Ψ.eval m = p3vec q (Lcomb q (stereo (Gram q) P₀ (d + m • δ))) := by
  have hA : (Gram q)ᵀ = Gram q := Gram_symm q
  have hApc : ∀ i j, PConstructible ((Gram q) i j) :=
    fun i j => Gram_Pconstructible q hq i j
  have hqd : PConstructible (qform (Gram q) d) := bilin_Pconstructible hApc hd hd
  have hqδ : PConstructible (qform (Gram q) δ) := bilin_Pconstructible hApc hδ hδ
  have hbd : PConstructible (bilin (Gram q) d δ) := bilin_Pconstructible hApc hd hδ
  have hBPd : PConstructible (bilin (Gram q) P₀ d) := bilin_Pconstructible hApc hP₀ hd
  have hBPδ : PConstructible (bilin (Gram q) P₀ δ) := bilin_Pconstructible hApc hP₀ hδ
  let lineQ : ℝ[X] := C (qform (Gram q) d) + C (2 * bilin (Gram q) d δ) * X
      + C (qform (Gram q) δ) * X ^ 2
  have hlineQdef : lineQ = C (qform (Gram q) d) + C (2 * bilin (Gram q) d δ) * X
      + C (qform (Gram q) δ) * X ^ 2 := rfl
  let lineB : ℝ[X] := C (bilin (Gram q) P₀ d) + C (bilin (Gram q) P₀ δ) * X
  have hlineBdef : lineB = C (bilin (Gram q) P₀ d)
      + C (bilin (Gram q) P₀ δ) * X := rfl
  let stComp : Fin 6 → ℝ[X] := fun i =>
      lineQ * C (P₀ i) - (C 2 * lineB) * (C (d i) + C (δ i) * X)
  have hstCompdef : ∀ i, stComp i = lineQ * C (P₀ i)
      - (C 2 * lineB) * (C (d i) + C (δ i) * X) := fun _ => rfl
  let lineVec : Fin 7 → ℝ[X] := fun i => ∑ j : Fin 6, stComp j * C (bvec q j i)
  have hlineVecdef : ∀ i, lineVec i = ∑ j : Fin 6, stComp j * C (bvec q j i) :=
    fun _ => rfl
  let Ψ : ℝ[X] := ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
      (lineVec i * lineVec j * lineVec k) *
        C (Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val)))
  have hPsiedef : Ψ = ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
      (lineVec i * lineVec j * lineVec k) *
        C (Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val))) := rfl
  -- Evaluation of the line polynomials.
  have hlineQ_eval : ∀ m : ℝ, (lineQ).eval m = qform (Gram q) (d + m • δ) := by
    intro m
    have hq' := qform_smul_add (Gram q) hA 1 m d δ
    rw [one_smul] at hq'
    rw [hlineQdef, hq']
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, one_pow, one_mul]
    ring
  have hlineB_eval : ∀ m : ℝ, (lineB).eval m = bilin (Gram q) P₀ (d + m • δ) := by
    intro m
    rw [hlineBdef, bilin_add_right, bilin_smul_right]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  have hstComp_eval : ∀ (i : Fin 6) (m : ℝ),
      (stComp i).eval m = stereo (Gram q) P₀ (d + m • δ) i := by
    intro i m
    rw [hstCompdef i]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [hlineQ_eval m, hlineB_eval m]
    simp only [stereo, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    ring
  have hlineVec_eval : ∀ (i : Fin 7) (m : ℝ),
      (lineVec i).eval m = (Lcomb q (stereo (Gram q) P₀ (d + m • δ))) i := by
    intro i m
    rw [hlineVecdef i]
    simp only [Lcomb, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hstComp_eval j m]
  -- Coefficient closure.
  have hlineQ_c : ∀ k, PConstructible (lineQ.coeff k) := by
    rw [hlineQdef]
    exact coeff_add_Pc
      (coeff_add_Pc (coeff_C_Pconstructible hqd)
        (coeff_mul_Pconstructible
          (coeff_C_Pconstructible (PConstructible.mul two_Pconstructible hbd)) coeff_X_Pc))
      (coeff_mul_Pconstructible (coeff_C_Pconstructible hqδ) coeff_X_sq_Pc)
  have hlineB_c : ∀ k, PConstructible (lineB.coeff k) := by
    rw [hlineBdef]
    exact coeff_add_Pc (coeff_C_Pconstructible hBPd)
      (coeff_mul_Pconstructible (coeff_C_Pconstructible hBPδ) coeff_X_Pc)
  have hstComp_c : ∀ i k, PConstructible ((stComp i).coeff k) := by
    intro i k
    rw [hstCompdef i]
    refine coeff_sub_Pc ?_ ?_ k
    · exact coeff_mul_Pconstructible hlineQ_c (coeff_C_Pconstructible (hP₀ i))
    · exact coeff_mul_Pconstructible
        (coeff_mul_Pconstructible (coeff_C_Pconstructible two_Pconstructible) hlineB_c)
        (coeff_add_Pc (coeff_C_Pconstructible (hd i))
          (coeff_mul_Pconstructible (coeff_C_Pconstructible (hδ i)) coeff_X_Pc))
  have hlineVec_c : ∀ i k, PConstructible ((lineVec i).coeff k) := by
    intro i k
    rw [hlineVecdef i, coeff_finset_sum]
    refine Finset.sum_Pconstructible Finset.univ _ (fun j _ => ?_)
    exact coeff_mul_Pconstructible (hstComp_c j)
      (coeff_C_Pconstructible (bvec_Pconstructible q hq j i)) k
  have hPsi_c : ∀ n, PConstructible (Ψ.coeff n) := by
    intro n
    rw [hPsiedef, coeff_finset_sum]
    refine Finset.sum_Pconstructible Finset.univ _ (fun i _ => ?_)
    rw [coeff_finset_sum]
    refine Finset.sum_Pconstructible Finset.univ _ (fun j _ => ?_)
    rw [coeff_finset_sum]
    refine Finset.sum_Pconstructible Finset.univ _ (fun k _ => ?_)
    exact coeff_mul_Pconstructible
      (coeff_mul_Pconstructible
        (coeff_mul_Pconstructible (hlineVec_c i) (hlineVec_c j)) (hlineVec_c k))
      (coeff_C_Pconstructible
        (trace_pow_companion7_Pconstructible q hq (i.val + j.val + k.val))) n
  -- Degree bound.
  have hlineQ_deg : lineQ.natDegree ≤ 2 := by
    rw [hlineQdef]
    exact natDegree_quad_le _ _ _
  have hlineB_deg : lineB.natDegree ≤ 1 := by
    rw [hlineBdef]
    exact natDegree_lin_le _ _
  have hstComp_deg : ∀ i, (stComp i).natDegree ≤ 2 := by
    intro i
    rw [hstCompdef i]
    refine le_trans (Polynomial.natDegree_sub_le_of_le ?_ ?_) (le_of_eq (max_self 2))
    · exact le_trans (Polynomial.natDegree_mul_C_le lineQ (P₀ i)) hlineQ_deg
    · exact Polynomial.natDegree_mul_le_of_le
        (le_trans (Polynomial.natDegree_C_mul_le 2 lineB) hlineB_deg)
        (natDegree_lin_le (d i) (δ i))
  have hlineVec_deg : ∀ i, (lineVec i).natDegree ≤ 2 := by
    intro i
    rw [hlineVecdef i]
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin 6))
      (fun j => stComp j * C (bvec q j i)) (fun j _ => ?_)
    exact le_trans (Polynomial.natDegree_mul_C_le (stComp j) (bvec q j i))
      (hstComp_deg j)
  have hPsi_deg : Ψ.natDegree ≤ 6 := by
    rw [hPsiedef]
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin 7))
      (fun i => ∑ j : Fin 7, ∑ k : Fin 7,
        (lineVec i * lineVec j * lineVec k) *
          C (Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val))))
      (fun i _ => ?_)
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin 7))
      (fun j => ∑ k : Fin 7,
        (lineVec i * lineVec j * lineVec k) *
          C (Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val))))
      (fun j _ => ?_)
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin 7))
      (fun k =>
        (lineVec i * lineVec j * lineVec k) *
          C (Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val))))
      (fun k _ => ?_)
    refine le_trans (Polynomial.natDegree_mul_C_le _ _) ?_
    exact Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le (hlineVec_deg i) (hlineVec_deg j))
      (hlineVec_deg k)
  -- Evaluation of the sextic.
  have hPsi_eval : ∀ m : ℝ,
      Ψ.eval m = p3vec q (Lcomb q (stereo (Gram q) P₀ (d + m • δ))) := by
    intro m
    rw [hPsiedef, p3vec_eq_sum]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hlineVec_eval i m, hlineVec_eval j m, hlineVec_eval k m]
  exact ⟨Ψ, hPsi_c, hPsi_deg, hPsi_eval⟩

end

end Pconstructible


/- ==================== inlined from Pptc.S1Final ==================== -/


open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### Continuity of the stereographic cubic

The sign certificate `exists_sign_change` produces *some* real directions on which the cubic
has a prescribed sign; to obtain P-constructible (rational) directions we use density, which
needs continuity of the composite `d ↦ p3vec q (Lcomb q (stereo (Gram q) P₀ d))`.  Everything
in sight is polynomial, so continuity is proved coordinatewise. -/

-- Theorem: `qform` is continuous in its vector argument.
theorem continuous_qform {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun x : Fin n → ℝ => qform A x) := by
  rw [show (fun x : Fin n → ℝ => qform A x)
      = fun x => ∑ j, ∑ k, x j * A j k * x k by
    funext x; rw [qform_eq_sum]]
  fun_prop

-- Theorem: `bilin A y ·` is continuous in its second argument.
theorem continuous_bilin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    Continuous (fun x : Fin n → ℝ => bilin A y x) := by
  rw [show (fun x : Fin n → ℝ => bilin A y x)
      = fun x => ∑ j, ∑ k, y j * A j k * x k by
    funext x; rw [bilin_eq_sum]]
  fun_prop

-- Theorem: `stereo` is continuous in the direction.
theorem continuous_stereo (q : ℝ[X]) (P₀ : Fin 6 → ℝ) :
    Continuous (fun d : Fin 6 → ℝ => stereo (Gram q) P₀ d) := by
  apply continuous_pi
  intro i
  have hq : Continuous (fun d : Fin 6 → ℝ => qform (Gram q) d) := continuous_qform _
  have hb : Continuous (fun d : Fin 6 → ℝ => bilin (Gram q) P₀ d) := continuous_bilin _ _
  have hfun : (fun d : Fin 6 → ℝ => stereo (Gram q) P₀ d i)
      = fun d => qform (Gram q) d * P₀ i - (2 * bilin (Gram q) P₀ d) * d i := by
    funext d
    simp only [stereo, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact (hq.mul continuous_const).sub ((continuous_const.mul hb).mul (continuous_apply i))

-- Theorem: `Lcomb q` is continuous.
theorem continuous_Lcomb (q : ℝ[X]) :
    Continuous (fun v : Fin 6 → ℝ => Lcomb q v) := by
  apply continuous_pi
  intro i
  have hfun : (fun v : Fin 6 → ℝ => Lcomb q v i)
      = fun v => ∑ j : Fin 6, v j * bvec q j i := by
    funext v
    rw [Lcomb, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  fun_prop

-- Theorem: the stereographic cubic is continuous in the direction.
theorem continuous_Phi (q : ℝ[X]) (P₀ : Fin 6 → ℝ) :
    Continuous (fun d : Fin 6 → ℝ => p3vec q (Lcomb q (stereo (Gram q) P₀ d))) :=
  (continuous_p3vec q).comp ((continuous_Lcomb q).comp (continuous_stereo q P₀))

-- Theorem: `stereo` of P-constructible data has P-constructible coordinates.
theorem stereo_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {P₀ d : Fin 6 → ℝ} (hP₀ : ∀ i, PConstructible (P₀ i))
    (hd : ∀ i, PConstructible (d i)) :
    ∀ i, PConstructible (stereo (Gram q) P₀ d i) := by
  intro i
  have hG : ∀ i j, PConstructible (Gram q i j) := Gram_Pconstructible q hq
  have hqform : PConstructible (qform (Gram q) d) := bilin_Pconstructible hG hd hd
  have hbilin : PConstructible (bilin (Gram q) P₀ d) := bilin_Pconstructible hG hP₀ hd
  simp only [stereo, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact PConstructible.sub (PConstructible.mul hqform (hP₀ i))
    (PConstructible.mul (PConstructible.mul (by pconstructible) hbilin) (hd i))

/-! ### The one-conjugate-pair case

With all the pieces in place the proof follows `PLAN-degree7-s1.md` Steps 1-7: build a
P-constructible cone point `P₀`, certify a sign change of the stereographic cubic, round the
witnesses to rational directions, solve the resulting sextic, and feed the recovered
Tschirnhaus polynomial to the tail `root_Pconstructible_of_tschirnhaus`. -/

set_option maxHeartbeats 1000000 in
-- the assembly involves large `ring`/`nlinarith` goals in the non-degeneracy argument
-- Theorem: a real root `β` of a monic separable septic `q` with exactly one non-real
-- conjugate pair `{z, z̄}` is P-constructible.
theorem root_Pconstructible_of_one_conjugate_pair {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 7) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β := by
  classical
  -- Step 1: P-constructible directions with `Q e < 0 < Q f`.
  obtain ⟨fneg, hfnegdeg, hfneg1, hfneg2⟩ := exists_neg_trace q hmon hnat hsep hz hzim
  obtain ⟨fpos, hfposdeg, hfpos1, hfpos2⟩ := exists_pos_trace q hmon hnat hsep hz hzim
  have hvecneg_p1 : p1vec q (vecOf fneg) = 0 := by
    rw [p1vec_vecOf q fneg hfnegdeg, hfneg1]
  have hLneg : Lcomb q (coeff6 (vecOf fneg)) = vecOf fneg := Lcomb_coeff6 q hvecneg_p1
  have hQneg : qform (Gram q) (coeff6 (vecOf fneg)) = -2 := by
    rw [← qform_Hmat_Lcomb q (coeff6 (vecOf fneg)), hLneg, qform_Hmat_eq_hermiteForm,
      hermiteForm_eq_trace_sq, polyOfVec_vecOf hfnegdeg, hfneg2]
  set gpos : ℝ[X] := fpos - C (2 / 7) with hgpos
  have hgposdeg : gpos.natDegree ≤ 6 := by
    rw [hgpos]
    refine le_trans (Polynomial.natDegree_sub_le fpos (C (2 / 7))) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hfposdeg
  have hvecpos_p1 : p1vec q (vecOf gpos) = 0 := by
    rw [p1vec_vecOf q gpos hgposdeg, hgpos, aeval_sub_C, Matrix.trace_sub,
      Matrix.trace_smul, hfpos1, Matrix.trace_one]
    norm_num
  have hLpos : Lcomb q (coeff6 (vecOf gpos)) = vecOf gpos := Lcomb_coeff6 q hvecpos_p1
  have hQpos : qform (Gram q) (coeff6 (vecOf gpos)) = 10 / 7 := by
    rw [← qform_Hmat_Lcomb q (coeff6 (vecOf gpos)), hLpos, qform_Hmat_eq_hermiteForm,
      hermiteForm_eq_trace_sq, polyOfVec_vecOf hgposdeg, hgpos, aeval_sub_C,
      trace_sq_sub_scalar, hfpos1, hfpos2]
    norm_num
  obtain ⟨rneg, hrneg⟩ := exists_rat_vec_pos 6 (continuous_qform (Gram q)).neg
    (x := coeff6 (vecOf fneg)) (by linarith : 0 < -qform (Gram q) (coeff6 (vecOf fneg)))
  obtain ⟨rpos, hrpos⟩ := exists_rat_vec_pos 6 (continuous_qform (Gram q))
    (x := coeff6 (vecOf gpos)) (by linarith : 0 < qform (Gram q) (coeff6 (vecOf gpos)))
  set e : Fin 6 → ℝ := fun i => (rneg i : ℝ) with he
  set f : Fin 6 → ℝ := fun i => (rpos i : ℝ) with hf
  have heP : ∀ i, PConstructible (e i) := fun i => rat_Pconstructible (rneg i)
  have hfP : ∀ i, PConstructible (f i) := fun i => rat_Pconstructible (rpos i)
  have heQ : qform (Gram q) e < 0 := by simpa using hrneg
  have hfQ : 0 < qform (Gram q) f := hrpos
  -- Step 2: a P-constructible point `P₀` on the cone.
  obtain ⟨P₀, hP₀P, hQ₀, hP₀ne⟩ := exists_isotropic_Pconstructible q hq heP hfP heQ hfQ
  -- Step 3: a sign change of the stereographic cubic on the cone.
  obtain ⟨dplus, dminus, hdplus, hdminus⟩ :=
    exists_sign_change hmon hnat hsep hz hzim hone hQ₀ hP₀ne
  -- Step 4: rationalise the two witnesses.
  obtain ⟨rdplus, hrdplus⟩ := exists_rat_vec_pos 6 (continuous_Phi q P₀) (x := dplus) hdplus
  obtain ⟨rdminus, hrdminus⟩ := exists_rat_vec_pos 6 (continuous_Phi q P₀).neg
    (x := dminus) (by linarith : 0 < -p3vec q (Lcomb q (stereo (Gram q) P₀ dminus)))
  set dp : Fin 6 → ℝ := fun i => (rdplus i : ℝ) with hdp
  set dm : Fin 6 → ℝ := fun i => (rdminus i : ℝ) with hdm
  have hdpP : ∀ i, PConstructible (dp i) := fun i => rat_Pconstructible (rdplus i)
  have hdmP : ∀ i, PConstructible (dm i) := fun i => rat_Pconstructible (rdminus i)
  have hPhidp : 0 < p3vec q (Lcomb q (stereo (Gram q) P₀ dp)) := hrdplus
  have hPhidm : p3vec q (Lcomb q (stereo (Gram q) P₀ dm)) < 0 := by simpa using hrdminus
  -- Step 5: the sextic along the line `dp + m • (dm - dp)`.
  set δ : Fin 6 → ℝ := dm - dp with hδ
  have hδP : ∀ i, PConstructible (δ i) := by
    intro i; rw [hδ]; exact PConstructible.sub (hdmP i) (hdpP i)
  obtain ⟨Ψ, hΨc, hΨdeg, hΨeval⟩ := exists_sextic_along_line q hq hP₀P hdpP hδP
  have hΨ0 : 0 < Ψ.eval 0 := by
    rw [hΨeval 0]
    simpa using hPhidp
  have hdm_eq : dp + (1 : ℝ) • δ = dm := by
    rw [hδ]; simp only [one_smul]; abel
  have hΨ1 : Ψ.eval 1 < 0 := by
    rw [hΨeval 1, hdm_eq]
    exact hPhidm
  have hΨne : Ψ ≠ 0 := by
    intro h0; rw [h0, Polynomial.eval_zero] at hΨ0; exact lt_irrefl _ hΨ0
  have hcontOn : ContinuousOn (fun m : ℝ => Ψ.eval m) (Set.Icc (0 : ℝ) 1) :=
    (Polynomial.continuous Ψ).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc (Ψ.eval 1) (Ψ.eval 0) :=
    ⟨le_of_lt hΨ1, le_of_lt hΨ0⟩
  obtain ⟨mstar, hmstar_mem, hmstar_root⟩ :=
    (intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcontOn) hmem
  have hmstar_ne0 : mstar ≠ 0 := by
    intro h0; rw [h0] at hmstar_root; linarith [hΨ0]
  have hmstar_ne1 : mstar ≠ 1 := by
    intro h1; rw [h1] at hmstar_root; linarith [hΨ1]
  have hmstar_pos : 0 < mstar := lt_of_le_of_ne hmstar_mem.1 hmstar_ne0.symm
  have hmstar_lt1 : mstar < 1 := lt_of_le_of_ne hmstar_mem.2 hmstar_ne1
  have hmstarP : PConstructible mstar :=
    root_Pconstructible_le_six_coeffs hΨne hΨdeg hΨc hmstar_root
  set xstar : Fin 6 → ℝ := dp + mstar • δ with hxstar
  have hxstarP : ∀ i, PConstructible (xstar i) := by
    intro i
    simp only [hxstar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.add (hdpP i) (PConstructible.mul hmstarP (hδP i))
  set vstar : Fin 6 → ℝ := stereo (Gram q) P₀ xstar with hvstar
  have hvstarP : ∀ i, PConstructible (vstar i) := stereo_Pconstructible q hq hP₀P hxstarP
  have hQvstar : qform (Gram q) vstar = 0 := qform_stereo_eq_zero (Gram_symm q) hQ₀ xstar
  have hphistar0 : p3vec q (Lcomb q vstar) = 0 := by
    have h := hΨeval mstar
    rw [← hxstar, ← hvstar] at h
    exact h.symm.trans hmstar_root
  -- Step 6: non-degeneracy of `vstar`.
  have hnotpar : ¬ ∃ c : ℝ, xstar = c • P₀ := by
    rintro ⟨c, hc⟩
    set Phiδ : ℝ := p3vec q (Lcomb q (stereo (Gram q) P₀ δ)) with hPhiδ
    have hxstar_eq : dp + mstar • δ = c • P₀ := by rw [← hc, hxstar]
    have hdp_eq : dp = c • P₀ - mstar • δ := by rw [← hxstar_eq, add_sub_cancel_right]
    have hPsi_eq : ∀ m : ℝ, Ψ.eval m = (m - mstar) ^ 6 * Phiδ := by
      intro m
      rw [hΨeval m]
      have hx : dp + m • δ = c • P₀ + (m - mstar) • δ := by rw [hdp_eq]; module
      rw [hx, stereo_smul_add_smul (A := Gram q) (Gram_symm q) hQ₀ c (m - mstar) δ,
        Lcomb_smul, p3vec_smul, ← hPhiδ]
      ring
    have h0 : Ψ.eval 0 = mstar ^ 6 * Phiδ := by rw [hPsi_eq 0]; ring
    have h1 : Ψ.eval 1 = (1 - mstar) ^ 6 * Phiδ := hPsi_eq 1
    have hA : 0 < mstar ^ 6 := pow_pos hmstar_pos 6
    have hB : 0 < (1 - mstar) ^ 6 := pow_pos (by linarith) 6
    nlinarith [hΨ0, hΨ1, h0, h1, hA, hB]
  have hvstar_ne : vstar ≠ 0 := by
    intro hv
    have hsub : qform (Gram q) xstar • P₀
        - (2 * bilin (Gram q) P₀ xstar) • xstar = 0 := by
      rw [← hv, hvstar]; rfl
    by_cases hb : bilin (Gram q) P₀ xstar = 0
    · have hQx : qform (Gram q) xstar = 0 := by
        rw [hb] at hsub
        simp only [mul_zero, zero_smul, sub_zero] at hsub
        exact (smul_eq_zero.mp hsub).resolve_right hP₀ne
      have hb' : bilin (Gram q) xstar P₀ = 0 := by
        rw [← bilin_comm (Gram_symm q) P₀ xstar]; exact hb
      exact hnotpar
        (isotropic_plane_trivial hmon hnat hsep hz hzim hone xstar P₀ hQx hQ₀ hb' hP₀ne)
    · by_cases hQx : qform (Gram q) xstar = 0
      · have hx0 : xstar = 0 := by
          rw [hQx, zero_smul, zero_sub] at hsub
          rw [neg_eq_zero] at hsub
          exact (smul_eq_zero.mp hsub).resolve_left (mul_ne_zero two_ne_zero hb)
        exact hnotpar ⟨0, by rw [hx0, zero_smul]⟩
      · have hx : xstar
            = ((2 * bilin (Gram q) P₀ xstar)⁻¹ * qform (Gram q) xstar) • P₀ := by
          have hrel : qform (Gram q) xstar • P₀
              = (2 * bilin (Gram q) P₀ xstar) • xstar := sub_eq_zero.mp hsub
          have h2b : (2 * bilin (Gram q) P₀ xstar) ≠ 0 := mul_ne_zero two_ne_zero hb
          have h := congrArg (fun v : Fin 6 → ℝ =>
            ((2 * bilin (Gram q) P₀ xstar))⁻¹ • v) hrel
          rw [smul_smul, smul_smul, inv_mul_cancel₀ h2b, one_smul] at h
          exact h.symm
        exact hnotpar ⟨_, hx⟩
  -- Step 7: the Tschirnhaus polynomial and the tail.
  set φ : ℝ[X] := polyOfVec (Lcomb q vstar) with hφ
  have hLne : Lcomb q vstar ≠ 0 := fun h => hvstar_ne (Lcomb_injective q h)
  refine root_Pconstructible_of_tschirnhaus (φ := φ) hmon hnat hsep hq ?_ ?_ ?_ ?_ ?_ ?_ hβ
  · exact polyOfVec_coeff_Pconstructible _ (Lcomb_Pconstructible q hq hvstarP)
  · exact polyOfVec_natDegree_le _
  · rw [hφ]; exact polyOfVec_ne_zero hLne
  · rw [hφ, ← p1vec_eq_trace q (Lcomb q vstar)]; exact p1vec_Lcomb q vstar
  · rw [hφ, ← hermiteForm_eq_trace_sq q (Lcomb q vstar),
      ← qform_Hmat_eq_hermiteForm, qform_Hmat_Lcomb q vstar]
    exact hQvstar
  · rw [hφ]
    change p3vec q (Lcomb q vstar) = 0
    exact hphistar0

/-! ### The literal issue statement

Finally, drop the separability hypothesis by normalising to a monic septic and splitting on
whether a second conjugate pair exists (`root_Pconstructible_of_two_conjugate_pairs`), with
the non-separable branch handled by `root_Pconstructible_of_nonSeparable`. -/

-- Theorem: a real root `β` of any degree-7 polynomial `q` with P-constructible coefficients
-- and a non-real root `z` is P-constructible (the literal statement of issue #6).
theorem root_Pconstructible_of_nonreal_root {q : ℝ[X]} (hnat : q.natDegree = 7)
    (hq : ∀ k, PConstructible (q.coeff k)) {z : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    {β : ℝ} (hβ : q.eval β = 0) : PConstructible β := by
  classical
  have hne : q ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  set q₀ : ℝ[X] := C q.leadingCoeff⁻¹ * q with hq₀
  have hmon : q₀.Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hnat₀ : q₀.natDegree = 7 := by
    rw [hq₀, Polynomial.natDegree_C_mul (inv_ne_zero hlc), hnat]
  have hq₀c : ∀ k, PConstructible (q₀.coeff k) :=
    C_mul_coeff_Pconstructible (inv_Pconstructible (hq q.natDegree)) hq
  have hroot₀ : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 →
      (q₀.map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx
    simp [hq₀, Polynomial.map_mul, hx]
  have hz₀ : (q₀.map (algebraMap ℝ ℂ)).eval z = 0 := hroot₀ z hz
  have hβ₀ : q₀.eval β = 0 := by simp [hq₀, hβ]
  by_cases hsep : q₀.Separable
  · by_cases hsecond : ∃ w : ℂ, (q₀.map (algebraMap ℝ ℂ)).eval w = 0 ∧ w.im ≠ 0 ∧
        w ≠ z ∧ w ≠ starRingEnd ℂ z
    · obtain ⟨w, hw, hwim, hwz, hwz'⟩ := hsecond
      have hzw' : z ≠ starRingEnd ℂ w := by
        intro h
        exact hwz' (by
          have := congrArg (starRingEnd ℂ) h
          simpa using this.symm)
      exact root_Pconstructible_of_two_conjugate_pairs_monic hmon hnat₀ hq₀c hz₀ hzim
        hw hwim hwz.symm hzw' hβ₀
    · have hone : ∀ w : ℂ, (q₀.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
          w = z ∨ w = starRingEnd ℂ z := by
        intro w hw hwim
        by_contra hc
        rcases not_or.mp hc with ⟨hwz, hwz'⟩
        exact hsecond ⟨w, hw, hwim, hwz, hwz'⟩
      exact root_Pconstructible_of_one_conjugate_pair hmon hnat₀ hsep hq₀c hz₀ hzim hone hβ₀
  · exact root_Pconstructible_of_nonSeparable hmon hq₀c (le_of_eq hnat₀) hsep hβ₀

end

end Pconstructible
