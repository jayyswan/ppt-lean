import Pptc.DegreeSeven

/-! # Pptc.NonicResolvent — degree-9 companion-matrix / resolvent infrastructure

A mechanical generalisation of the degree-7 companion-matrix development in
`Pptc.DegreeSeven` to degree `9`: the generic companion matrix `companion9'`, the real
companion matrix `companion9`, the eigenvector `(1, β, …, β⁸)`, and the fact that `φ β` is
a root of the characteristic polynomial of the resolvent `φ (companion9 q)` whenever `q`
is monic of degree `9` with root `β`.
-/

open Polynomial Matrix

namespace Pconstructible

/-! ### The companion matrix of a degree-9 polynomial -/

/-- The companion matrix of `q`, over an arbitrary commutative ring. -/
def companion9' {R : Type*} [CommRing R] (q : R[X]) : Matrix (Fin 9) (Fin 9) R :=
  fun i j => if i.val = 8 then -q.coeff j.val
             else if j.val = i.val + 1 then 1 else 0

/-- The real companion matrix of `q`. -/
def companion9 (q : ℝ[X]) : Matrix (Fin 9) (Fin 9) ℝ := companion9' q

/-- The vector `(1, z, …, z⁸)`. -/
def companionVec9 {K : Type*} [Monoid K] (z : K) : Fin 9 → K := fun k => z ^ k.val

-- Theorem: the entries of the generic companion matrix are as specified.
theorem companion9'_apply {R : Type*} [CommRing R] (q : R[X]) (i j : Fin 9) :
    companion9' q i j = if i.val = 8 then -q.coeff j.val
      else if j.val = i.val + 1 then 1 else 0 := rfl

-- Theorem: the real companion matrix is the generic companion matrix.
theorem companion9_eq_companion9' (q : ℝ[X]) : companion9 q = companion9' q := rfl

-- Theorem: in every non-last row, multiplication by the companion matrix shifts the vector.
theorem companion9'_mulVec_apply_of_lt {K : Type*} [CommRing K] (q : K[X]) (w : Fin 9 → K)
    {i : Fin 9} (hi : i.val < 8) :
    (companion9' q *ᵥ w) i = w ⟨i.val + 1, by omega⟩ := by
  have hi8 : i.val ≠ 8 := by omega
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single ⟨i.val + 1, by omega⟩]
  · simp [companion9', hi8]
  · intro j _ hne
    have hne' : j.val ≠ i.val + 1 := fun hh => hne (Fin.ext (by simpa using hh))
    simp [companion9', hi8, hne']
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

-- Theorem: the last row of the companion matrix computes `-∑ j, q.coeff j * w j`.
theorem companion9'_mulVec_apply_last {K : Type*} [CommRing K] (q : K[X]) (w : Fin 9 → K) :
    (companion9' q *ᵥ w) ⟨8, by norm_num⟩ = -∑ j : Fin 9, q.coeff j.val * w j := by
  rw [Matrix.mulVec, dotProduct]
  simp only [companion9', ↓reduceIte]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]

-- Theorem: `(1, z, …, z⁸)` is an eigenvector of the companion matrix with eigenvalue `z`,
-- whenever `z` is a root of the monic degree-9 polynomial `q`.
theorem companion9'_mulVec_companionVec9 {K : Type*} [Field K] {q : K[X]} {z : K}
    (hz : q.eval z = 0) (h9 : q.coeff 9 = 1) (hdeg : q.natDegree ≤ 9) :
    companion9' q *ᵥ companionVec9 z = z • companionVec9 z := by
  have hsum : (∑ k ∈ Finset.range 9, q.coeff k * z ^ k) = -z ^ 9 := by
    have h := hz
    rw [Polynomial.eval_eq_sum_range' (p := q) (n := 10) (by omega)] at h
    rw [Finset.sum_range_succ, h9, one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  funext i
  by_cases hi : i.val = 8
  · have hι : i = ⟨8, by norm_num⟩ := Fin.ext (by simpa using hi)
    subst hι
    rw [companion9'_mulVec_apply_last]
    simp only [companionVec9]
    rw [Fin.sum_univ_eq_sum_range (fun k => q.coeff k * z ^ k) 9, hsum, neg_neg]
    simp only [Pi.smul_apply, companionVec9, smul_eq_mul]
    rw [pow_succ']
  · have hlt : i.val < 8 := by have := i.isLt; omega
    rw [companion9'_mulVec_apply_of_lt q (companionVec9 z) hlt]
    simp only [Pi.smul_apply, companionVec9, smul_eq_mul]
    rw [pow_succ']

-- Theorem: `φ β` is a root of the characteristic polynomial of `φ (companion9 q)`, for any
-- root `β` of the monic degree-9 polynomial `q`.
theorem companion9_charpoly_aeval_isRoot {q φ : ℝ[X]} {β : ℝ}
    (hβ : q.eval β = 0) (h9 : q.coeff 9 = 1) (hdeg : q.natDegree ≤ 9) :
    ((aeval (companion9 q) φ).charpoly).eval (φ.eval β) = 0 := by
  rw [companion9_eq_companion9']
  set M := companion9' q with hM
  set v : Fin 9 → ℝ := companionVec9 β with hv
  have hMv : M *ᵥ v = β • v := by
    rw [hM, hv]
    exact companion9'_mulVec_companionVec9 hβ h9 hdeg
  have hvne : v ≠ 0 := by
    intro h0
    have h1 := congrFun h0 0
    simp [hv, companionVec9] at h1
  have hNv : (aeval M φ) *ᵥ v = (φ.eval β) • v :=
    aeval_mulVec_eigenvector_gen M hMv φ
  have hzero : (Matrix.scalar (Fin 9) (φ.eval β) - aeval M φ) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hNv, Matrix.scalar_apply, Matrix.diagonal_const_mulVec, sub_self]
  rw [Matrix.eval_charpoly]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, hzero⟩

end Pconstructible
