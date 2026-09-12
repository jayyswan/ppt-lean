import Pptc.ScratchG
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

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
