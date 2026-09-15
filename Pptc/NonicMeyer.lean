import Pptc.NonicPowerLaw
import Pptc.NonicRecovery
import Pptc.HasseMinkowski.Main

/-! # Pptc.NonicMeyer — degree-9 trace form and the Tschirnhaus reduction

This file models, at degree `9`, the companion-matrix trace apparatus of
`Pptc.DegreeSeven` (`companion9'` here plays the role of `companion7'`), and reduces the
Tschirnhaus problem for the nonic to a single rational trace condition.

The mathematical plan (see `NOTES-nonic-meyer.md`) is:

* `A = ℚ[X]/(q)` for a monic separable `q` of degree `9`, with `Tr` the algebra trace;
* the trace form `Q f = Tr (f²)` restricted to `V = {f : deg ≤ 6, Tr f = 0}` (a
  `6`-dimensional rational quadratic space) is indefinite whenever `q` has a nonreal root;
* Meyer's theorem (`Pptc.HasseMinkowski.meyer`) then produces a nonzero rational `f ∈ V`
  with `Q f = 0`, i.e. `Tr f = Tr (f²) = 0`;
* Newton's identities turn `Tr f = Tr (f²) = 0` into the vanishing of the `X^8` and `X^7`
  coefficients of the resolvent, which is the statement of `exists_tschirnhaus9`.

The last step is fully formalised here: `exists_tschirnhaus9_of_isotropic` proves the
Tschirnhaus statement from the existence of such a rational `f`.  The existence of `f`
(Meyer applied to the indefinite trace form) is the single remaining gap, isolated in
`Nonic.lean`. -/

open Polynomial Matrix Module

namespace Pconstructible

noncomputable section

/-! ### Trace of a power of the degree-9 companion matrix

These copy the degree-7 results over an algebraically closed field, with `Fin 7 → Fin 9`. -/

-- Theorem: the trace of the `k`-th power of the degree-9 companion matrix is the sum of the
-- `k`-th powers of the roots of `q` (with multiplicity).
set_option linter.style.haveILetI false in
theorem companion9'_trace_pow {K : Type*} [Field K] [IsAlgClosed K]
    (q : K[X]) (hmon : q.Monic) (hnat : q.natDegree = 9) (hsep : q.Separable) (k : ℕ) :
    Matrix.trace ((companion9' q) ^ k) = (q.roots.map (fun z => z ^ k)).sum := by
  classical
  have h9 : q.coeff 9 = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ 9 := le_of_eq hnat
  have hnodup : q.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard : q.roots.card = 9 := by
    rw [← hnat]; exact (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  let idx := q.roots.toFinset
  haveI : Nonempty idx := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
      rw [Multiset.toFinset_card_of_nodup hnodup, hcard]; norm_num)
    exact ⟨⟨x, hx⟩⟩
  let v : idx → (Fin 9 → K) := fun z => companionVec9 (z : K)
  have hv : ∀ z : idx, companion9' q *ᵥ v z = (z : K) • v z := by
    intro z
    have hz : q.eval (z : K) = 0 :=
      (Polynomial.mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp z.2)
    exact companion9'_mulVec_companionVec9 hz h9 hdeg
  have hvne : ∀ z : idx, v z ≠ 0 := by
    intro z h0
    have h1 := congrFun h0 0
    simp [v, companionVec9] at h1
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (companion9' q).toLin' (fun z : idx => (z : K))
      Subtype.coe_injective v (fun z =>
        ⟨(Module.End.mem_eigenspace_iff).mpr (by rw [Matrix.toLin'_apply]; exact hv z), hvne z⟩)
  have hcardfin : Fintype.card idx = Module.finrank K (Fin 9 → K) := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcard]
    norm_num
  let b : Basis idx K (Fin 9 → K) := basisOfLinearIndependentOfCardEqFinrank hli hcardfin
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have htrace := trace_pow_eq_sum_eigen ((companion9' q).toLin') b (fun z : idx => (z : K))
    (fun z => by rw [hb]; exact hv z) k
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow, htrace, Finset.sum_coe_sort idx
    (fun z : K => z ^ k)]
  have hval : idx.val = q.roots := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  rw [show (∑ i ∈ idx, i ^ k) = (idx.val.map (fun z => z ^ k)).sum from rfl, hval]

-- Theorem: the trace of any polynomial in the degree-9 companion matrix is the sum over the
-- roots of `q` of the polynomial evaluated there.
theorem companion9'_trace_aeval {K : Type*} [Field K] [IsAlgClosed K]
    (q φ : K[X]) (hmon : q.Monic) (hnat : q.natDegree = 9) (hsep : q.Separable) :
    Matrix.trace (aeval (companion9' q) φ) = (q.roots.map φ.eval).sum := by
  classical
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
        companion9'_trace_pow q hmon hnat hsep n]
      rw [show (q.roots.map (fun x => eval x ((monomial n) a)))
            = q.roots.map (fun z => a * z ^ n) from
          Multiset.map_congr rfl (fun z _ => by rw [Polynomial.eval_monomial])]
      rw [Multiset.sum_map_mul_left]

/-! ### The characteristic polynomial in an eigenbasis -/

-- Theorem: the characteristic polynomial of `φ` evaluated at the degree-9 companion matrix
-- is the product of `X - C (φ.eval z)` over the roots `z` of `q`.
set_option linter.style.haveILetI false in
theorem companion9'_charpoly_aeval_eq_prod {K : Type*} [Field K] [IsAlgClosed K]
    (q φ : K[X]) (hmon : q.Monic) (hnat : q.natDegree = 9) (hsep : q.Separable) :
    (aeval (companion9' q) φ).charpoly
      = (q.roots.map (fun z => Polynomial.X - Polynomial.C (φ.eval z))).prod := by
  classical
  set M : Matrix (Fin 9) (Fin 9) K := companion9' q with hM
  have h9 : q.coeff 9 = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ 9 := le_of_eq hnat
  have hnodup : q.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard : q.roots.card = 9 := by
    rw [← hnat]; exact (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  let idx := q.roots.toFinset
  haveI : Nonempty idx := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
      rw [Multiset.toFinset_card_of_nodup hnodup, hcard]; norm_num)
    exact ⟨⟨x, hx⟩⟩
  let v : idx → (Fin 9 → K) := fun z => companionVec9 (z : K)
  have hv : ∀ z : idx, M *ᵥ v z = (z : K) • v z := by
    intro z
    have hz : q.eval (z : K) = 0 :=
      (Polynomial.mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp z.2)
    exact companion9'_mulVec_companionVec9 hz h9 hdeg
  have hvne : ∀ z : idx, v z ≠ 0 := by
    intro z h0
    have h1 := congrFun h0 0
    simp [v, companionVec9] at h1
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' M.toLin' (fun z : idx => (z : K))
      Subtype.coe_injective v (fun z =>
        ⟨(Module.End.mem_eigenspace_iff).mpr (by rw [Matrix.toLin'_apply]; exact hv z), hvne z⟩)
  have hcardfin : Fintype.card idx = Module.finrank K (Fin 9 → K) := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcard]
    norm_num
  let b : Basis idx K (Fin 9 → K) := basisOfLinearIndependentOfCardEqFinrank hli hcardfin
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

/-! ### Mapping `aeval` along `ℚ → ℂ` -/

-- Theorem: mapping `aeval (companion9' q) φ` along `ℚ → ℂ` is `aeval` of the mapped
-- companion matrix and the mapped polynomial.
theorem companion9_aeval_map_eq_complex (q φ : ℚ[X]) :
    (aeval (companion9' q) φ).map (algebraMap ℚ ℂ)
      = aeval (companion9' (q.map (algebraMap ℚ ℂ))) (φ.map (algebraMap ℚ ℂ)) := by
  rw [show (aeval (companion9' q) φ).map (algebraMap ℚ ℂ)
        = RingHom.mapMatrix (algebraMap ℚ ℂ) (aeval (companion9' q) φ) from
      (RingHom.mapMatrix_apply _ _).symm,
    Polynomial.map_aeval_eq_aeval_map (R := ℚ) (S := Matrix (Fin 9) (Fin 9) ℚ)
      (T := ℂ) (U := Matrix (Fin 9) (Fin 9) ℂ) (φ := algebraMap ℚ ℂ)
      (ψ := RingHom.mapMatrix (algebraMap ℚ ℂ))
      (by ext r i j; by_cases h : i = j <;>
        simp [Matrix.algebraMap_matrix_apply, h])
      φ (companion9' q),
    RingHom.mapMatrix_apply, companion9'_map_eq]

-- Theorem: the trace of the `k`-th power of `aeval (companion9' q) φ` maps to the sum of the
-- `k`-th powers of `φ.eval z` over the complex roots `z` of `q`.
theorem companion9_trace_pow_aeval (q φ : ℚ[X]) (hmon : q.Monic) (hnat : q.natDegree = 9)
    (hsep : q.Separable) (k : ℕ) :
    algebraMap ℚ ℂ (Matrix.trace ((aeval (companion9' q) φ) ^ k))
      = ((q.map (algebraMap ℚ ℂ)).roots.map
          (fun z => ((φ.map (algebraMap ℚ ℂ)).eval z) ^ k)).sum := by
  have hpow : (aeval (companion9' q) φ) ^ k = aeval (companion9' q) (φ ^ k) := by
    rw [map_pow]
  have hmon' : (q.map (algebraMap ℚ ℂ)).Monic := hmon.map (algebraMap ℚ ℂ)
  have hnat' : (q.map (algebraMap ℚ ℂ)).natDegree = 9 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective]; exact hnat
  have hsep' : (q.map (algebraMap ℚ ℂ)).Separable := hsep.map
  rw [hpow, AddMonoidHom.map_trace (algebraMap ℚ ℂ) (aeval (companion9' q) (φ ^ k)),
    companion9_aeval_map_eq_complex q (φ ^ k)]
  rw [companion9'_trace_aeval (q.map (algebraMap ℚ ℂ)) ((φ ^ k).map (algebraMap ℚ ℂ))
    hmon' hnat' hsep']
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro z _
  rw [Polynomial.map_pow, Polynomial.eval_pow]

/-! ### Newton identities: two power sums kill two elementary symmetric functions -/

-- Theorem: if the first two power sums of a multiset vanish, so do `e₁` and `e₂`.
theorem esymm_eq_zero_of_powerSums_two (s : Multiset ℂ)
    (h1 : s.sum = 0) (h2 : (s.map (fun z => z ^ 2)).sum = 0) :
    s.esymm 1 = 0 ∧ s.esymm 2 = 0 := by
  have e1 : s.esymm 1 = 0 := by rw [esymm_one_eq_sum, h1]
  have e2 : s.esymm 2 = 0 := by
    have h := two_mul_esymm_two s
    rw [e1, h1, h2, mul_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  exact ⟨e1, e2⟩

/-! ### The reduction: two vanishing traces kill `X^8` and `X^7` -/

-- Theorem: if `q` is a monic separable nonic over `ℚ` and `φ` has vanishing first two trace
-- power sums at `companion9' q`, then `charpoly (aeval (companion9' q) φ)` has zero `X^8`
-- and `X^7` coefficients.  The eigenvalues of `aeval (companion9' q) φ` are the values
-- `φ z` at the roots `z` of `q`, so the top coefficients are elementary symmetric functions
-- of those values; the trace hypotheses are the vanishing power sums.
theorem charpoly_aeval_coeff_8_7_eq_zero {q φ : ℚ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 9) (hsep : q.Separable)
    (hp1 : Matrix.trace (aeval (companion9' q) φ) = 0)
    (hp2 : Matrix.trace ((aeval (companion9' q) φ) ^ 2) = 0) :
    (aeval (companion9' q) φ).charpoly.coeff 8 = 0 ∧
    (aeval (companion9' q) φ).charpoly.coeff 7 = 0 := by
  classical
  set qC : ℂ[X] := q.map (algebraMap ℚ ℂ) with hqC
  set φC : ℂ[X] := φ.map (algebraMap ℚ ℂ) with hφC
  set y : Multiset ℂ := qC.roots.map (fun z => φC.eval z) with hy
  set N : Matrix (Fin 9) (Fin 9) ℚ := aeval (companion9' q) φ with hN
  set R : ℚ[X] := N.charpoly with hR
  have hmon' : qC.Monic := by rw [hqC]; exact hmon.map _
  have hnat' : qC.natDegree = 9 := by
    rw [hqC, Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective]; exact hnat
  have hsep' : qC.Separable := by rw [hqC]; exact hsep.map
  have hchar : R.map (algebraMap ℚ ℂ)
      = (y.map (fun w => Polynomial.X - Polynomial.C w)).prod := by
    have h1 : R.map (algebraMap ℚ ℂ) = (N.map (algebraMap ℚ ℂ)).charpoly := by
      rw [hR]
      exact (Matrix.charpoly_map N (algebraMap ℚ ℂ)).symm
    have h2 : N.map (algebraMap ℚ ℂ) = aeval (companion9' qC) φC := by
      rw [hN, hqC, hφC]
      exact companion9_aeval_map_eq_complex q φ
    rw [h1, h2]
    simpa only [hy, Multiset.map_map, Function.comp_apply] using
      companion9'_charpoly_aeval_eq_prod qC φC hmon' hnat' hsep'
  have hycard : y.card = 9 := by
    rw [hy, Multiset.card_map]
    rw [show qC.roots.card = qC.natDegree from
      (IsAlgClosed.splits qC).natDegree_eq_card_roots.symm, hnat']
  have hsum_pow (k : ℕ) (hk : Matrix.trace (N ^ k) = 0) :
      (y.map (fun w => w ^ k)).sum = 0 := by
    have h := companion9_trace_pow_aeval q φ hmon hnat hsep k
    rw [hN.symm, hk, map_zero] at h
    rw [h]
    congr 1
    rw [hy, Multiset.map_map]
    rfl
  have h1y : y.sum = 0 := by
    have h := hsum_pow 1 (by rw [pow_one]; exact hp1)
    simpa using h
  have h2y : (y.map (fun w => w ^ 2)).sum = 0 := hsum_pow 2 hp2
  have he := esymm_eq_zero_of_powerSums_two y h1y h2y
  have coeff_eq (k : ℕ) (hk : k ≤ y.card) :
      algebraMap ℚ ℂ (R.coeff k) = (-1) ^ (y.card - k) * y.esymm (y.card - k) := by
    rw [← Polynomial.coeff_map, hchar, Multiset.prod_X_sub_C_coeff y hk]
  have hcoeff (j : ℕ) (hj : j ≤ y.card) (hjesymm : y.esymm j = 0) :
      R.coeff (y.card - j) = 0 := by
    have h := coeff_eq (y.card - j) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hj, hjesymm, mul_zero] at h
    exact (algebraMap ℚ ℂ).injective (by simpa using h)
  refine ⟨?_, ?_⟩
  · have h := hcoeff 1 (by rw [hycard]; norm_num) he.1
    rw [hycard] at h
    norm_num at h
    exact h
  · have h := hcoeff 2 (by rw [hycard]; norm_num) he.2
    rw [hycard] at h
    norm_num at h
    exact h

/-! ### The Hermite (trace) form in the monomial basis `1, X, …, X⁶`

These are the degree-9 copies of `hermiteForm`, `polyOfVec`, `aeval_polyOfVec`,
`aeval_polyOfVec_sq` and `trace_aeval_polyOfVec_sq` of `Pptc.DegreeSeven`. -/

/-- The Hermite (trace) form of `q` in the monomial basis `1, X, …, X⁶`. -/
noncomputable def hermiteForm9 (q : ℚ[X]) (v : Fin 7 → ℚ) : ℚ :=
  ∑ i, ∑ j, v i * Matrix.trace ((companion9' q) ^ (i.val + j.val)) * v j

/-- The polynomial whose coefficient vector is `v` (degree `≤ 6`). -/
noncomputable def polyOfVec9 (v : Fin 7 → ℚ) : ℚ[X] :=
  ∑ i : Fin 7, Polynomial.monomial i.val (v i)

-- Theorem: `aeval` of the coefficient vector is the corresponding matrix polynomial.
theorem aeval_polyOfVec9 (q : ℚ[X]) (v : Fin 7 → ℚ) :
    aeval (companion9' q) (polyOfVec9 v) = ∑ i : Fin 7, v i • (companion9' q) ^ i.val := by
  rw [polyOfVec9, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one]
  rw [Matrix.smul_mul, Matrix.one_mul]

-- Theorem: the square of that matrix polynomial expands into the Hermite basis.
theorem aeval_polyOfVec9_sq (q : ℚ[X]) (v : Fin 7 → ℚ) :
    (aeval (companion9' q) (polyOfVec9 v)) ^ 2 =
      ∑ i : Fin 7, ∑ j : Fin 7, (v i * v j) • (companion9' q) ^ (i.val + j.val) := by
  rw [aeval_polyOfVec9, pow_two, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]

-- Theorem: the Hermite form is the trace of the square of the matrix polynomial.
theorem trace_aeval_polyOfVec9_sq (q : ℚ[X]) (v : Fin 7 → ℚ) :
    Matrix.trace ((aeval (companion9' q) (polyOfVec9 v)) ^ 2) = hermiteForm9 q v := by
  rw [aeval_polyOfVec9_sq, hermiteForm9, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul]
  ring

/-! ### The trace form on the trace-zero subspace `{deg ≤ 6, Tr = 0}`

The trace-zero hyperplane is parametrised by
`v ↦ f_v = ∑_k v_k X^{k+1} - C((∑_k v_k s_{k+1}) / 9)`, `k : Fin 6`, where
`s_m = Tr (M^m)` and `M = companion9' q`.  We prove that `f_v` really has trace zero
(`trace_traceZeroPol`), degree `≤ 6` (`traceZeroPol_natDegree_le`) and coefficient
`v k` in degree `k+1` (`coeff_traceZeroPol`).

The Gram matrix of the trace form in these coordinates is `gramTraceZero`; identifying it
with `Tr (f_v · f_w)` is the algebraic computation that is still missing (see the
`### The remaining gap` section at the end of this file). -/

/-- `s_m = Tr (M^m)`, the `m`-th power sum of the companion matrix of `q`. -/
def ps9 (q : ℚ[X]) (m : ℕ) : ℚ := Matrix.trace ((companion9' q) ^ m)

/-- The Gram matrix of the trace form on the trace-zero subspace `{deg ≤ 6, Tr = 0}`. -/
def gramTraceZero (q : ℚ[X]) : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => ps9 q (i.val + j.val + 2) - ps9 q (i.val + 1) * ps9 q (j.val + 1) / 9

/-- The trace-zero polynomial with coordinate vector `v`. -/
noncomputable def traceZeroPol (q : ℚ[X]) (v : Fin 6 → ℚ) : ℚ[X] :=
  (∑ k : Fin 6, C (v k) * X ^ (k.val + 1))
    - C ((∑ k : Fin 6, v k * ps9 q (k.val + 1)) / 9)

-- Theorem: the polynomial part of `traceZeroPol` has degree at most six.
theorem natDegree_sum_shift_le (v : Fin 6 → ℚ) :
    (∑ k : Fin 6, C (v k) * X ^ (k.val + 1)).natDegree ≤ 6 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

-- Theorem: the trace-zero polynomial has degree at most six.
theorem traceZeroPol_natDegree_le (q : ℚ[X]) (v : Fin 6 → ℚ) :
    (traceZeroPol q v).natDegree ≤ 6 := by
  rw [traceZeroPol]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (natDegree_sum_shift_le v) ?_)
  rw [Polynomial.natDegree_C]
  omega

-- Theorem: the coefficient of `X^{k+1}` in the trace-zero polynomial is `v k`.
theorem coeff_traceZeroPol (q : ℚ[X]) (v : Fin 6 → ℚ) (k : Fin 6) :
    (traceZeroPol q v).coeff (k.val + 1) = v k := by
  rw [traceZeroPol, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega), sub_zero,
    Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (by rintro h; exact hj (Fin.ext (by omega))), mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

-- Theorem: `aeval` of the polynomial part of `traceZeroPol` is the matrix sum.
theorem aeval_sum_shift (q : ℚ[X]) (v : Fin 6 → ℚ) :
    aeval (companion9' q) (∑ k : Fin 6, C (v k) * X ^ (k.val + 1))
      = ∑ k : Fin 6, v k • (companion9' q) ^ (k.val + 1) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]

-- Theorem: the trace of the polynomial part is `∑ k, v k * s_{k+1}`.
theorem trace_aeval_sum_shift (q : ℚ[X]) (v : Fin 6 → ℚ) :
    Matrix.trace (aeval (companion9' q) (∑ k : Fin 6, C (v k) * X ^ (k.val + 1)))
      = ∑ k : Fin 6, v k * ps9 q (k.val + 1) := by
  rw [aeval_sum_shift, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul, ps9]

-- Theorem: `traceZeroPol` really lies in the trace-zero hyperplane.
theorem trace_traceZeroPol (q : ℚ[X]) (v : Fin 6 → ℚ) :
    Matrix.trace (aeval (companion9' q) (traceZeroPol q v)) = 0 := by
  rw [traceZeroPol, map_sub, Matrix.trace_sub, trace_aeval_sum_shift, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  ring

/-! ### The Gram identification `Tr (f_v²) = v ⬝ (gramTraceZero ⬝ v)`

This is Gap 1 of the plan: the quadratic form attached to `gramTraceZero` is exactly the
trace form in the `traceZeroPol` coordinates. -/

-- Theorem: the square of the shifted monomial sum expands into the Gram basis.
theorem sum_shift_sq (v : Fin 6 → ℚ) :
    (∑ k : Fin 6, C (v k) * X ^ (k.val + 1)) ^ 2
      = ∑ i : Fin 6, ∑ j : Fin 6, C (v i * v j) * X ^ (i.val + j.val + 2) := by
  rw [pow_two, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_mul_mul_comm, ← Polynomial.C_mul, ← pow_add,
    show (i.val + 1) + (j.val + 1) = i.val + j.val + 2 from by omega]

-- Theorem: `gramTraceZero` is the matrix of the trace form in `traceZeroPol` coordinates.
theorem trace_sq_traceZeroPol (q : ℚ[X]) (v : Fin 6 → ℚ) :
    Matrix.trace ((aeval (companion9' q) (traceZeroPol q v)) ^ 2)
      = ∑ i, ∑ j, v i * gramTraceZero q i j * v j := by
  set p : ℚ[X] := ∑ k : Fin 6, C (v k) * X ^ (k.val + 1) with hp
  set c : ℚ := (∑ k : Fin 6, v k * ps9 q (k.val + 1)) / 9 with hc
  have hf : traceZeroPol q v = p - C c := by rw [traceZeroPol, hp, hc]
  have hp2 : p ^ 2 = ∑ i : Fin 6, ∑ j : Fin 6,
      C (v i * v j) * X ^ (i.val + j.val + 2) := by
    rw [hp]; exact sum_shift_sq v
  have hp2a : aeval (companion9' q) (p ^ 2)
      = ∑ i : Fin 6, ∑ j : Fin 6, (v i * v j) • (companion9' q) ^ (i.val + j.val + 2) := by
    rw [hp2, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
  have hp2t : Matrix.trace (aeval (companion9' q) (p ^ 2))
      = ∑ i : Fin 6, ∑ j : Fin 6, v i * v j * ps9 q (i.val + j.val + 2) := by
    rw [hp2a, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.trace_smul, smul_eq_mul, ps9]
  have hpt : Matrix.trace (aeval (companion9' q) p) = 9 * c := by
    rw [hp, trace_aeval_sum_shift, hc]
    ring
  have hsq : (p - C c) ^ 2 = p ^ 2 - C (c + c) * p + C c * C c := by
    rw [Polynomial.C_add]
    ring
  have hCcp : aeval (companion9' q) (C (c + c) * p)
      = (c + c) • aeval (companion9' q) p := by
    rw [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.one_mul]
  have hCcc : aeval (companion9' q) (C c * C c)
      = (c * c) • (1 : Matrix (Fin 9) (Fin 9) ℚ) := by
    simp only [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.one_mul, smul_smul]
  have hexp : aeval (companion9' q) (p ^ 2 - C (c + c) * p + C c * C c)
      = aeval (companion9' q) (p ^ 2) - (c + c) • aeval (companion9' q) p
        + (c * c) • (1 : Matrix (Fin 9) (Fin 9) ℚ) := by
    rw [map_add, map_sub, hCcp, hCcc]
  have htr : Matrix.trace (aeval (companion9' q) ((p - C c) ^ 2))
      = (∑ i : Fin 6, ∑ j : Fin 6, v i * v j * ps9 q (i.val + j.val + 2)) - 9 * c ^ 2 := by
    rw [hsq, hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul, Matrix.trace_one, Fintype.card_fin, hp2t, hpt]
    ring
  have hA : ∀ i j : Fin 6,
      v i * (ps9 q (i.val + j.val + 2) - ps9 q (i.val + 1) * ps9 q (j.val + 1) / 9) * v j
        = v i * v j * ps9 q (i.val + j.val + 2)
          - (v i * ps9 q (i.val + 1)) * (v j * ps9 q (j.val + 1)) / 9 := by
    intro i j; ring
  have hsq1 : (∑ k : Fin 6, v k * ps9 q (k.val + 1)) ^ 2
      = ∑ i : Fin 6, ∑ j : Fin 6,
          (v i * ps9 q (i.val + 1)) * (v j * ps9 q (j.val + 1)) := by
    rw [pow_two, Finset.sum_mul_sum]
  have h9 : 9 * ((∑ k : Fin 6, v k * ps9 q (k.val + 1)) / 9) ^ 2
      = (∑ k : Fin 6, v k * ps9 q (k.val + 1)) ^ 2 / 9 := by ring
  have hfin : (∑ i : Fin 6, ∑ j : Fin 6, v i * gramTraceZero q i j * v j)
      = (∑ i : Fin 6, ∑ j : Fin 6, v i * v j * ps9 q (i.val + j.val + 2))
        - 9 * c ^ 2 := by
    rw [hc]
    simp only [gramTraceZero]
    rw [h9, hsq1]
    simp_rw [hA, Finset.sum_sub_distrib, Finset.sum_div]
  rw [← map_pow, hf, htr, ← hfin]

-- Theorem: the Gram matrix of the trace form is symmetric.
theorem gramTraceZero_symm (q : ℚ[X]) : (gramTraceZero q)ᵀ = gramTraceZero q := by
  ext i j
  simp only [Matrix.transpose_apply, gramTraceZero, Nat.add_comm, Nat.add_assoc]
  ring

/-! ### General matrices: the trace form `Tr (f²)` for an arbitrary `A : Mat₉(ℚ)`

The trace-form apparatus of `{deg ≤ 6, Tr = 0}` was stated for the companion matrix
`companion9' q`, but the proofs use nothing about that matrix beyond traces of powers.
We isolate the general statement here, for an arbitrary `A : Matrix (Fin 9) (Fin 9) ℚ`;
the companion specialisations `ps9`, `gramTraceZero`, `traceZeroPol` are related to it by
the `rfl`-bridges below.

Writing `s_m = psOf A m = Tr (A^m)`, the trace-zero polynomial with coordinate `v` is
`tzPolOf A v = ∑_k v_k X^{k+1} - C((∑_k v_k s_{k+1})/9)`, and its Gram matrix is
`gramOf A`.  These are the general forms used by `tschirnhausDatum_of_signs` below, where
`A = aeval (companion9' q) ψ` for a Tschirnhaus transformation `ψ`. -/

/-- The trace condition on a general Tschirnhaus pair `(ψ, f)`: `Tr N = Tr N² = 0` for
`N = aeval (companion9' q) (f.comp ψ)`.  By Newton's identities (`charpoly` coefficients
`8` and `7` of an `9 × 9` matrix are `-Tr N` and `(Tr N² - (Tr N)²)/2`) this is equivalent
to the vanishing of the `X^8`/`X^7` resolvent coefficients used in `exists_tschirnhaus9`. -/
def TschirnhausDatum (q : ℚ[X]) : Prop :=
  ∃ ψ f : ℚ[X], ψ.natDegree ≤ 6 ∧ 1 ≤ ψ.natDegree ∧ f.natDegree ≤ 6 ∧ 1 ≤ f.natDegree ∧
    Matrix.trace (aeval (companion9' q) (f.comp ψ)) = 0 ∧
    Matrix.trace ((aeval (companion9' q) (f.comp ψ)) ^ 2) = 0

/-- `psOf A m = Tr (A^m)`, the `m`-th power sum of the matrix `A`. -/
def psOf (A : Matrix (Fin 9) (Fin 9) ℚ) (m : ℕ) : ℚ := Matrix.trace (A ^ m)

/-- The Gram matrix of the trace form on `{deg ≤ 6, Tr = 0}` for an arbitrary matrix `A`. -/
def gramOf (A : Matrix (Fin 9) (Fin 9) ℚ) : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => psOf A (i.val + j.val + 2) - psOf A (i.val + 1) * psOf A (j.val + 1) / 9

/-- The trace-zero polynomial with coordinate vector `v`, for an arbitrary matrix `A`. -/
noncomputable def tzPolOf (A : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 6 → ℚ) : ℚ[X] :=
  (∑ k : Fin 6, C (v k) * X ^ (k.val + 1))
    - C ((∑ k : Fin 6, v k * psOf A (k.val + 1)) / 9)

-- Theorem: the Gram matrix of the trace form is symmetric.
theorem gramOf_symm (A : Matrix (Fin 9) (Fin 9) ℚ) : (gramOf A)ᵀ = gramOf A := by
  ext i j
  simp only [Matrix.transpose_apply, gramOf, Nat.add_comm, Nat.add_assoc]
  ring

-- Theorem: `aeval` of the monomial sum `∑_k v_k X^{k+1}` is the matrix sum.
theorem aeval_sum_shiftOf (A : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 6 → ℚ) :
    aeval A (∑ k : Fin 6, C (v k) * X ^ (k.val + 1))
      = ∑ k : Fin 6, v k • A ^ (k.val + 1) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]

-- Theorem: the trace of the monomial sum is `∑_k v_k s_{k+1}`.
theorem trace_aeval_sum_shiftOf (A : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 6 → ℚ) :
    Matrix.trace (aeval A (∑ k : Fin 6, C (v k) * X ^ (k.val + 1)))
      = ∑ k : Fin 6, v k * psOf A (k.val + 1) := by
  rw [aeval_sum_shiftOf, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul, psOf]

-- Theorem: the trace of the square of the monomial sum expands in the Gram basis.
theorem trace_aeval_shift_sqOf (A : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 6 → ℚ) :
    Matrix.trace ((aeval A (∑ k : Fin 6, C (v k) * X ^ (k.val + 1))) ^ 2)
      = ∑ i, ∑ j, v i * v j * psOf A (i.val + j.val + 2) := by
  have hp2 : (∑ k : Fin 6, C (v k) * X ^ (k.val + 1)) ^ 2
      = ∑ i : Fin 6, ∑ j : Fin 6, C (v i * v j) * X ^ (i.val + j.val + 2) :=
    sum_shift_sq v
  rw [← map_pow, hp2, map_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    smul_eq_mul, psOf]

-- Theorem: `tzPolOf A v` really lies in the trace-zero hyperplane.
theorem trace_tzPolOf (A : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 6 → ℚ) :
    Matrix.trace (aeval A (tzPolOf A v)) = 0 := by
  rw [tzPolOf, map_sub, Matrix.trace_sub, trace_aeval_sum_shiftOf, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  ring

-- Theorem: the Gram quadratic form equals `Tr (p²) - (Tr p)²/9` for `p = ∑_k v_k X^{k+1}`.
theorem sum_gramOf_eq (A : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 6 → ℚ) :
    (∑ i, ∑ j, v i * gramOf A i j * v j)
      = (∑ i, ∑ j, v i * v j * psOf A (i.val + j.val + 2))
        - (∑ k, v k * psOf A (k.val + 1)) ^ 2 / 9 := by
  have hA : ∀ i j : Fin 6,
      v i * (psOf A (i.val + j.val + 2)
          - psOf A (i.val + 1) * psOf A (j.val + 1) / 9) * v j
        = v i * v j * psOf A (i.val + j.val + 2)
          - (v i * psOf A (i.val + 1)) * (v j * psOf A (j.val + 1)) / 9 := by
    intro i j; ring
  have hsq1 : (∑ k : Fin 6, v k * psOf A (k.val + 1)) ^ 2
      = ∑ i : Fin 6, ∑ j : Fin 6,
          (v i * psOf A (i.val + 1)) * (v j * psOf A (j.val + 1)) := by
    rw [pow_two, Finset.sum_mul_sum]
  simp only [gramOf]
  rw [hsq1]
  simp_rw [hA, Finset.sum_sub_distrib, Finset.sum_div]

-- Theorem: the trace of the square of `tzPolOf A v` is the Gram quadratic form.
theorem trace_sq_tzPolOf (A : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 6 → ℚ) :
    Matrix.trace ((aeval A (tzPolOf A v)) ^ 2)
      = ∑ i, ∑ j, v i * gramOf A i j * v j := by
  set p : ℚ[X] := ∑ k : Fin 6, C (v k) * X ^ (k.val + 1) with hp
  set c : ℚ := (∑ k : Fin 6, v k * psOf A (k.val + 1)) / 9 with hc
  have hf : tzPolOf A v = p - C c := by rw [tzPolOf, hp, hc]
  have hpt : Matrix.trace (aeval A p) = 9 * c := by
    rw [hp, trace_aeval_sum_shiftOf, hc]
    ring
  have hSt : Matrix.trace (aeval A (p ^ 2))
      = ∑ i : Fin 6, ∑ j : Fin 6, v i * v j * psOf A (i.val + j.val + 2) := by
    rw [hp, map_pow]
    exact trace_aeval_shift_sqOf A v
  have hsq : (p - C c) ^ 2 = p ^ 2 - C (c + c) * p + C c * C c := by
    rw [Polynomial.C_add]
    ring
  have hCcp : aeval A (C (c + c) * p) = (c + c) • aeval A p := by
    rw [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.one_mul]
  have hCcc : aeval A (C c * C c) = (c * c) • (1 : Matrix (Fin 9) (Fin 9) ℚ) := by
    simp only [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.one_mul, smul_smul]
  have hexp : aeval A (p ^ 2 - C (c + c) * p + C c * C c)
      = aeval A (p ^ 2) - (c + c) • aeval A p
        + (c * c) • (1 : Matrix (Fin 9) (Fin 9) ℚ) := by
    rw [map_add, map_sub, hCcp, hCcc]
  have htr : Matrix.trace (aeval A ((p - C c) ^ 2))
      = (∑ i : Fin 6, ∑ j : Fin 6, v i * v j * psOf A (i.val + j.val + 2)) - 9 * c ^ 2 := by
    rw [hsq, hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul, Matrix.trace_one, Fintype.card_fin, hSt, hpt]
    ring
  have hfin : (∑ i : Fin 6, ∑ j : Fin 6, v i * gramOf A i j * v j)
      = (∑ i : Fin 6, ∑ j : Fin 6, v i * v j * psOf A (i.val + j.val + 2))
        - 9 * c ^ 2 := by
    rw [sum_gramOf_eq, hc]
    ring
  rw [← map_pow, hf, htr, ← hfin]

-- Theorem: the coefficient of `X^{k+1}` in `tzPolOf A v` is `v k`.
theorem coeff_tzPolOf (A : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 6 → ℚ) (k : Fin 6) :
    (tzPolOf A v).coeff (k.val + 1) = v k := by
  rw [tzPolOf, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega), sub_zero,
    Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (by rintro h; exact hj (Fin.ext (by omega))), mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

-- Theorem: `tzPolOf A v` has degree at most six.
theorem tzPolOf_natDegree_le (A : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 6 → ℚ) :
    (tzPolOf A v).natDegree ≤ 6 := by
  rw [tzPolOf]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (natDegree_sum_shift_le v) ?_)
  rw [Polynomial.natDegree_C]
  omega

-- Theorem: the Gram quadratic form is the shifted trace form `Tr (p²) - (Tr p)²/9`.
theorem gram_eq_trace_shift (A : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 6 → ℚ) :
    (∑ i, ∑ j, v i * gramOf A i j * v j)
      = Matrix.trace ((aeval A (∑ k : Fin 6, C (v k) * X ^ (k.val + 1))) ^ 2)
        - (Matrix.trace (aeval A (∑ k : Fin 6, C (v k) * X ^ (k.val + 1)))) ^ 2 / 9 := by
  have hT : Matrix.trace (aeval A (∑ k : Fin 6, C (v k) * X ^ (k.val + 1)))
      = ∑ k : Fin 6, v k * psOf A (k.val + 1) := trace_aeval_sum_shiftOf A v
  have hS := trace_aeval_shift_sqOf A v
  rw [hT, hS, sum_gramOf_eq]

-- Theorem: `ps9` is `psOf` of the degree-9 companion matrix.
theorem ps9_eq_psOf (q : ℚ[X]) (m : ℕ) : ps9 q m = psOf (companion9' q) m := rfl

-- Theorem: `gramTraceZero` is `gramOf` of the degree-9 companion matrix.
theorem gramTraceZero_eq_gramOf (q : ℚ[X]) : gramTraceZero q = gramOf (companion9' q) := rfl

-- Theorem: `traceZeroPol` is `tzPolOf` of the degree-9 companion matrix.
theorem traceZeroPol_eq_tzPolOf (q : ℚ[X]) (v : Fin 6 → ℚ) :
    traceZeroPol q v = tzPolOf (companion9' q) v := rfl

-- Theorem: `gramOf` vanishes on scalar matrices; used to rule out a constant `ψ`.
theorem gramOf_algebraMap_eq_zero (c : ℚ) :
    gramOf (algebraMap ℚ (Matrix (Fin 9) (Fin 9) ℚ) c) = 0 := by
  have hps : ∀ m : ℕ,
      psOf (algebraMap ℚ (Matrix (Fin 9) (Fin 9) ℚ) c) m = 9 * c ^ m := by
    intro m
    rw [psOf, ← map_pow (algebraMap ℚ (Matrix (Fin 9) (Fin 9) ℚ)),
      Matrix.algebraMap_eq_diagonal, Matrix.trace_diagonal]
    simp [Finset.sum_const, Fintype.card_fin]
  ext i j
  simp only [gramOf, Matrix.zero_apply]
  rw [hps, hps, hps]
  have hpow : c ^ (i.val + j.val + 2) = c ^ (i.val + 1) * c ^ (j.val + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  ring

-- Theorem: the two signs of the general Gram form give the Tschirnhaus datum for `q`.
-- This is the corrected ("ψ ≠ X") form of the degree-9 reduction: an arbitrary rational
-- `ψ` of degree `≤ 6` whose Gram matrix `gramOf (aeval (companion9' q) ψ)` is indefinite
-- yields a Tschirnhaus pair, via Meyer's theorem applied to `.baseChange ℝ`.
theorem tschirnhausDatum_of_signs {q ψ : ℚ[X]} (hψ : ψ.natDegree ≤ 6)
    (hneg : ∃ v : Fin 6 → ℚ,
      ∑ i, ∑ j, v i * gramOf (aeval (companion9' q) ψ) i j * v j < 0)
    (hpos : ∃ v : Fin 6 → ℚ,
      0 < ∑ i, ∑ j, v i * gramOf (aeval (companion9' q) ψ) i j * v j) :
    TschirnhausDatum q := by
  classical
  set A : Matrix (Fin 9) (Fin 9) ℚ := aeval (companion9' q) ψ with hA
  have hψ1 : 1 ≤ ψ.natDegree := by
    by_contra h
    have h0 : ψ.natDegree = 0 := Nat.lt_one_iff.mp (not_le.mp h)
    have hψC : ψ = C (ψ.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (le_of_eq h0)
    have hA0 : A = algebraMap ℚ (Matrix (Fin 9) (Fin 9) ℚ) (ψ.coeff 0) := by
      rw [hA]
      conv_lhs => rw [hψC]
      rw [Polynomial.aeval_C]
    have hgram0 : gramOf (aeval (companion9' q) ψ) = 0 := by
      rw [← hA, hA0]
      exact gramOf_algebraMap_eq_zero (ψ.coeff 0)
    obtain ⟨v, hv⟩ := hneg
    have h0sum : (∑ i : Fin 6, ∑ j : Fin 6, v i * (0 : Matrix (Fin 6) (Fin 6) ℚ) i j * v j)
        = 0 := by simp
    rw [hgram0, h0sum] at hv
    exact lt_irrefl (0 : ℚ) hv
  set G : Matrix (Fin 6) (Fin 6) ℚ := gramOf A with hG
  set Q : QuadraticForm ℚ (Fin 6 → ℚ) := Matrix.toQuadraticForm' G with hQ
  have hQapply : ∀ v : Fin 6 → ℚ, Q v = ∑ i, ∑ j, v i * G i j * v j := by
    intro v
    rw [hQ]
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hbase : ∀ v : Fin 6 → ℚ, Q.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] v) = (Q v : ℝ) := by
    intro v
    rw [QuadraticForm.baseChange_tmul]
    simp [Rat.smul_def]
  obtain ⟨vneg, hvneg⟩ := hneg
  obtain ⟨vpos, hvpos⟩ := hpos
  have hQvneg : Q vneg < 0 := by
    rw [hQapply vneg, hG, hA]
    exact hvneg
  have hQvpos : 0 < Q vpos := by
    rw [hQapply vpos, hG, hA]
    exact hvpos
  have hind : Pptc.HasseMinkowski.Indefinite (Q.baseChange ℝ) := by
    refine ⟨⟨(1 : ℝ) ⊗ₜ[ℚ] vneg, ?_⟩, ⟨(1 : ℝ) ⊗ₜ[ℚ] vpos, ?_⟩⟩
    · rw [hbase vneg]; exact_mod_cast hQvneg
    · rw [hbase vpos]; exact_mod_cast hQvpos
  have hrank : 5 ≤ Module.finrank ℚ (Fin 6 → ℚ) := by simp
  obtain ⟨v, hvne, hvQ⟩ := Pptc.HasseMinkowski.meyer Q hrank hind
  have hvgram : (∑ i, ∑ j, v i * gramOf A i j * v j) = 0 := by
    rw [← hG, ← hQapply v]
    exact hvQ
  set f : ℚ[X] := tzPolOf A v with hf
  have hfdeg : f.natDegree ≤ 6 := by rw [hf]; exact tzPolOf_natDegree_le A v
  have hf1 : 1 ≤ f.natDegree := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hvne
    have hk' : v k ≠ 0 := by simpa using hk
    have hcoeff : f.coeff (k.val + 1) ≠ 0 := by
      rw [hf, coeff_tzPolOf A v k]
      exact hk'
    have := Polynomial.le_natDegree_of_ne_zero hcoeff
    omega
  have htr1 : Matrix.trace (aeval (companion9' q) (f.comp ψ)) = 0 := by
    rw [Polynomial.aeval_comp, ← hA, hf]
    exact trace_tzPolOf A v
  have htr2 : Matrix.trace ((aeval (companion9' q) (f.comp ψ)) ^ 2) = 0 := by
    rw [Polynomial.aeval_comp, ← hA, hf, trace_sq_tzPolOf A v]
    exact hvgram
  exact ⟨ψ, f, hψ, hψ1, hfdeg, hf1, htr1, htr2⟩

/-! ### Assembly: the isotropic trace vector gives the Tschirnhaus pair -/

-- Theorem: given a rational `f` of degree between `1` and `6` with `Tr f = Tr f² = 0`, the
-- Tschirnhaus pair `ψ = X`, `φ = f` kills the `X^8` and `X^7` coefficients of the resolvent.
theorem exists_tschirnhaus9_of_isotropic {q : ℚ[X]} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable)
    (hiso : ∃ f : ℚ[X], 1 ≤ f.natDegree ∧ f.natDegree ≤ 6 ∧
      Matrix.trace (aeval (companion9' q) f) = 0 ∧
      Matrix.trace ((aeval (companion9' q) f) ^ 2) = 0) :
    ∃ ψ φ : ℚ[X], ψ.natDegree ≤ 6 ∧ 1 ≤ ψ.natDegree ∧
      φ.natDegree ≤ 6 ∧ 1 ≤ φ.natDegree ∧
      ((aeval (companion9' q) (φ.comp ψ)).charpoly).coeff 8 = 0 ∧
      ((aeval (companion9' q) (φ.comp ψ)).charpoly).coeff 7 = 0 := by
  obtain ⟨f, hf1, hfdeg, h1, h2⟩ := hiso
  have hcoeff := charpoly_aeval_coeff_8_7_eq_zero hmon h9 hsep h1 h2
  refine ⟨X, f, by simp, by simp, hfdeg, hf1, ?_, ?_⟩
  · simpa using hcoeff.1
  · simpa using hcoeff.2

-- Theorem: a Tschirnhaus pair whose composite is trace-isotropic gives the Tschirnhaus
-- datum of `exists_tschirnhaus9`.  This is the general (`ψ ≠ X`) form of the reduction.
theorem exists_tschirnhaus9_of_isotropic_comp {q ψ f : ℚ[X]} (hmon : q.Monic)
    (h9 : q.natDegree = 9) (hsep : q.Separable)
    (hψ : ψ.natDegree ≤ 6) (hψ1 : 1 ≤ ψ.natDegree) (hf : f.natDegree ≤ 6)
    (hf1 : 1 ≤ f.natDegree)
    (h1 : Matrix.trace (aeval (companion9' q) (f.comp ψ)) = 0)
    (h2 : Matrix.trace ((aeval (companion9' q) (f.comp ψ)) ^ 2) = 0) :
    ∃ ψ₀ φ : ℚ[X], ψ₀.natDegree ≤ 6 ∧ 1 ≤ ψ₀.natDegree ∧
      φ.natDegree ≤ 6 ∧ 1 ≤ φ.natDegree ∧
      ((aeval (companion9' q) (φ.comp ψ₀)).charpoly).coeff 8 = 0 ∧
      ((aeval (companion9' q) (φ.comp ψ₀)).charpoly).coeff 7 = 0 := by
  have hcoeff := charpoly_aeval_coeff_8_7_eq_zero hmon h9 hsep h1 h2
  exact ⟨ψ, f, hψ, hψ1, hf, hf1, hcoeff.1, hcoeff.2⟩

-- Theorem: the Tschirnhaus datum (a general `ψ`) is exactly what `exists_tschirnhaus9`
-- needs.  The converse also holds, by Newton's identities.
theorem exists_tschirnhaus9_of_datum {q : ℚ[X]} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable) (hd : TschirnhausDatum q) :
    ∃ ψ φ : ℚ[X], ψ.natDegree ≤ 6 ∧ 1 ≤ ψ.natDegree ∧
      φ.natDegree ≤ 6 ∧ 1 ≤ φ.natDegree ∧
      ((aeval (companion9' q) (φ.comp ψ)).charpoly).coeff 8 = 0 ∧
      ((aeval (companion9' q) (φ.comp ψ)).charpoly).coeff 7 = 0 := by
  obtain ⟨ψ, f, hψ, hψ1, hf, hf1, h1, h2⟩ := hd
  exact exists_tschirnhaus9_of_isotropic_comp hmon h9 hsep hψ hψ1 hf hf1 h1 h2

/-! ### The remaining gap, and the falsity of the `ψ = X` formulation

**Gap 1 is proved**: `trace_sq_traceZeroPol` identifies `Matrix.toQuadraticForm' (gramTraceZero q)`
on `Fin 6 → ℚ` with the trace form in the `traceZeroPol` coordinates of `{deg ≤ 6, Tr = 0}`.

**Gap 2 as previously stated is FALSE.**  The `ψ = X` subspace need not carry an indefinite
form.  Explicit counterexample:

  `q = (X² + 1)(X + 13)(X + 12)(X + 3)(X + 2)(X - 2)(X - 8)(X - 11)`

is monic, separable, of degree 9, with the nonreal roots `±i`.  Its Gram matrix
`gramTraceZero q` has leading principal minors

  `504, 17062416, 7177780688000, 1120883224656340000000 / 9`,
  `… , 705355934905388066193936000000000000000`,

all positive, so the form is **positive definite**: `Tr (f²) > 0` for every nonzero `f` with
`f.natDegree ≤ 6` and `Tr f = 0`.  Hence

  `¬ Indefinite (QuadraticForm.baseChange ℝ (Matrix.toQuadraticForm' (gramTraceZero q)))`.

So the correct statement must allow a Tschirnhaus transformation `ψ ≠ X`.  The relevant
subspace is `{φ (ψ x) : deg φ ≤ 6} ∩ {Tr = 0}`, and `NOTES-nonic-meyer.md` §2.2/§4 chooses
`ψ` to make its trace form indefinite: `ψ = X` when `r₂ ≥ 3` (dimension count on Hermite's
signature), and a real-collision `ψ` when `r₂ ∈ {1,2}`.  For the counterexample above
(`r₂ = 1`, seven real roots) the collision choice is required.

The two facts still needed to close `exists_tschirnhaus9` are therefore:

1. **The Gram identification for a general `ψ`** — reduce to `trace_sq_traceZeroPol` after
   reparametrising `{φ (ψ x) : deg φ ≤ 6} ∩ {Tr = 0}`;

2. **Existence of an isotropic trace vector for a suitable rational `ψ`** (the
   real-collision + openness/density argument of `NOTES-nonic-meyer.md`, or Hermite's
   signature theorem for the trace form), which then feeds
   `exists_tschirnhaus9_of_isotropic_comp` / `exists_tschirnhaus9_of_datum`.

With those, `Pptc.HasseMinkowski.meyer` (rank `6 ≥ 5`) produces the nonzero isotropic `v`,
and `traceZeroPol`/`coeff_traceZeroPol`/`trace_traceZeroPol` give the datum. -/

end

end Pconstructible
