import Pptc.ScratchF
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

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
