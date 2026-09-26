/- Copyright (c) 2024 Lean Community. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file is part of the Pptc (PowerPoint Constructibility) project.
-/

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
import Pptc.TotallyReal.Newton
import Mathlib.LinearAlgebra.Lagrange

/-! # Pptc.TotallyReal.YSpace

The bridge of `TotallyReal/PLAN.md` §2.1 and §2.6: the **y-space** of a monic
polynomial `q` with distinct real roots `αs`.

## The y-space

Write `q` monic of degree `n` with distinct real roots `α₀ … α_{n−1}`, and for
`b : Fin n → ℝ` let `Φ_b(X) = Σ_{k<n} b_k X^k` and

    y(b) = (Φ_b(α₀), …, Φ_b(α_{n−1}))  ∈  ℝⁿ.

Three facts carry the whole plan, and all three are proved here.

1. `b ↦ y(b)` is a **linear isomorphism** (Vandermonde), so a rational `b` gives a dense
   set of `y`'s. This is what makes the open set of good inputs of `Certificate.lean`
   contain a P-constructible input at all (PLAN §2.6).
2. The power sums `pₖ(y(b)) = Σᵢ Φ_b(αᵢ)^k` are **P-constructible** whenever `b` is. The
   reason is that they are *symmetric* in the `αᵢ`, hence polynomials in the power sums
   of the roots, hence in the coefficients of `q` — which are P-constructible by
   hypothesis. Note this is emphatically *not* a statement about the entries of `y(b)`
   themselves: those involve `αᵢ` one at a time and are generally not constructible.
3. `∏ᵢ (X − yᵢ)` is the characteristic polynomial of `Φ_b (companionN q)`, and so has
   **P-constructible coefficients**, again because the matrix entries are.

## Why the trace route, not polynomial expansion

Fact 2 could be proved by expanding `(Σ_k b_k αᵢ^k)^m` and collecting the symmetric
coefficients. It is proved here instead by identifying the power sum with a matrix trace,
`∑ᵢ Φ_b(αᵢ)^m = Tr ((Φ_b (companionN q))^m)`, and then using
`aeval_entries_Pconstructible` and `charpoly_coeff_Pconstructible` — both already
`n`-general in `DegreeSeven.lean`, and both one line. The eigendecomposition that makes
the identification is the same one that gives fact 3 for free.

## The generic companion matrix

`DegreeSeven.lean` hard-codes `Fin 7` in `companion7` and
`trace_pow_companion7_Pconstructible`, and `Nonic/NonicResolvent.lean` hard-codes `Fin 9`.
The octic case needs `Fin 8`, so `companionN` below is the `n`-general version. The
`Fin 7` proofs are already `n`-general in shape — an eigenbasis indexed by `q.roots` — so
the generalisation is mostly about the two hand-computed matrix multiplications.
-/

namespace Pconstructible

open Polynomial Matrix

variable {n : ℕ}

/-! ### The generic companion matrix -/

/-- The companion matrix of `q` over an arbitrary commutative ring: superdiagonal `1`,
last row `-q.coeff 0, …, −q.coeff (n−1)`. -/
noncomputable def companionN' {R : Type*} [CommRing R] (q : R[X]) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i.val = n - 1 then -q.coeff j.val
             else if j.val = i.val + 1 then 1 else 0

/-- The real companion matrix of `q`. -/
noncomputable def companionN (q : ℝ[X]) : Matrix (Fin n) (Fin n) ℝ := companionN' q

/-- The vector `(1, z, …, z^{n−1})`. -/
def companionVecN {K : Type*} [Monoid K] (z : K) : Fin n → K := fun k => z ^ k.val

theorem companionN_map_eq (n : ℕ) {S : Type*} [CommRing S] (f : ℝ →+* S) (q : ℝ[X]) :
    (companionN (n := n) q).map f = companionN' (n := n) (q.map f) := by
  ext i j
  simp only [Matrix.map_apply, companionN, companionN']
  by_cases h : i.val = n - 1 <;> simp [h]

/-- Every entry of `companionN q` is P-constructible when the coefficients of `q` are. -/
theorem companionN_entries_Pconstructible (n : ℕ) (q : ℝ[X])
    (hq : ∀ k, PConstructible (q.coeff k)) (i j : Fin n) :
    PConstructible (companionN (n := n) q i j) := by
  rw [companionN]
  by_cases hi : i.val = n - 1
  · simp only [companionN', hi, ↓reduceIte]
    exact neg_Pconstructible (hq j.val)
  · simp only [companionN', hi, ↓reduceIte]
    by_cases hj : j.val = i.val + 1
    · simp only [hj, ↓reduceIte]
      exact PConstructible.base_one
    · simp only [hj, ↓reduceIte]
      exact zero_Pconstructible

/-- Off the last row, `companionN' q` acts as the shift `(w (i+1))ᵢ`. -/
theorem companionN'_mulVec_apply_of_lt {R : Type*} [CommRing R] (q : R[X]) (w : Fin n → R)
    {i : Fin n} (hi : i.val < n - 1) :
    (companionN' (n := n) q *ᵥ w) i = w ⟨i.val + 1, by omega⟩ := by
  have hi' : i.val ≠ n - 1 := by omega
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single ⟨i.val + 1, by omega⟩]
  · simp [companionN', hi']
  · intro j _ hne
    have hne' : j.val ≠ i.val + 1 := fun hh => hne (Fin.ext (by simpa using hh))
    simp [companionN', hi', hne']
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

/-- On the last row, `companionN' q` is `-q.coeff j`. -/
theorem companionN'_mulVec_apply_last {R : Type*} [CommRing R] (q : R[X]) (w : Fin n → R)
    (hn : 0 < n) :
    (companionN' (n := n) q *ᵥ w) ⟨n - 1, Nat.sub_lt hn (by norm_num : 0 < 1)⟩
      = -∑ j : Fin n, q.coeff j.val * w j := by
  rw [Matrix.mulVec, dotProduct]
  simp only [companionN', ↓reduceIte]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]

/-- The Vandermonde vector at a root of `q` is an eigenvector of the generic companion
matrix, over an arbitrary field. This is the `n`-general `companion7'_mulVec_companionVecC`;
it is stated over an arbitrary `K` because `companionN'_trace_pow` and
`companionN'_charpoly_aeval_eq_prod` need it over an algebraically closed field. -/
theorem companionN'_mulVec_companionVecN {K : Type*} [Field K] {q : K[X]} {z : K}
    (hn : 0 < n) (hqn : q.coeff n = 1) (hdeg : q.natDegree ≤ n) (hz : q.eval z = 0) :
    companionN' (n := n) q *ᵥ companionVecN (n := n) z = z • companionVecN (n := n) z := by
  have hsum : (∑ k ∈ Finset.range n, q.coeff k * z ^ k) = -z ^ n := by
    have h := hz
    rw [Polynomial.eval_eq_sum_range' (p := q) (n := n + 1) (by omega)] at h
    rw [Finset.sum_range_succ, hqn, one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  funext i
  by_cases hi : i.val = n - 1
  · have hι : i = ⟨n - 1, Nat.sub_lt hn (by norm_num : 0 < 1)⟩ := Fin.ext (by simpa using hi)
    subst hι
    rw [companionN'_mulVec_apply_last _ _ hn]
    simp only [companionVecN]
    rw [Fin.sum_univ_eq_sum_range (fun k => q.coeff k * z ^ k) n, hsum, neg_neg]
    simp only [Pi.smul_apply, companionVecN, smul_eq_mul]
    simpa only [Nat.sub_add_cancel (m := 1) (n := n) (by omega : 1 ≤ n)] using
      (pow_succ' z (n - 1))
  · have hlt : i.val < n - 1 := by have := i.isLt; omega
    rw [companionN'_mulVec_apply_of_lt q (companionVecN z) hlt]
    simp only [Pi.smul_apply, companionVecN, smul_eq_mul]
    rw [pow_succ']

/-- The companion matrix maps the Vandermonde vector at a root to that root times itself.

This is the one genuinely `n`-indexed hand computation; `DegreeSeven.lean` proves it for
`Fin 7` as `companion7'_mulVec_companionVecC`. Note the `hqn : q.coeff n = 1`
hypothesis: it is what forces `α = 0` when `n` is the degree, and in that case both
sides are `0`. -/
theorem companionN_mulVec_companionVecN (n : ℕ) (q : ℝ[X]) (hn : 0 < n) (hqn : q.coeff n = 1)
    (hdeg : q.natDegree ≤ n) {α : ℝ} (hα : q.eval α = 0) :
    companionN (n := n) q *ᵥ companionVecN (n := n) α = α • companionVecN (n := n) α := by
  change companionN' (n := n) q *ᵥ companionVecN (n := n) α = α • companionVecN (n := n) α
  exact companionN'_mulVec_companionVecN hn hqn hdeg hα

/-- `Φ_b (α)` is a root of the characteristic polynomial of `Φ_b (companionN q)`. -/
theorem companionN_charpoly_aeval_isRoot (n : ℕ) {q φ : ℝ[X]} {β : ℝ}
    (hβ : q.eval β = 0) (hn : 0 < n) (hqn : q.coeff n = 1) (hdeg : q.natDegree ≤ n) :
    ((aeval (companionN (n := n) q) φ).charpoly).eval (φ.eval β) = 0 := by
  change ((aeval (companionN' (n := n) q) φ).charpoly).eval (φ.eval β) = 0
  set v : Fin n → ℝ := companionVecN (n := n) β with hv
  have hMv : companionN' (n := n) q *ᵥ v = β • v := by
    rw [hv]
    exact companionN_mulVec_companionVecN n q hn hqn hdeg hβ
  have hvne : v ≠ 0 := by
    intro h0
    have h1 := congrFun h0 ⟨0, by omega⟩
    simp [hv, companionVecN] at h1
  have hNv : (aeval (companionN' (n := n) q) φ) *ᵥ v = (φ.eval β) • v :=
    aeval_mulVec_eigenvector_gen (companionN' (n := n) q) hMv φ
  have hzero : (Matrix.scalar (Fin n) (φ.eval β) - aeval (companionN' (n := n) q) φ) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hNv, Matrix.scalar_apply, Matrix.diagonal_const_mulVec, sub_self]
  rw [Matrix.eval_charpoly]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, hzero⟩

/-- Mapping along `ℝ → ℂ`: the trace of the `k`-th power of `Φ (companionN q)` is the sum
of the `k`-th powers of `Φ z` over the complex roots `z` of `q`. -/
theorem companionN'_trace_pow (n : ℕ) {K : Type*} [Field K] [IsAlgClosed K]
    (q φ : K[X]) (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (k : ℕ) :
    Matrix.trace ((aeval (companionN' (n := n) q) φ) ^ k)
      = (q.roots.map (fun z => (φ.eval z) ^ k)).sum := by
  classical
  have hqn : q.coeff n = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ n := le_of_eq hnat
  have hnodup : q.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard : q.roots.card = n := by
    rw [← hnat]; exact (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  have hplain : ∀ (j : ℕ), Matrix.trace ((companionN' (n := n) q) ^ j)
      = (q.roots.map (fun z : K => z ^ j)).sum := by
    intro j
    set M : Matrix (Fin n) (Fin n) K := companionN' (n := n) q with hM
    haveI : Nonempty q.roots.toFinset := by
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
        rw [Multiset.toFinset_card_of_nodup hnodup, hcard]; exact hn)
      exact ⟨⟨x, hx⟩⟩
    set v : q.roots.toFinset → (Fin n → K) := fun z => companionVecN (n := n) (z : K) with hv
    have hvv : ∀ z : q.roots.toFinset, M *ᵥ v z = (z : K) • v z := by
      intro z
      have hz : q.eval (z : K) = 0 :=
        (Polynomial.mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp z.2)
      exact companionN'_mulVec_companionVecN hn hqn hdeg hz
    have hvne : ∀ z : q.roots.toFinset, v z ≠ 0 := by
      intro z h0
      have h1 := congrFun h0 ⟨0, by omega⟩
      simp [v, companionVecN] at h1
    have hli : LinearIndependent K v :=
      Module.End.eigenvectors_linearIndependent' M.toLin' (fun z : q.roots.toFinset => (z : K))
        Subtype.coe_injective v (fun z =>
          ⟨(Module.End.mem_eigenspace_iff).mpr (by rw [Matrix.toLin'_apply]; exact hvv z),
            hvne z⟩)
    have hcardfin : Fintype.card q.roots.toFinset = Module.finrank K (Fin n → K) := by
      rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcard]
      norm_num
    set b : Module.Basis q.roots.toFinset K (Fin n → K) :=
      basisOfLinearIndependentOfCardEqFinrank hli hcardfin with hb
    have hbeq : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have htrace := trace_pow_eq_sum_eigen (Matrix.toLin' M) b
      (fun z : q.roots.toFinset => (z : K)) (fun z => by rw [hbeq]; exact hvv z) j
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow, htrace,
      Finset.sum_coe_sort q.roots.toFinset (fun z : K => z ^ j)]
    have hval : q.roots.toFinset.val = q.roots := by
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
    rw [show (∑ i ∈ q.roots.toFinset, i ^ j)
      = (q.roots.toFinset.val.map (fun z : K => z ^ j)).sum from rfl, hval]
  have htraceeval : ∀ (p : K[X]), Matrix.trace (aeval (companionN' (n := n) q) p)
      = (q.roots.map (fun z : K => p.eval z)).sum := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
        rw [map_add, Matrix.trace_add, hp, hr]
        rw [show (q.roots.map (fun z : K => (p + r).eval z))
              = q.roots.map (fun z : K => p.eval z + r.eval z) from
            Multiset.map_congr rfl (fun z _ => by rw [Polynomial.eval_add])]
        rw [Multiset.sum_map_add]
    | monomial j a =>
        rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
          Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, hplain j]
        rw [← Multiset.sum_map_mul_left]
        apply congrArg Multiset.sum
        exact Multiset.map_congr rfl (fun z _ => by rw [Polynomial.eval_monomial])
  have hpow : (aeval (companionN' (n := n) q) φ) ^ k
      = aeval (companionN' (n := n) q) (φ ^ k) := by
    rw [map_pow]
  rw [hpow, htraceeval]
  apply congrArg Multiset.sum
  exact Multiset.map_congr rfl (fun z _ => by rw [Polynomial.eval_pow])

/-- The characteristic polynomial of `Φ (companionN q)` is `∏_{z ∈ q.roots} (X − Φ z)`. -/
theorem companionN'_charpoly_aeval_eq_prod (n : ℕ) {K : Type*} [Field K] [IsAlgClosed K]
    (q φ : K[X]) (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable) :
    (aeval (companionN' (n := n) q) φ).charpoly
      = (q.roots.map (fun z => Polynomial.X - Polynomial.C (φ.eval z))).prod := by
  classical
  set M : Matrix (Fin n) (Fin n) K := companionN' (n := n) q with hM
  have hqn : q.coeff n = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ n := le_of_eq hnat
  have hnodup : q.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard : q.roots.card = n := by
    rw [← hnat]; exact (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  haveI : Nonempty q.roots.toFinset := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
      rw [Multiset.toFinset_card_of_nodup hnodup, hcard]; exact hn)
    exact ⟨⟨x, hx⟩⟩
  set v : q.roots.toFinset → (Fin n → K) := fun z => companionVecN (n := n) (z : K) with hv
  have hvv : ∀ z : q.roots.toFinset, M *ᵥ v z = (z : K) • v z := by
    intro z
    have hz : q.eval (z : K) = 0 :=
      (Polynomial.mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp z.2)
    exact companionN'_mulVec_companionVecN hn hqn hdeg hz
  have hvne : ∀ z : q.roots.toFinset, v z ≠ 0 := by
    intro z h0
    have h1 := congrFun h0 ⟨0, by omega⟩
    simp [v, companionVecN] at h1
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' M.toLin' (fun z : q.roots.toFinset => (z : K))
      Subtype.coe_injective v (fun z =>
        ⟨(Module.End.mem_eigenspace_iff).mpr (by rw [Matrix.toLin'_apply]; exact hvv z),
          hvne z⟩)
  have hcardfin : Fintype.card q.roots.toFinset = Module.finrank K (Fin n → K) := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcard]
    norm_num
  set b : Module.Basis q.roots.toFinset K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcardfin with hb
  have hbeq : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have heig : ∀ z : q.roots.toFinset,
      (aeval M φ).mulVecLin (b z) = (φ.eval (z : K)) • b z := by
    intro z
    rw [Matrix.mulVecLin_apply, hbeq]
    exact aeval_mulVec_eigenvector_gen M (hvv z) φ
  have hchar := charpoly_eq_prod_of_eigenbasis ((aeval M φ).mulVecLin) b
    (fun z : q.roots.toFinset => φ.eval (z : K)) heig
  rw [Matrix.charpoly_mulVecLin] at hchar
  rw [hM] at hchar
  rw [hchar]
  rw [Finset.prod_coe_sort q.roots.toFinset
    (fun z : K => Polynomial.X - Polynomial.C (φ.eval z))]
  have hval : q.roots.toFinset.val = q.roots := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  rw [show (∏ i ∈ q.roots.toFinset, (Polynomial.X - Polynomial.C (φ.eval i)))
      = (q.roots.toFinset.val.map
          (fun z : K => Polynomial.X - Polynomial.C (φ.eval z))).prod from rfl, hval]

/-- Mapping `aeval (companionN q) φ` along `ℝ → ℂ` is `aeval` of the mapped companion
matrix and the mapped polynomial. The `n`-general `companion7_aeval_map_eq`. -/
theorem companionN_aeval_map_eq (n : ℕ) (q φ : ℝ[X]) :
    (aeval (companionN (n := n) q) φ).map (algebraMap ℝ ℂ)
      = aeval (companionN' (n := n) (q.map (algebraMap ℝ ℂ))) (φ.map (algebraMap ℝ ℂ)) := by
  rw [show (aeval (companionN (n := n) q) φ).map (algebraMap ℝ ℂ)
        = RingHom.mapMatrix (algebraMap ℝ ℂ) (aeval (companionN (n := n) q) φ) from
      (RingHom.mapMatrix_apply _ _).symm,
    Polynomial.map_aeval_eq_aeval_map (R := ℝ) (S := Matrix (Fin n) (Fin n) ℝ)
      (T := ℂ) (U := Matrix (Fin n) (Fin n) ℂ) (φ := algebraMap ℝ ℂ)
      (ψ := RingHom.mapMatrix (algebraMap ℝ ℂ))
      (by ext r i j; by_cases h : i = j <;>
        simp [RingHom.mapMatrix_apply, Matrix.algebraMap_matrix_apply, h])
      φ (companionN (n := n) q),
    RingHom.mapMatrix_apply, companionN_map_eq n]

/-- **PLAN's totally real hypothesis, in the only form used below:** if `q` is monic of
degree `n`, separable, and `αs` is an injective list of its real roots, then its complex
root multiset is exactly the images of the `αs`. This is what makes the power sums and
the characteristic polynomial come out over ℝ again. -/
theorem roots_eq_map_αs {q : ℝ[X]} {αs : Fin n → ℝ} (hmon : q.Monic) (hnat : q.natDegree = n)
    (hsep : q.Separable) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs) :
    (q.map (algebraMap ℝ ℂ)).roots
      = ((Finset.univ : Finset (Fin n)).val.map (fun i : Fin n => (αs i : ℂ))) := by
  classical
  have hmonC : (q.map (algebraMap ℝ ℂ)).Monic := hmon.map (algebraMap ℝ ℂ)
  have hnatC : (q.map (algebraMap ℝ ℂ)).natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]; exact hnat
  have hsepC : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  have hnodupC : (q.map (algebraMap ℝ ℂ)).roots.Nodup := Polynomial.nodup_roots hsepC
  have hcardC : (q.map (algebraMap ℝ ℂ)).roots.card = n := by
    rw [show (q.map (algebraMap ℝ ℂ)).roots.card
        = (q.map (algebraMap ℝ ℂ)).natDegree from
      (IsAlgClosed.splits (q.map (algebraMap ℝ ℂ))).natDegree_eq_card_roots.symm, hnatC]
  have hinj : Function.Injective (fun i : Fin n => (αs i : ℂ)) :=
    fun i j hij => hnd ((algebraMap ℝ ℂ).injective hij)
  have hrootmem : ∀ i : Fin n, (αs i : ℂ) ∈ (q.map (algebraMap ℝ ℂ)).roots := by
    intro i
    rw [Polynomial.mem_roots hmonC.ne_zero]
    exact Polynomial.IsRoot.map (Polynomial.IsRoot.def.mpr (hαs i))
  have hinjOn : Set.InjOn (fun i : Fin n => (αs i : ℂ)) (Finset.univ : Finset (Fin n)) :=
    fun i j _ _ hij => hinj hij
  have hAsub : (Finset.univ : Finset (Fin n)).image (fun i : Fin n => (αs i : ℂ))
      ⊆ (q.map (algebraMap ℝ ℂ)).roots.toFinset := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_def.2 (Multiset.mem_toFinset.mpr (hrootmem i))
  have hAcard : ((Finset.univ : Finset (Fin n)).image (fun i : Fin n => (αs i : ℂ))).card = n := by
    rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hinj, Finset.card_univ,
      Fintype.card_fin]
  have hRcard : ((q.map (algebraMap ℝ ℂ)).roots).toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnodupC, hcardC]
  have hAe : (Finset.univ : Finset (Fin n)).image (fun i : Fin n => (αs i : ℂ))
      = (q.map (algebraMap ℝ ℂ)).roots.toFinset :=
    Finset.eq_of_subset_of_card_le hAsub (by rw [hAcard, hRcard])
  have h1 : Multiset.map (fun i : Fin n => (αs i : ℂ)) (Finset.univ : Finset (Fin n)).val
      = (q.map (algebraMap ℝ ℂ)).roots := by
    have h := congrArg Finset.val hAe
    rw [Finset.image_val_of_injOn hinjOn] at h
    have h2 := Multiset.toFinset_val ((q.map (algebraMap ℝ ℂ)).roots)
    rw [Multiset.dedup_eq_self.mpr hnodupC] at h2
    rwa [h2] at h
  exact h1.symm

/-! ### P-constructibility of the trace machinery -/

/-- Every entry of `Φ (companionN q)` is P-constructible when the coefficients of `q` and
`Φ` are. Immediate from `aeval_entries_Pconstructible`, which is already `n`-general. -/
theorem aeval_companionN_entries_Pconstructible (n : ℕ) (q φ : ℝ[X])
    (hq : ∀ k, PConstructible (q.coeff k)) (hφ : ∀ k, PConstructible (φ.coeff k))
    (i j : Fin n) : PConstructible ((aeval (companionN (n := n) q) φ) i j) := by
  exact aeval_entries_Pconstructible _ (companionN_entries_Pconstructible n q hq) φ hφ i j

/-- The trace of a power of `Φ (companionN q)` is P-constructible. This is the `n`-general
replacement for `trace_pow_companion7_Pconstructible`. -/
@[pconstructible]
theorem trace_pow_companionN_Pconstructible (n : ℕ) (q φ : ℝ[X])
    (hq : ∀ k, PConstructible (q.coeff k)) (hφ : ∀ k, PConstructible (φ.coeff k))
    (k : ℕ) : PConstructible (Matrix.trace ((aeval (companionN (n := n) q) φ) ^ k)) := by
  have hM : ∀ i j : Fin n, PConstructible ((aeval (companionN (n := n) q) φ) i j) :=
    fun i j => aeval_entries_Pconstructible _ (companionN_entries_Pconstructible n q hq) φ hφ i j
  have hpow : ∀ k (i j : Fin n),
      PConstructible (((aeval (companionN (n := n) q) φ) ^ k) i j) := by
    intro k
    induction k with
    | zero =>
        intro i j
        rw [pow_zero, Matrix.one_apply]
        by_cases h : i = j <;> simp [h, zero_Pconstructible, PConstructible.base_one]
    | succ k ih =>
        intro i j
        rw [pow_succ]
        exact matrix_mul_entries_Pconstructible ih hM i j
  rw [Matrix.trace]
  exact Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun i _ => hpow k i i)

/-- Every coefficient of the characteristic polynomial of `Φ (companionN q)` is
P-constructible. Immediate from `charpoly_coeff_Pconstructible`. -/
theorem charpoly_aeval_companionN_coeff_Pconstructible (n : ℕ) (q φ : ℝ[X])
    (hq : ∀ k, PConstructible (q.coeff k)) (hφ : ∀ k, PConstructible (φ.coeff k))
    (k : ℕ) : PConstructible ((aeval (companionN (n := n) q) φ).charpoly.coeff k) := by
  exact charpoly_coeff_Pconstructible _
    (fun i j => aeval_entries_Pconstructible _
      (companionN_entries_Pconstructible n q hq) φ hφ i j) k

/-! ### From a coefficient vector to a polynomial -/

/-- `Φ_b(X) = Σ_{k<n} b_k X^k`, the degree-`< n` polynomial attached to `b`. -/
noncomputable def bPoly (b : Fin n → ℝ) : ℝ[X] := ∑ k, C (b k) * X ^ (k : ℕ)

/-- `bPoly b` has degree `< n`, i.e. `≤ n − 1`.

The `≤` form is the one that holds unconditionally, so that is the statement. (A strict
`< n` version is also true, but only once `0 < n` is assumed: at `n = 0` the sum is
empty, `bPoly b = 0` and `natDegree 0 = 0`, so `natDegree < n` would read `0 < 0`.) -/
theorem bPoly_natDegree_le (b : Fin n → ℝ) : (bPoly b).natDegree ≤ n - 1 := by
  have hle : ∀ k : Fin n, (C (b k) * X ^ (k : ℕ)).natDegree ≤ n - 1 := by
    intro k
    have hlt : k.val < n := k.isLt
    have h := Polynomial.natDegree_C_mul_X_pow_le (b k) k.val
    omega
  rw [bPoly]
  exact Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin n))
    (fun k : Fin n => C (b k) * X ^ (k : ℕ)) (fun k _ => hle k)

/-- `bPoly b` has P-constructible coefficients when `b` does. -/
theorem bPoly_coeff_Pconstructible {b : Fin n → ℝ} (hb : ∀ k, PConstructible (b k))
    (j : ℕ) : PConstructible ((bPoly b).coeff j) := by
  rw [bPoly, Polynomial.finsetSum_coeff]
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun k _ => ?_)
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hj : j = (k : ℕ)
  · rw [hj, if_pos rfl]
    exact hb k
  · rw [if_neg hj]
    exact zero_Pconstructible

/-- The whole `bPoly b` is P-constructible-coefficientwise, i.e. it may be used as the
`φ` argument of every `PConstructible`-coefficient lemma in this file. -/
theorem bPoly_coeffs_Pconstructible {b : Fin n → ℝ} (hb : ∀ k, PConstructible (b k)) :
    ∀ k, PConstructible ((bPoly b).coeff k) :=
  fun k => bPoly_coeff_Pconstructible hb k

/-- The `j`-th coefficient of `bPoly b`, for `j < n`, is `b j`. This is the coefficient
formula that `bPoly_coeff_Pconstructible` uses in summand form. -/
lemma bPoly_coeff' (b : Fin n → ℝ) (j : ℕ) (hj : j < n) :
    (bPoly b).coeff j = b ⟨j, hj⟩ := by
  rw [bPoly, Polynomial.finsetSum_coeff]
  refine (Fintype.sum_eq_single
    (f := fun x : Fin n => (C (b x) * X ^ (x : ℕ)).coeff j) (a := ⟨j, hj⟩) ?_).trans ?_
  · intro k hk
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (fun hc => hk (Fin.ext hc.symm))]
  · simp [Polynomial.coeff_C_mul_X_pow]

/-! ### The y-vector -/

/-- The y-vector of `b` at the root list `αs`: `y i = Φ_b (αs i)`.

Linearity of `y` in `b` is the point of the definition. -/
def yvec (αs : Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ k, b k * (αs i) ^ (k : ℕ)

theorem yvec_eq_bPoly_eval (αs : Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    (bPoly b).eval (αs i) = yvec αs b i := by
  rw [bPoly, Polynomial.eval_finsetSum, yvec]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem yvec_zero (αs : Fin n → ℝ) : yvec αs 0 = 0 := by
  funext i
  simp [yvec]

theorem yvec_add (αs : Fin n → ℝ) (b c : Fin n → ℝ) :
    yvec αs (b + c) = yvec αs b + yvec αs c := by
  funext i
  simp only [yvec, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem yvec_smul (αs : Fin n → ℝ) (s : ℝ) (b : Fin n → ℝ) :
    yvec αs (s • b) = s • yvec αs b := by
  funext i
  simp only [yvec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => mul_assoc _ _ _)

/-- The `m`-th power sum of the y-vector. PLAN's `psumY`; in this file it is
`Newton.lean`'s `psumFinY`, which is the same function. -/
abbrev psumY {n : ℕ} (y : Fin n → ℝ) (m : ℕ) : ℝ := psumFinY y m

-- The entries of a y-vector are **not** P-constructible, and must never be assumed to
-- be. `yvec αs b i = ∑ₖ bₖ · (αs i)^k` involves `αs i` one root at a time, and a root of
-- a P-constructible-coefficient polynomial is in general *not* P-constructible —
-- `PConstructible` is countable (a countable union of finite sets, one per drawable
-- curve), so almost every real is outside it. This is why PLAN §2.6 insists the
-- Tschirnhaus chain be run in `b`-coordinates, and why only the *symmetric* pairings
-- `ymoment2`, `ymoment3`, `yBdot`, `yConicB`, `yNB` below are P-constructible: those are
-- polynomials in the power sums of the roots, hence in the coefficients of `q`.
-- (This was originally stated here as a theorem `yvec_entry_Pconstructible`, which is
-- false for exactly this reason; there is deliberately no such lemma.)

-- NOTE: `psum_yvec_Pconstructible` is stated *after* `trace_pow_eq_psumY` below, because
-- its proof is `trace_pow_companionN_Pconstructible` transported along
-- `trace_pow_eq_psumY`, and a theorem may only use earlier ones.

/-- The power sum of a y-vector is the trace of a power of `Φ_b (companionN q)`. -/
theorem trace_pow_eq_psumY {q : ℝ[X]} {αs : Fin n → ℝ} {b : Fin n → ℝ}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hαs : ∀ i : Fin n, q.eval (αs i) = 0) (hnd : Function.Injective αs) (m : ℕ) :
    Matrix.trace ((aeval (companionN (n := n) q) (bPoly (n := n) b)) ^ m) = psumY (yvec (n := n) αs b) m := by
  have hmonC : (q.map (algebraMap ℝ ℂ)).Monic := hmon.map (algebraMap ℝ ℂ)
  have hnatC : (q.map (algebraMap ℝ ℂ)).natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    exact hnat
  have hsepC : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  have htr : Matrix.trace
        ((aeval (companionN' (n := n) (q.map (algebraMap ℝ ℂ)))
          ((bPoly (n := n) b).map (algebraMap ℝ ℂ))) ^ m)
      = ((q.map (algebraMap ℝ ℂ)).roots.map
          (fun z : ℂ => ((bPoly (n := n) b).map (algebraMap ℝ ℂ)).eval z ^ m)).sum :=
    companionN'_trace_pow n (q.map (algebraMap ℝ ℂ))
      ((bPoly (n := n) b).map (algebraMap ℝ ℂ)) hmonC hn hnatC hsepC m
  have hmap : ((aeval (companionN (n := n) q) (bPoly (n := n) b)) ^ m).map
      ⇑(algebraMap ℝ ℂ)
      = (aeval (companionN' (n := n) (q.map (algebraMap ℝ ℂ)))
          ((bPoly (n := n) b).map (algebraMap ℝ ℂ))) ^ m := by
    rw [Matrix.map_pow, companionN_aeval_map_eq n q (bPoly (n := n) b)]
  have htrace : (algebraMap ℝ ℂ) (Matrix.trace
        ((aeval (companionN (n := n) q) (bPoly (n := n) b)) ^ m))
      = Matrix.trace
        ((aeval (companionN' (n := n) (q.map (algebraMap ℝ ℂ)))
          ((bPoly (n := n) b).map (algebraMap ℝ ℂ))) ^ m) := by
    rw [AddMonoidHom.map_trace, hmap]
  have hsum : ((q.map (algebraMap ℝ ℂ)).roots.map
        (fun z : ℂ => ((bPoly (n := n) b).map (algebraMap ℝ ℂ)).eval z ^ m)).sum
      = (algebraMap ℝ ℂ) (psumY (yvec (n := n) αs b) m) := by
    have hyv : psumY (yvec (n := n) αs b) m
        = ∑ i : Fin n, ((bPoly (n := n) b).eval (αs i)) ^ m := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact congrArg (fun z : ℝ => z ^ m) (yvec_eq_bPoly_eval αs b i).symm
    rw [roots_eq_map_αs hmon hnat hsep hαs hnd, Multiset.map_map, Finset.sum_map_val]
    have hcast : ∀ i : Fin n, ((αs i : ℝ) : ℂ) = algebraMap ℝ ℂ (αs i) := fun _ => rfl
    simp_rw [hcast]
    simp only [Function.comp_apply, Polynomial.eval_map_apply, hyv, ← map_sum, ← map_pow]
  apply (algebraMap ℝ ℂ).injective
  exact htrace.trans (htr.trans hsum)

/-- **PLAN §2.1/§2.6.** Power sums of a P-constructible y-vector are P-constructible. -/
theorem psum_yvec_Pconstructible {q : ℝ[X]} {αs : Fin n → ℝ} {b : Fin n → ℝ}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k))
    (hαs : ∀ i : Fin n, q.eval (αs i) = 0) (hnd : Function.Injective αs)
    (hb : ∀ k, PConstructible (b k)) (m : ℕ) :
    PConstructible (psumY (yvec αs b) m) := by
  rw [← trace_pow_eq_psumY hmon hn hnat hsep hαs hnd m]
  exact trace_pow_companionN_Pconstructible n q (bPoly (n := n) b) hcoef
    (bPoly_coeffs_Pconstructible hb) m

/-- **PLAN §2.1.** The characteristic polynomial of the y-vector is
`∏ᵢ (X − yᵢ)`, and its coefficients are P-constructible. -/
theorem prodSubY_yvec_eq_charpoly_aeval {q : ℝ[X]} {αs : Fin n → ℝ} {b : Fin n → ℝ}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hαs : ∀ i : Fin n, q.eval (αs i) = 0) (hnd : Function.Injective αs) :
    prodSubY (yvec (n := n) αs b) = (aeval (companionN (n := n) q) (bPoly (n := n) b)).charpoly := by
  classical
  have hqn : q.coeff n = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ n := le_of_eq hnat
  set v : Fin n → (Fin n → ℝ) := fun i => companionVecN (n := n) (αs i) with hv
  have hvv : ∀ i : Fin n, companionN (n := n) q *ᵥ v i = (αs i) • v i := by
    intro i
    rw [hv]
    exact companionN_mulVec_companionVecN n q hn hqn hdeg (hαs i)
  have hvne : ∀ i : Fin n, v i ≠ 0 := by
    intro i h0
    have h1 := congrFun h0 ⟨0, by omega⟩
    simp [hv, companionVecN] at h1
  have hli : LinearIndependent ℝ v :=
    Module.End.eigenvectors_linearIndependent' (companionN (n := n) q).toLin' αs hnd v
      (fun i => ⟨(Module.End.mem_eigenspace_iff).mpr
        (by rw [Matrix.toLin'_apply, hvv i]), hvne i⟩)
  have hcardfin : Fintype.card (Fin n) = Module.finrank ℝ (Fin n → ℝ) := by simp
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set bs : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcardfin with hbs
  have hbeq : ⇑bs = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcardfin
  have hvv' : ∀ i : Fin n, companionN (n := n) q *ᵥ bs i = (αs i) • bs i := by
    intro i
    rw [congrFun hbeq i]
    exact hvv i
  have heig : ∀ i : Fin n,
      (aeval (companionN (n := n) q) (bPoly (n := n) b)).mulVecLin (bs i)
        = (yvec (n := n) αs b i) • bs i := by
    intro i
    rw [Matrix.mulVecLin_apply]
    have h1 := aeval_mulVec_eigenvector_gen (companionN (n := n) q) (hvv' i)
      (bPoly (n := n) b)
    rw [h1, yvec_eq_bPoly_eval]
  have hchar := charpoly_eq_prod_of_eigenbasis
    (aeval (companionN (n := n) q) (bPoly (n := n) b)).mulVecLin bs
    (fun i => yvec (n := n) αs b i) heig
  rw [Matrix.charpoly_mulVecLin] at hchar
  exact hchar.symm

theorem prodSubY_yvec_coeff_Pconstructible {q : ℝ[X]} {αs : Fin n → ℝ} {b : Fin n → ℝ}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs) (hb : ∀ k, PConstructible (b k)) (k : ℕ) :
    PConstructible ((prodSubY (yvec αs b)).coeff k) := by
  rw [prodSubY_yvec_eq_charpoly_aeval hmon hn hnat hsep hαs hnd]
  exact charpoly_aeval_companionN_coeff_Pconstructible n q (bPoly (n := n) b) hcoef
    (bPoly_coeffs_Pconstructible hb) k

/-- A y-vector of a P-constructible `b` is a real root of the corresponding characteristic
polynomial: `Φ_b (α)` for a root `α` of `q` is one of the `yᵢ`. -/
theorem eval_prodSubY_yvec {q : ℝ[X]} {αs : Fin n → ℝ} {b : Fin n → ℝ}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k))
    (hαs : ∀ i : Fin n, q.eval (αs i) = 0) (hnd : Function.Injective αs)
    (hb : ∀ k, PConstructible (b k)) {i : Fin n} :
    (prodSubY (yvec αs b)).eval (yvec αs b i) = 0 := by
  exact eval_prodSubY (yvec αs b) i

/-! ### Power sums of the roots, and symmetric functionals of y-vectors

Everything the odd Tschirnhaus chain needs to know about P-constructibility rests on one
observation: a functional of y-vectors that is **symmetric in the `αᵢ`** is a polynomial
in the power sums of the `αᵢ`, hence in the coefficients of `q`, hence
P-constructible. The entries of a y-vector are *not* symmetric and are *not*
constructible; their power sums, and every symmetric pairing below, are.

The expansion that makes this usable is `yBdot_eq_sum` / `yConicB_eq_sum` / `yNB_eq_sum`:
writing `x^a` as a product of `a` copies of `x` turns `Σᵢ (YP i)^a (YV i)^b` into a sum
over `Fin n × Fin n × Fin n`, each summand a product of `b`-vector entries times one power
sum of the roots. That is the form in which `pconstructible` can finish the job.
(The general `a, b` index-list form that used to be claimed here is false; see the
docstring of `yBdot_eq_sum`.)
-/

/-- The `m`-th power sum of the roots: `∑ᵢ αᵢ^m`. -/
def psumRoots {n : ℕ} (αs : Fin n → ℝ) (m : ℕ) : ℝ := ∑ i, (αs i) ^ m

/-- The `m`-th power sum of the roots is the trace of the `m`-th power of the companion
matrix. Proved over `ℂ` by `companionN'_trace_pow` at `φ = X`, then brought back to `ℝ`
through `companionN_map_eq` and `roots_eq_map_αs`. -/
theorem psumRoots_eq_trace {q : ℝ[X]} {αs : Fin n → ℝ} (hmon : q.Monic) (hn : 0 < n)
    (hnat : q.natDegree = n) (hsep : q.Separable) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs) (m : ℕ) :
    Matrix.trace ((companionN (n := n) q) ^ m) = psumRoots αs m := by
  have hmonC : (Polynomial.map (algebraMap ℝ ℂ) q).Monic := hmon.map (algebraMap ℝ ℂ)
  have hnatC : (Polynomial.map (algebraMap ℝ ℂ) q).natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    exact hnat
  have hsepC : (Polynomial.map (algebraMap ℝ ℂ) q).Separable := hsep.map
  have htr : Matrix.trace
        ((aeval (companionN' (n := n) (Polynomial.map (algebraMap ℝ ℂ) q))
          (Polynomial.X : ℂ[X])) ^ m)
      = (Multiset.map (fun z : ℂ => Polynomial.eval z Polynomial.X ^ m)
          (Polynomial.map (algebraMap ℝ ℂ) q).roots).sum :=
    companionN'_trace_pow n (Polynomial.map (algebraMap ℝ ℂ) q) Polynomial.X
      hmonC hn hnatC hsepC m
  have hmap : ((companionN (n := n) q) ^ m).map ⇑(algebraMap ℝ ℂ)
      = (companionN' (n := n) (Polynomial.map (algebraMap ℝ ℂ) q)) ^ m := by
    rw [Matrix.map_pow, companionN_map_eq]
  have htrace : (algebraMap ℝ ℂ) (Matrix.trace ((companionN (n := n) q) ^ m))
      = Matrix.trace ((companionN' (n := n) (Polynomial.map (algebraMap ℝ ℂ) q)) ^ m) := by
    rw [AddMonoidHom.map_trace, hmap]
  have hps : (∑ i : Fin n, ((αs i : ℂ)) ^ m) = algebraMap ℝ ℂ (psumRoots αs m) := by
    simp [psumRoots, ← map_sum, ← map_pow]
  have hpa : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ),
      (aeval M (Polynomial.X : ℂ[X])) ^ k = M ^ k := by
    intro M k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, pow_succ, Polynomial.aeval_X]
  rw [hpa] at htr
  have hsum : (Multiset.map (fun z : ℂ => Polynomial.eval z Polynomial.X ^ m)
      (Polynomial.map (algebraMap ℝ ℂ) q).roots).sum = psumRoots αs m := by
    rw [roots_eq_map_αs hmon hnat hsep hαs hnd, Multiset.map_map]
    simp only [Function.comp_apply, Polynomial.eval_X]
    rw [Finset.sum_map_val]
    exact hps
  have htr'' : (algebraMap ℝ ℂ) (Matrix.trace ((companionN (n := n) q) ^ m))
      = (Multiset.map (fun z : ℂ => Polynomial.eval z Polynomial.X ^ m)
          (Polynomial.map (algebraMap ℝ ℂ) q).roots).sum := htrace.trans htr
  have hkey : (algebraMap ℝ ℂ) (psumRoots αs m)
      = (Multiset.map (fun z : ℂ => Polynomial.eval z Polynomial.X ^ m)
          (Polynomial.map (algebraMap ℝ ℂ) q).roots).sum := by
    exact hsum.symm
  apply (algebraMap ℝ ℂ).injective
  exact htr''.trans hkey.symm

-- Every power sum of the roots is P-constructible, for every `m` and whatever `n` is.
-- This is the single primitive that the three `_Pconstructible` y-space pairings below
-- are built from.
--
-- **There is deliberately no theorem here by the name `psumRoots_Pconstructible`.** The
-- statement one would want,
--
--     PConstructible (psumRoots αs m)
--
-- from only `hcoef : ∀ k, PConstructible (q.coeff k)` and
-- `hαs : ∀ i : Fin n, q.eval (αs i) = 0`, is FALSE. With `n = 1`, `m = 1`,
-- `q = X ^ 3 - 2` and `αs = fun _ => ∛2`, both hypotheses hold (the coefficients are
-- rational, and `∛2` is a root) while the conclusion reads `PConstructible ∛2`, which is
-- false. What is missing is that `αs` must enumerate *all* the roots of `q` — i.e.
-- `hmon : q.Monic`, `hn : 0 < n`, `hnat : q.natDegree = n`, `hsep : q.Separable`,
-- `hnd : Function.Injective αs`, exactly the hypotheses of `psumRoots_eq_trace`. With
-- those added the proof is one line. The statement that *is* true, with those five
-- hypotheses, is `psumRoots_Pconstructible_of_roots` immediately below; use that one.
/-- Every power sum of the roots is P-constructible, for every `m`.

This is `psumRoots_Pconstructible_with_too_few_hypotheses` (the false statement commented
out above) with the five hypotheses that statement is missing — that `αs` enumerates *all*
the roots of `q`, as separate real roots — and it is proved in the one line the comment
above predicts. -/
theorem psumRoots_Pconstructible_of_roots {q : ℝ[X]} {αs : Fin n → ℝ}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k))
    (hαs : ∀ i : Fin n, q.eval (αs i) = 0) (hnd : Function.Injective αs) (m : ℕ) :
    PConstructible (psumRoots αs m) := by
  have htr : PConstructible (Matrix.trace ((companionN (n := n) q) ^ m)) := by
    have heq : ∀ k : ℕ, ((aeval (companionN (n := n) q)) (Polynomial.X : ℝ[X])) ^ k
        = (companionN (n := n) q) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ih, pow_succ, Polynomial.aeval_X]
    have h1 := trace_pow_companionN_Pconstructible n q Polynomial.X hcoef
      (fun k => by simp [Polynomial.coeff_X] <;> split <;> pconstructible) m
    rw [heq m] at h1
    exact h1
  rw [← psumRoots_eq_trace hmon hn hnat hsep hαs hnd m]
  exact htr

/-- A symmetric pairing of three plain `n`-vectors:
`Σᵢ uᵢ^a vᵢ^b wᵢ^c`. This is the object the odd Tschirnhaus chain actually works with;
`ymoment3` below is its lift to `b`-vectors. -/
def ymoment3Y {n : ℕ} (u v w : Fin n → ℝ) (a b c : ℕ) : ℝ :=
  ∑ i, u i ^ a * v i ^ b * w i ^ c

/-- A symmetric moment of two plain `n`-vectors: `Σᵢ uᵢ^a vᵢ^b`. -/
def ymoment2Y {n : ℕ} (u v : Fin n → ℝ) (a b : ℕ) : ℝ := ∑ i, u i ^ a * v i ^ b

/-- `ymoment3Y` at the y-vectors of three `b`-vectors. -/
def ymoment3 {n : ℕ} (αs : Fin n → ℝ) (u v w : Fin n → ℝ) (a b c : ℕ) : ℝ :=
  ymoment3Y (yvec αs u) (yvec αs v) (yvec αs w) a b c

/-- `ymoment2Y` at the y-vectors of two `b`-vectors. -/
def ymoment2 {n : ℕ} (αs : Fin n → ℝ) (u v : Fin n → ℝ) (a b : ℕ) : ℝ :=
  ymoment2Y (yvec αs u) (yvec αs v) a b

/-- The bilinear pairing `⟨P; u, v⟩ = Σᵢ YP i · Yu i · Yv i` of the y-space. -/
def yBdot {n : ℕ} (αs : Fin n → ℝ) (P u v : Fin n → ℝ) : ℝ :=
  ymoment3Y (yvec αs P) (yvec αs u) (yvec αs v) 1 1 1

/-- The quadratic form `Q_P(u) = Σᵢ YP i · Yu i²` of the y-space. -/
def yConicB {n : ℕ} (αs : Fin n → ℝ) (P u : Fin n → ℝ) : ℝ :=
  ymoment2Y (yvec αs P) (yvec αs u) 1 2

/-- The subspace `N_P = {v : Σᵢ (YP i)² · Yv i = 0}` of the y-space. -/
def yNB {n : ℕ} (αs : Fin n → ℝ) (P v : Fin n → ℝ) : ℝ :=
  ymoment2Y (yvec αs P) (yvec αs v) 2 1

/-- The pairing written on y-vectors. This is the form the chain algebra uses. -/
def yBdotY {n : ℕ} (YP Yu Yv : Fin n → ℝ) : ℝ := ymoment3Y YP Yu Yv 1 1 1

/-- The conic form written on y-vectors. -/
def yConicY {n : ℕ} (YP Yu : Fin n → ℝ) : ℝ := ymoment2Y YP Yu 1 2

/-- The `N_P` pairing written on y-vectors. -/
def yNBY {n : ℕ} (YP Yv : Fin n → ℝ) : ℝ := ymoment2Y YP Yv 2 1

@[simp] theorem yBdot_eq_yBdotY {n : ℕ} (αs : Fin n → ℝ) (P u v : Fin n → ℝ) :
    yBdot αs P u v = yBdotY (yvec αs P) (yvec αs u) (yvec αs v) := rfl

@[simp] theorem yConicB_eq_yConicY {n : ℕ} (αs : Fin n → ℝ) (P u : Fin n → ℝ) :
    yConicB αs P u = yConicY (yvec αs P) (yvec αs u) := rfl

@[simp] theorem yNB_eq_yNBY {n : ℕ} (αs : Fin n → ℝ) (P v : Fin n → ℝ) :
    yNB αs P v = yNBY (yvec αs P) (yvec αs v) := rfl

/-- The three y-space pairings, as explicit triple sums over `Fin n × Fin n × Fin n`.

Each of these is a sum of **three** factors of y-entries, so the product expands with no
index coupling: `Σᵢ YPᵢ·YUᵢ·YVᵢ = Σ_{k,l,j} P_k U_l V_j · psumRoots αs (k+l+j)`, since the
`αᵢ` all appear in separate factors and the single surviving sum is `Σᵢ αᵢ^{k+l+j}`.
Every factor on the right is P-constructible once the `b`-entries are, which is the whole
point.

Higher moments — `Σᵢ (YPᵢ)^{m−t} (YVᵢ)^t` for `m > 3` — do **not** have this form: there
the powers of the *same* y-entry are coupled, and a single `psumRoots` cannot represent
them. (An earlier version of this file asserted a `Fin (a+b) → Fin n` index-list form
for general `a, b`; that is false, e.g. `n = 1`, `a = b = 1`, `u = v = 1`, `αs = 3` gives
`1` on the left and `9` on the right.) They are reached instead by `psumY_line_poly`
below, which reads the coefficients off the values by interpolation. -/

-- The four-fold sum over `Fin n` factors: the sum over the roots commutes past the
-- three sums over `b`-indices. Only the innermost pair can be swapped with a bare
-- `Finset.sum_comm`, so the other two are swapped under the binders.
private theorem sum_comm4 {n : ℕ} (g : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ k, ∑ l, ∑ j, g i k l j) = ∑ k, ∑ l, ∑ j, ∑ i, g i k l j := by
  calc (∑ i, ∑ k, (∑ l, ∑ j, g i k l j))
      = ∑ k, ∑ i, (∑ l, ∑ j, g i k l j) := Finset.sum_comm
    _ = ∑ k, ∑ l, (∑ i, ∑ j, g i k l j) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ j, (∑ i, g i k l j) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun l _ => ?_)
        exact Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ j, ∑ i, g i k l j := rfl

/-- Three y-entries at a common root, expanded: the three factors are independent, so
the product becomes a triple sum over `b`-indices with the powers of `αs i` still split. -/
private theorem yvec_mul3_eq_sum {n : ℕ} (αs : Fin n → ℝ) (A B C : Fin n → ℝ) (i : Fin n) :
    yvec αs A i * yvec αs B i * yvec αs C i
      = ∑ k : Fin n, ∑ l : Fin n, ∑ j : Fin n,
          (A k * B l * C j) * ((αs i) ^ (k : ℕ) * (αs i) ^ (l : ℕ) * (αs i) ^ (j : ℕ)) := by
  have key2 : yvec αs A i * yvec αs B i
      = ∑ k : Fin n, ∑ l : Fin n, (A k * B l) * ((αs i) ^ (k : ℕ) * (αs i) ^ (l : ℕ)) := by
    simp only [yvec]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [key2]
  simp only [yvec]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem yBdot_eq_sum {n : ℕ} (αs : Fin n → ℝ) (P u v : Fin n → ℝ) :
    yBdot αs P u v
      = ∑ k : Fin n, ∑ l : Fin n, ∑ j : Fin n,
          (P k * u l * v j) * psumRoots αs ((k : ℕ) + (l : ℕ) + (j : ℕ)) := by
  have hpow : ∀ (x : ℝ) (a b c : ℕ), x ^ a * x ^ b * x ^ c = x ^ (a + b + c) := by
    intro x a b c
    rw [pow_add, pow_add]
  simp only [yBdot, ymoment3Y, pow_one]
  refine (Finset.sum_congr rfl (fun i _ => yvec_mul3_eq_sum αs P u v i)).trans ?_
  calc (∑ i, ∑ k, ∑ l, ∑ j, (P k * u l * v j) * ((αs i) ^ (k : ℕ) * (αs i) ^ (l : ℕ)
      * (αs i) ^ (j : ℕ)))
      = ∑ k, ∑ l, ∑ j, ∑ i, (P k * u l * v j) * ((αs i) ^ (k : ℕ) * (αs i) ^ (l : ℕ)
        * (αs i) ^ (j : ℕ)) :=
          sum_comm4 (g := fun (i k l j : Fin n) =>
            (P k * u l * v j) * ((αs i) ^ (k : ℕ) * (αs i) ^ (l : ℕ) * (αs i) ^ (j : ℕ)))
    _ = ∑ k, ∑ l, ∑ j, (P k * u l * v j)
          * ∑ i, (αs i) ^ ((k : ℕ) + (l : ℕ) + (j : ℕ)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun l _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact congrArg (fun z : ℝ => (P k * u l * v j) * z) (hpow _ _ _ _)
    _ = _ := rfl

theorem yConicB_eq_sum {n : ℕ} (αs : Fin n → ℝ) (P u : Fin n → ℝ) :
    yConicB αs P u
      = ∑ k : Fin n, ∑ l : Fin n, ∑ j : Fin n,
          (P k * u l * u j) * psumRoots αs ((k : ℕ) + (l : ℕ) + (j : ℕ)) := by
  have key : yConicB αs P u = yBdot αs P u u := by
    simp only [yConicB, ymoment2Y, yBdot, ymoment3Y]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [pow_one, pow_two]
    ring
  exact key.trans (yBdot_eq_sum αs P u u)

theorem yNB_eq_sum {n : ℕ} (αs : Fin n → ℝ) (P v : Fin n → ℝ) :
    yNB αs P v
      = ∑ k : Fin n, ∑ l : Fin n, ∑ j : Fin n,
          (P k * P l * v j) * psumRoots αs ((k : ℕ) + (l : ℕ) + (j : ℕ)) := by
  have key : yNB αs P v = yBdot αs P P v := by
    simp only [yNB, ymoment2Y, yBdot, ymoment3Y]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [pow_one, pow_two]
  exact key.trans (yBdot_eq_sum αs P P v)

/-- **PLAN §2.1, the working form.** The three y-space pairings of P-constructible
`b`-vectors are P-constructible: `rw [yBdot_eq_sum]` (resp. `yConicB_eq_sum`,
`yNB_eq_sum`), then `Finset.sum_induction`; each summand is `pconstructible` from the
entry hypotheses and `psumRoots_Pconstructible_of_roots`. -/
theorem yBdot_Pconstructible {q : ℝ[X]} {αs : Fin n → ℝ} {P u v : Fin n → ℝ}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs) (hP : ∀ k, PConstructible (P k))
    (hu : ∀ k, PConstructible (u k)) (hv : ∀ k, PConstructible (v k)) :
    PConstructible (yBdot αs P u v) := by
  rw [yBdot_eq_sum]
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun _ _ => ?_)
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun _ _ => ?_)
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun j _ => ?_)
  exact PConstructible.mul
    (PConstructible.mul (PConstructible.mul (hP _) (hu _)) (hv j))
    (psumRoots_Pconstructible_of_roots hmon hn hnat hsep hcoef hαs hnd _)

theorem yConicB_Pconstructible {q : ℝ[X]} {αs : Fin n → ℝ} {P u : Fin n → ℝ}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs) (hP : ∀ k, PConstructible (P k))
    (hu : ∀ k, PConstructible (u k)) : PConstructible (yConicB αs P u) := by
  rw [yConicB_eq_sum]
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun _ _ => ?_)
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun _ _ => ?_)
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun j _ => ?_)
  exact PConstructible.mul
    (PConstructible.mul (PConstructible.mul (hP _) (hu _)) (hu j))
    (psumRoots_Pconstructible_of_roots hmon hn hnat hsep hcoef hαs hnd _)

theorem yNB_Pconstructible {q : ℝ[X]} {αs : Fin n → ℝ} {P v : Fin n → ℝ}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs) (hP : ∀ k, PConstructible (P k))
    (hv : ∀ k, PConstructible (v k)) : PConstructible (yNB αs P v) := by
  rw [yNB_eq_sum]
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun _ _ => ?_)
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun _ _ => ?_)
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun j _ => ?_)
  exact PConstructible.mul
    (PConstructible.mul (PConstructible.mul (hP _) (hP _)) (hv j))
    (psumRoots_Pconstructible_of_roots hmon hn hnat hsep hcoef hαs hnd _)

/-- The quadratic form is the pairing squared. -/
theorem yConicB_eq_yBdot {n : ℕ} (αs : Fin n → ℝ) (P u : Fin n → ℝ) :
    yConicB αs P u = yBdot αs P u u := by
  simp only [yConicB, ymoment2Y, yBdot, ymoment3Y]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [pow_one, pow_two]
  ring

/-! ### Interpolation at rational nodes

Small coefficient facts used by `psumY_line_poly` below: the coefficients of `X - C y`, and
hence of `Lagrange.basisDivisor x y` and of the `Lagrange.basis` polynomials, are
P-constructible whenever the nodes `x`, `y` are, and a finset-product of polynomials with
P-constructible coefficients again has P-constructible coefficients. (The `C ·`-multiple
and binary-product steps are `C_mul_coeff_Pconstructible` and `coeff_mul_Pconstructible`,
already public in `Pptc.DegreeSeven`.) -/

private theorem prod_coeff_Pconstructible {ι : Type*} {s : Finset ι} {f : ι → ℝ[X]}
    (hf : ∀ i ∈ s, ∀ k, PConstructible ((f i).coeff k)) (j : ℕ) :
    PConstructible ((∏ i ∈ s, f i).coeff j) :=
  (Finset.prod_induction f (fun q => ∀ k, PConstructible (q.coeff k))
    (fun a b ha hb k => coeff_mul_Pconstructible ha hb k)
    (fun k => by
      rw [Polynomial.coeff_one]
      split_ifs
      · exact PConstructible.base_one
      · exact zero_Pconstructible)
    (fun i hi => hf i hi)) j

private theorem X_sub_C_coeff_Pconstructible {y : ℝ} (hy : PConstructible y) (k : ℕ) :
    PConstructible ((Polynomial.X - Polynomial.C y).coeff k) := by
  rw [Polynomial.coeff_sub]
  refine PConstructible.sub ?_ (coeff_C_Pconstructible hy k)
  rw [Polynomial.coeff_X]
  split_ifs with h
  · exact PConstructible.base_one
  · exact zero_Pconstructible

private theorem basisDivisor_coeff_Pconstructible {x y : ℝ} (hx : PConstructible x)
    (hy : PConstructible y) (k : ℕ) :
    PConstructible ((Lagrange.basisDivisor x y).coeff k) := by
  unfold Lagrange.basisDivisor
  exact C_mul_coeff_Pconstructible
    (inv_Pconstructible (PConstructible.sub hx hy))
    (fun j => X_sub_C_coeff_Pconstructible hy j) k

private theorem basis_coeff_Pconstructible {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → ℝ}
    (hv : ∀ i, PConstructible (v i)) (i : ι) (k : ℕ) :
    PConstructible ((Lagrange.basis (Finset.univ : Finset ι) v i).coeff k) :=
  prod_coeff_Pconstructible (fun j _ => basisDivisor_coeff_Pconstructible (hv i) (hv j)) k

/-- **PLAN §2.6, the general step-polynomial lemma.** The univariate polynomial
`s ↦ pₘ(Y(u + s • v))` has degree `≤ m` and P-constructible coefficients.

The route is interpolation. `F(s) = pₘ(Y(u + s • v))` is a polynomial in `s` of degree
`≤ m` because `Y(u + s • v) = Yu + s • Yv` is affine in `s` and `pₘ` is a fixed symmetric
form. For each *rational* `r`, `u + r • v` is a P-constructible `b`-vector, so
`F(r) = psum_yvec_Pconstructible … m` is P-constructible. A degree-`≤ m` polynomial is
determined by its values at `m + 1` distinct points, and the interpolation formula has
rational (hence P-constructible) coefficients, so every coefficient of `F` is
P-constructible.

This one lemma is what the four step polynomials of `Pptc/TotallyReal/Certificate.lean`
need; it is the reason that file never has to expand a coupled moment by hand. -/
theorem psumY_line_poly {q : ℝ[X]} {αs : Fin n → ℝ} {u v : Fin n → ℝ}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs) (hu : ∀ k, PConstructible (u k))
    (hv : ∀ k, PConstructible (v k)) (m : ℕ) :
    ∃ g : ℝ[X], g.natDegree ≤ m ∧ (∀ j, PConstructible (g.coeff j)) ∧
      ∀ s : ℝ, g.eval s = psumY (yvec αs (u + s • v)) m := by
  classical
  -- HALF (a). The step polynomial, written as a sum of `m`-th powers of linear
  -- polynomials: `p s = Σᵢ (Y(u)_ᵢ + s · Y(v)_ᵢ)^m = pₘ(Y(u + s • v))`.
  have hlin (a b : ℝ) :
      (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 :=
    Polynomial.natDegree_add_le_of_degree_le (by simp) (by
      simpa using Polynomial.natDegree_C_mul_X_pow_le b 1)
  set p : ℝ[X] :=
    ∑ i : Fin n, (Polynomial.C (yvec αs u i) + Polynomial.C (yvec αs v i) * Polynomial.X) ^ m
    with hp
  have hpdeg : p.natDegree ≤ m := by
    rw [hp]
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin n)) _ fun i _ => ?_
    simpa using
      (Polynomial.natDegree_pow_le_of_le m (hlin (yvec αs u i) (yvec αs v i)))
  have hpeval (s : ℝ) : p.eval s = psumY (yvec αs (u + s • v)) m := by
    rw [hp, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, psumY, psumFinY]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [yvec_add, yvec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  -- HALF (b). Interpolate `p` at the `m + 1` rational nodes `0, 1, …, m`; the resulting
  -- polynomial is `p` again, and its coefficients are P-constructible because it is a
  -- rational linear combination of the `Lagrange.basis` polynomials.
  set vv : Fin (m + 1) → ℝ := fun r => (r : ℕ) with hvv
  have hinj : Set.InjOn vv ((Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))) := by
    rintro i _ j _ hij
    apply Fin.ext
    exact Nat.cast_injective hij
  have hcard : m < (Finset.univ : Finset (Fin (m + 1))).card := by simp
  have hpdeg' : p.degree ≤ m :=
    (Polynomial.natDegree_le_iff_degree_le (p := p) (n := m)).mp hpdeg
  have hdeglt : p.degree < (Finset.univ : Finset (Fin (m + 1))).card :=
    lt_of_le_of_lt hpdeg' (Nat.cast_lt.mpr hcard)
  have hgp : p = Lagrange.interpolate (Finset.univ : Finset (Fin (m + 1))) vv
      fun r => p.eval (vv r) :=
    Lagrange.eq_interpolate_of_eval_eq (fun r => p.eval (vv r)) hinj hdeglt fun _ _ => rfl
  set g : ℝ[X] := Lagrange.interpolate (Finset.univ : Finset (Fin (m + 1))) vv
    fun r => p.eval (vv r) with hg
  have hg' : g = p := hg.trans hgp.symm
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [hg']
    exact hpdeg
  · intro j
    have hvi : ∀ i : Fin (m + 1), PConstructible (vv i) := fun i => nat_Pconstructible i
    have hw : ∀ i : Fin (m + 1), PConstructible (p.eval (vv i)) := by
      intro i
      rw [hpeval (vv i)]
      refine psum_yvec_Pconstructible (αs := αs) (b := u + vv i • v) hmon hn hnat hsep hcoef
        hαs hnd ?_ m
      intro k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact PConstructible.add (hu k) (PConstructible.mul (hvi i) (hv k))
    rw [hg, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
    refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
      zero_Pconstructible fun i _ => ?_
    exact C_mul_coeff_Pconstructible (hw i) (basis_coeff_Pconstructible hvi i) j
  · intro s
    rw [hg']
    exact hpeval s

/-! ### Density (PLAN §2.6) -/

/-- `b ↦ yvec αs b` is injective when the roots are distinct (Vandermonde).


The proof is the Vandermonde determinant argument: `bPoly b − bPoly c` vanishes at the `n`
distinct points `αs i`, and has degree `≤ n − 1` by `bPoly_natDegree_le`, so it must be
the zero polynomial; its coefficients then give `b = c`. -/
theorem yvec_injective {αs : Fin n → ℝ} (hnd : Function.Injective αs) :
    Function.Injective (yvec αs) := by
  intro b c hbc
  by_cases hn0 : n = 0
  · funext k
    exact Fin.elim0 (hn0 ▸ k)
  · have hsub : bPoly b - bPoly c = 0 := by
      by_contra hne
      have hval : ∀ i : Fin n, (bPoly b).eval (αs i) = (bPoly c).eval (αs i) := by
        intro i
        rw [yvec_eq_bPoly_eval, yvec_eq_bPoly_eval, ← hbc]
      have hroot : ∀ i : Fin n, αs i ∈ (bPoly b - bPoly c).roots := by
        intro i
        rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_sub]
        exact sub_eq_zero.mpr (hval i)
      have hle := Polynomial.card_le_degree_of_subset_roots
        (p := bPoly b - bPoly c) (Z := (Finset.univ : Finset (Fin n)).image αs) (by
          intro x hx
          obtain ⟨i, _, hix⟩ := Finset.mem_image.mp (Finset.mem_def.mpr hx)
          rw [← hix]
          exact hroot i)
      have hdeg : (bPoly b - bPoly c).natDegree ≤ n - 1 :=
        le_trans (Polynomial.natDegree_sub_le ..)
          (Nat.max_le.mpr ⟨bPoly_natDegree_le b, bPoly_natDegree_le c⟩)
      rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hnd,
        Finset.card_univ, Fintype.card_fin] at hle
      omega
    have hk : ∀ k : Fin n, b k = c k := fun k => by
      have hc := congrArg (fun p : ℝ[X] => p.coeff k.val) hsub
      rw [Polynomial.coeff_sub, Polynomial.coeff_zero, bPoly_coeff' b k.val k.isLt,
        bPoly_coeff' c k.val k.isLt] at hc
      exact sub_eq_zero.mp hc
    exact funext hk

/-- `b ↦ yvec αs b` is a linear map (Vandermonde), by `yvec_add` / `yvec_smul`. -/
def yvecL (αs : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := yvec αs
  map_add' := yvec_add αs
  map_smul' := yvec_smul αs

/-- Being injective on a finite-dimensional space, `yvec αs` is onto, so every y-vector is
`yvec αs b` for a unique `b`. -/
lemma yvecL_surjective {αs : Fin n → ℝ} (hnd : Function.Injective αs) :
    Function.Surjective (yvecL αs) := by
  haveI : FiniteDimensional ℝ (Fin n → ℝ) := by infer_instance
  exact LinearMap.injective_iff_surjective.1 (yvec_injective hnd)

/-- Rational vectors are dense in `b`-space. This is the only place density is used: it is
what puts a P-constructible `b` into an open set of `b`-space. -/
lemma denseRange_piRatCast (n : ℕ) :
    DenseRange (fun f : Fin n → ℚ => fun i => (f i : ℝ)) := by
  exact DenseRange.piMap fun _ => Rat.denseRange_cast

/-- Every nonempty open set of `b`-space contains a P-constructible `b` (take it rational). -/
lemma exists_Pconstructible_mem_isOpen {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ b : Fin n → ℝ, (∀ k, PConstructible (b k)) ∧ b ∈ U := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hy
  obtain ⟨f, hf⟩ := (Metric.denseRange_iff.mp (denseRange_piRatCast n)) y ε hε
  exact ⟨fun i => (f i : ℝ), fun k => rat_Pconstructible (f k),
    hball (Metric.mem_ball'.mpr hf)⟩

/-- Subtract `c` from the `e`-th coordinate of `b`. For `e = 0` this is the trace correction
of PLAN §2.6; the `e`-th column of the Vandermonde map is `(αs 0^e, …, αs (n-1)^e)`. -/
def bcorrect (b : Fin n → ℝ) (e : Fin n) (c : ℝ) : Fin n → ℝ :=
  fun k => b k - (if k = e then c else 0)

/-- The key geometric fact behind the correction: because the `e`-th column of the
Vandermonde map is `(αs 0 ^ e, …)`, subtracting `c` from the `e`-th coordinate of `b` moves
the y-vector by `-c · αs ^ e`; for `e = 0` that is the constant vector `-c`. -/
lemma yvec_correct (αs : Fin n → ℝ) (b : Fin n → ℝ) (e : Fin n) (c : ℝ) (i : Fin n) :
    yvec αs (bcorrect b e c) i = yvec αs b i - c * (αs i) ^ (e : ℕ) := by
  have hone : ∑ k : Fin n, (if k = e then c else 0) * (αs i) ^ (k : ℕ)
      = c * (αs i) ^ (e : ℕ) := by
    have hne' : ∀ k : Fin n, k ≠ e → (if k = e then c else 0) * (αs i) ^ (k : ℕ) = 0 := by
      intro k hk
      simp [hk]
    refine (Fintype.sum_eq_single
      (f := fun k : Fin n => (if k = e then c else 0) * (αs i) ^ (k : ℕ))
      (a := e) hne').trans ?_
    simp
  simp only [yvec, bcorrect, sub_mul]
  rw [Finset.sum_sub_distrib, hone]

/-- The image of `ℚ` vectors under `yvec` is dense, so every nonempty open set of y-space
is met by a P-constructible `b`. The trace correction `b ↦ b − (p₁(y(b))/n)·(1,…,1)` then
puts the y-vector in `V = {y | p₁(y) = 0}` without leaving the open set. -/
theorem exists_b_Pconstructible_near {q : ℝ[X]} {αs : Fin n → ℝ}
    {U : Set (Fin n → ℝ)} (hn : 0 < n) (hnd : Function.Injective αs) (hU : IsOpen U)
    (hne : (U ∩ {y : Fin n → ℝ | psumY y 1 = 0}).Nonempty)
    (hpsum : ∀ b : Fin n → ℝ, (∀ k, PConstructible (b k)) →
      PConstructible (psumY (yvec αs b) 1)) :
    ∃ b : Fin n → ℝ, (∀ k, PConstructible (b k)) ∧ yvec αs b ∈ U ∧ psumY (yvec αs b) 1 = 0 := by
  obtain ⟨e, he⟩ : ∃ e : Fin n, e = ⟨0, hn⟩ := ⟨⟨0, hn⟩, rfl⟩
  -- the correction, and the fact that it lands in `V`
  have hcorr : ∀ b : Fin n → ℝ,
      psumY (yvec αs (bcorrect b e (psumY (yvec αs b) 1 / n))) 1 = 0 := by
    intro b
    have h1 : yvec αs (bcorrect b e (psumY (yvec αs b) 1 / n))
        = fun i => yvec αs b i - psumY (yvec αs b) 1 / n := by
      funext i
      rw [yvec_correct, he]
      simp
    rw [h1]
    simp only [psumY, psumFinY, pow_one, Finset.sum_sub_distrib]
    have h2 : (∑ i : Fin n, (∑ x, yvec αs b x) / ↑n) = ∑ x, yvec αs b x := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      field_simp
    rw [h2]
    ring
  -- the corrected y-vector moves continuously, so its inverse image of `U` is open …
  have hfc : Continuous (fun b : Fin n → ℝ =>
      yvec αs (bcorrect b e (psumY (yvec αs b) 1 / n))) := by
    have hyv : ∀ i : Fin n, Continuous fun b : Fin n → ℝ => yvec αs b i := by
      intro i
      have h2 : Continuous fun b : Fin n → ℝ => yvec αs b i := by
        simp only [yvec]
        refine continuous_finsetSum _ fun k _ => (continuous_apply k).mul continuous_const
      exact h2
    have hpc : Continuous fun b : Fin n → ℝ => psumY (yvec αs b) 1 := by
      have h2 : Continuous fun b : Fin n → ℝ => psumY (yvec αs b) 1 := by
        simp only [psumY, psumFinY]
        refine continuous_finsetSum _ fun i _ => ?_
        simpa using (hyv i).pow 1
      exact h2
    have h3 : Continuous (fun b : Fin n → ℝ => (fun i => yvec αs b i - psumY (yvec αs b) 1 / n)) := by
      refine continuous_pi fun i => ?_
      have hnum : Continuous (fun b : Fin n → ℝ => yvec αs b i - psumY (yvec αs b) 1) :=
        (hyv i).sub hpc
      exact (hyv i).sub (hpc.div_const (n : ℝ))
    have heq : (fun b : Fin n → ℝ => yvec αs (bcorrect b e (psumY (yvec αs b) 1 / n)))
        = (fun b : Fin n → ℝ => (fun i => yvec αs b i - psumY (yvec αs b) 1 / n)) := by
      funext b i
      rw [yvec_correct, he]
      simp
    rw [heq]
    exact h3
  -- … and is nonempty, because `yvec αs` is onto and `U ∩ V` is nonempty
  have hne' : {b : Fin n → ℝ | yvec αs (bcorrect b e (psumY (yvec αs b) 1 / n)) ∈ U}.Nonempty := by
    obtain ⟨y, hyU, hyH⟩ := hne
    obtain ⟨b, hb⟩ := yvecL_surjective hnd y
    refine ⟨b, ?_⟩
    have hb' : yvec αs b = y := hb
    have hL : psumY (yvec αs b) 1 = 0 := by
      rw [hb']
      exact hyH
    have hbc : bcorrect b e (psumY (yvec αs b) 1 / n) = b := by
      funext k
      simp [bcorrect, hL]
    show yvec αs (bcorrect b e (psumY (yvec αs b) 1 / n)) ∈ U
    rw [hbc, hb']
    exact hyU
  -- density now supplies a P-constructible `b` whose *corrected* y-vector is in `U`
  obtain ⟨b, hb, hbmem⟩ :=
    exists_Pconstructible_mem_isOpen (hU.preimage hfc) hne'
  refine ⟨bcorrect b e (psumY (yvec αs b) 1 / n), ?_, hbmem, hcorr b⟩
  intro k
  by_cases hk : k = e
  · rw [bcorrect, if_pos hk]
    exact PConstructible.sub (hb k)
      (PConstructible.div (hpsum b hb) (nat_Pconstructible n))
  · rw [bcorrect, if_neg hk, sub_zero]
    exact hb k

end Pconstructible
