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

import Pptc.TotallyReal.Main
import Pptc.Octic.Engine

/-! # Pptc.Octic.Resolvent

The resolvent (Newton) step and the Tschirnhaus tail for octics: Part B of
`Pptc/Octic/PLAN.md` §2.3, the degree-8 analogue of the septic block of `Pptc.DegreeSeven`.

For a monic separable octic `q` and a Tschirnhaus map `φ`, the resolvent is the
characteristic polynomial `R = χ(aeval (companionN q) φ)` of `φ(C_q)`.  Its eigenvalues are
`φ(z)` over the complex roots `z` of `q`, and the top three elementary symmetric functions
of those values are the trace power sums `p₁, p₂, p₃` of `φ(C_q)`.  Hence all three vanish,
kills the `X⁷, X⁶, X⁵` coefficients of `R`, and since `R` is monic of degree `8` with
`X⁸`-coefficient `1`, a root `y = φ(β)` satisfies the quartic power law

    y⁸ = c₄ y⁴ + c₃ y³ + c₂ y² + c₁ y + c₀,     cᵢ = −R.coeff i.

The shape `χ(t) = Q(t²) − e₈·t` with `Q` a monic quartic is exactly this: the `y⁸` term and
the even terms combine into `Q(y²)`, and the odd terms are absorbed into `e₈ · y`.

The tail recovers `β` from `y = φ β`: `y` is P-constructible by the octic engine
(`powerLaw_quartic_root_PConstructible`), and `β` is a root of `φ − C y`, a nonzero
polynomial of degree `≤ 7` with P-constructible coefficients, so the degree-7 theorem
`root_Pconstructible_deg7_coeffs` finishes.
-/

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### The spectral identities for `Fin 8` -/

-- Theorem: the trace of the `k`-th power of `aeval (companionN q) φ`, mapped to `ℂ`, is the
-- sum of the `k`-th powers of `φ` evaluated at the complex roots of `q`.
theorem companionN_trace_pow_aeval_eight (q φ : ℝ[X]) (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (k : ℕ) :
    algebraMap ℝ ℂ (Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ k))
      = ((q.map (algebraMap ℝ ℂ)).roots.map
          (fun z => ((φ.map (algebraMap ℝ ℂ)).eval z) ^ k)).sum := by
  have hmon' : (q.map (algebraMap ℝ ℂ)).Monic := hmon.map (algebraMap ℝ ℂ)
  have hnat' : (q.map (algebraMap ℝ ℂ)).natDegree = 8 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    exact hnat
  have hsep' : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  have hmap : ((aeval (companionN (n := 8) q) φ) ^ k).map (algebraMap ℝ ℂ)
      = (aeval (companionN' (n := 8) (q.map (algebraMap ℝ ℂ)))
          (φ.map (algebraMap ℝ ℂ))) ^ k := by
    rw [← RingHom.mapMatrix_apply (algebraMap ℝ ℂ) ((aeval (companionN (n := 8) q) φ) ^ k),
      map_pow, RingHom.mapMatrix_apply, companionN_aeval_map_eq]
  rw [AddMonoidHom.map_trace (algebraMap ℝ ℂ), hmap,
    companionN'_trace_pow 8 (q.map (algebraMap ℝ ℂ)) (φ.map (algebraMap ℝ ℂ))
      hmon' (by norm_num) hnat' hsep' k]

-- Theorem: the characteristic polynomial of `φ` evaluated at the degree-8 companion matrix
-- is the product of `X - C (φ.eval z)` over the roots `z` of `q`.
theorem companionN'_charpoly_aeval_eq_prod8 {K : Type*} [Field K] [IsAlgClosed K]
    (q φ : K[X]) (hmon : q.Monic) (hnat : q.natDegree = 8) (hsep : q.Separable) :
    (aeval (companionN' (n := 8) q) φ).charpoly
      = (q.roots.map (fun z => Polynomial.X - Polynomial.C (φ.eval z))).prod := by
  classical
  set M : Matrix (Fin 8) (Fin 8) K := companionN' (n := 8) q with hM
  have h8 : q.coeff 8 = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ 8 := le_of_eq hnat
  have hnodup : q.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard : q.roots.card = 8 := by
    rw [← hnat]; exact (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  let idx := q.roots.toFinset
  have : Nonempty idx := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
      rw [Multiset.toFinset_card_of_nodup hnodup, hcard]; norm_num)
    exact ⟨⟨x, hx⟩⟩
  let v : idx → (Fin 8 → K) := fun z => companionVecN (n := 8) (z : K)
  have hv : ∀ z : idx, M *ᵥ v z = (z : K) • v z := by
    intro z
    have hz : q.eval (z : K) = 0 :=
      (Polynomial.mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp z.2)
    exact companionN'_mulVec_companionVecN (by norm_num) h8 hdeg hz
  have hvne : ∀ z : idx, v z ≠ 0 := by
    intro z h0
    have h1 := congrFun h0 0
    simp [v, companionVecN] at h1
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' M.toLin' (fun z : idx => (z : K))
      Subtype.coe_injective v (fun z =>
        ⟨(Module.End.mem_eigenspace_iff).mpr (by rw [Matrix.toLin'_apply]; exact hv z), hvne z⟩)
  have hcardfin : Fintype.card idx = Module.finrank K (Fin 8 → K) := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcard]
    norm_num
  let b : Module.Basis idx K (Fin 8 → K) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcardfin
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

/-! ### The top three coefficients of the octic resolvent vanish -/

-- Theorem: if `q` is a monic separable octic over `ℝ` and `φ` has vanishing first three
-- trace power sums at `companionN q`, then `charpoly (aeval (companionN q) φ)` has zero
-- `X⁷`, `X⁶`, `X⁵` coefficients.  The eigenvalues of `aeval (companionN q) φ` are the
-- values `φ z` at the roots `z` of `q`, so the coefficients are elementary symmetric
-- functions of those values; the trace hypotheses are the vanishing power sums.
theorem charpoly_aeval_coeff_7_6_5_eq_zero {q φ : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable)
    (hp1 : Matrix.trace (aeval (companionN (n := 8) q) φ) = 0)
    (hp2 : Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 2) = 0)
    (hp3 : Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 3) = 0) :
    (aeval (companionN (n := 8) q) φ).charpoly.coeff 7 = 0 ∧
    (aeval (companionN (n := 8) q) φ).charpoly.coeff 6 = 0 ∧
    (aeval (companionN (n := 8) q) φ).charpoly.coeff 5 = 0 := by
  classical
  set qC : ℂ[X] := q.map (algebraMap ℝ ℂ) with hqC
  set φC : ℂ[X] := φ.map (algebraMap ℝ ℂ) with hφC
  set y : Multiset ℂ := qC.roots.map (fun z => φC.eval z) with hy
  set N : Matrix (Fin 8) (Fin 8) ℝ := aeval (companionN (n := 8) q) φ with hN
  set R : ℝ[X] := N.charpoly with hR
  have hmon' : qC.Monic := by rw [hqC]; exact hmon.map _
  have hnat' : qC.natDegree = 8 := by
    rw [hqC, Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]; exact hnat
  have hsep' : qC.Separable := by rw [hqC]; exact hsep.map
  have hchar : R.map (algebraMap ℝ ℂ)
      = (y.map (fun w => Polynomial.X - Polynomial.C w)).prod := by
    have h1 : R.map (algebraMap ℝ ℂ) = (N.map (algebraMap ℝ ℂ)).charpoly := by
      rw [hR]
      exact (Matrix.charpoly_map N (algebraMap ℝ ℂ)).symm
    have h2 : N.map (algebraMap ℝ ℂ) = aeval (companionN' (n := 8) qC) φC := by
      rw [hN, hqC, hφC]
      exact companionN_aeval_map_eq 8 q φ
    rw [h1, h2]
    simpa only [hy, Multiset.map_map, Function.comp_apply] using
      companionN'_charpoly_aeval_eq_prod8 qC φC hmon' hnat' hsep'
  have hycard : y.card = 8 := by
    rw [hy, Multiset.card_map]
    rw [show qC.roots.card = qC.natDegree from
      (IsAlgClosed.splits qC).natDegree_eq_card_roots.symm, hnat']
  have hsum_pow (k : ℕ) (hk : Matrix.trace (N ^ k) = 0) :
      (y.map (fun w => w ^ k)).sum = 0 := by
    have h := companionN_trace_pow_aeval_eight q φ hmon hnat hsep k
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

/-! ### The quartic power law of the resolvent -/

-- Theorem: if `q` is monic of degree `8` with P-constructible coefficients, `φ` has
-- P-constructible coefficients, and the resolvent `charpoly (φ (companionN q))` has its
-- `X ^ 7`, `X ^ 6`, `X ^ 5` coefficients zero, then `y = φ β` satisfies a power-law
-- equation `y ^ 8 = quarticVal c₀ c₁ c₂ c₃ c₄ y` with P-constructible `cᵢ`.
theorem resolvent_quarticPowerLaw {q φ : ℝ[X]} {β : ℝ}
    (hq : ∀ k, PConstructible (q.coeff k)) (hβ : q.eval β = 0) (h8 : q.coeff 8 = 1)
    (hdeg : q.natDegree ≤ 8) (hφ : ∀ k, PConstructible (φ.coeff k))
    (hkill : (aeval (companionN (n := 8) q) φ).charpoly.coeff 7 = 0 ∧
             (aeval (companionN (n := 8) q) φ).charpoly.coeff 6 = 0 ∧
             (aeval (companionN (n := 8) q) φ).charpoly.coeff 5 = 0) :
    ∃ c₀ c₁ c₂ c₃ c₄ : ℝ, PConstructible c₀ ∧ PConstructible c₁ ∧
      PConstructible c₂ ∧ PConstructible c₃ ∧ PConstructible c₄ ∧
      (φ.eval β) ^ 8 = quarticVal c₀ c₁ c₂ c₃ c₄ (φ.eval β) := by
  set N : Matrix (Fin 8) (Fin 8) ℝ := aeval (companionN (n := 8) q) φ with hN
  set R : ℝ[X] := N.charpoly with hR
  have hNc : ∀ i j, PConstructible (N i j) := fun i j =>
    aeval_entries_Pconstructible _ (companionN_entries_Pconstructible 8 q hq) φ hφ i j
  have hRc : ∀ k, PConstructible (R.coeff k) := fun k =>
    charpoly_aeval_companionN_coeff_Pconstructible 8 q φ hq hφ k
  have hk7 : R.coeff 7 = 0 := by rw [hR, hN]; exact hkill.1
  have hk6 : R.coeff 6 = 0 := by rw [hR, hN]; exact hkill.2.1
  have hk5 : R.coeff 5 = 0 := by rw [hR, hN]; exact hkill.2.2
  have hnat : R.natDegree = 8 := by rw [hR]; exact Matrix.charpoly_natDegree_eq_dim N
  have hmonic : R.Monic := by rw [hR]; exact Matrix.charpoly_monic N
  have hc8 : R.coeff 8 = 1 := by rw [← hnat]; exact hmonic.coeff_natDegree
  have hroot : R.eval (φ.eval β) = 0 := by
    rw [hR, hN]
    exact companionN_charpoly_aeval_isRoot 8 hβ (by norm_num) h8 hdeg
  have heval : R.eval (φ.eval β) =
      (φ.eval β) ^ 8 + R.coeff 4 * (φ.eval β) ^ 4 + R.coeff 3 * (φ.eval β) ^ 3
        + R.coeff 2 * (φ.eval β) ^ 2 + R.coeff 1 * (φ.eval β) + R.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range' (p := R) (n := 9) (by rw [hnat]; norm_num)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    rw [hk7, hk6, hk5, hc8]
    ring
  have h0 : (φ.eval β) ^ 8 + R.coeff 4 * (φ.eval β) ^ 4 + R.coeff 3 * (φ.eval β) ^ 3
      + R.coeff 2 * (φ.eval β) ^ 2 + R.coeff 1 * (φ.eval β) + R.coeff 0 = 0 := by
    rw [← heval]; exact hroot
  refine ⟨-R.coeff 0, -R.coeff 1, -R.coeff 2, -R.coeff 3, -R.coeff 4,
    neg_Pconstructible (hRc 0), neg_Pconstructible (hRc 1), neg_Pconstructible (hRc 2),
    neg_Pconstructible (hRc 3), neg_Pconstructible (hRc 4), ?_⟩
  rw [quarticVal]
  linarith [h0]

/-! ### Nonconstant from vanishing trace -/

-- Theorem: if a nonzero polynomial `φ` has `trace (aeval (companionN q) φ) = 0`, then `φ` is
-- nonconstant. If `φ` were the nonzero constant `C c`, the trace would be `8 c ≠ 0`.
theorem natDegree_ne_zero_of_trace_zero8 {q φ : ℝ[X]}
    (hp1 : Matrix.trace (aeval (companionN (n := 8) q) φ) = 0) (hφne : φ ≠ 0) :
    φ.natDegree ≠ 0 := by
  intro hdeg0
  obtain ⟨c, hc⟩ := (Polynomial.natDegree_eq_zero).mp hdeg0
  have htrace : Matrix.trace (aeval (companionN (n := 8) q) φ) = 8 * c := by
    rw [← hc, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul,
      Matrix.trace_one, smul_eq_mul]
    norm_num
    ring
  rw [htrace] at hp1
  have hc0 : c = 0 := by linarith
  rw [hc0, Polynomial.C_0] at hc
  exact hφne hc.symm

/-! ### The recovery step at degree `≤ 7` -/

-- Theorem: a nonconstant polynomial `φ` of degree at most 7 with P-constructible
-- coefficients has P-constructible roots over P-constructible values: if `φ β = y` and
-- `y` is P-constructible, then `β` is P-constructible.
theorem eval_root_Pconstructible8 {φ : Polynomial ℝ}
    (hcoeff : ∀ i, PConstructible (φ.coeff i)) (hdeg : φ.natDegree ≤ 7)
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
  have hψdeg : ψ.natDegree ≤ 7 := by
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
  exact root_Pconstructible_deg7_coeffs hψne hψdeg hψcoeff hψroot

/-! ### The Tschirnhaus tail -/

-- Theorem: a real root `β` of a monic separable octic `q` with P-constructible
-- coefficients is P-constructible, provided there is a nonzero degree-`≤ 7` polynomial `φ`
-- with P-constructible coefficients whose first three trace power sums at `companionN q`
-- vanish.
theorem root_Pconstructible_of_tschirnhaus8 {q φ : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    (hφc : ∀ k, PConstructible (φ.coeff k)) (hφdeg : φ.natDegree ≤ 7) (hφne : φ ≠ 0)
    (hp1 : Matrix.trace (aeval (companionN (n := 8) q) φ) = 0)
    (hp2 : Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 2) = 0)
    (hp3 : Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 3) = 0)
    {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β := by
  have hkill := charpoly_aeval_coeff_7_6_5_eq_zero hmon hnat hsep hp1 hp2 hp3
  have h8 : q.coeff 8 = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ 8 := le_of_eq hnat
  obtain ⟨c₀, c₁, c₂, c₃, c₄, hc₀, hc₁, hc₂, hc₃, hc₄, hpow⟩ :=
    resolvent_quarticPowerLaw hq hβ h8 hdeg hφc hkill
  exact eval_root_Pconstructible8 hφc hφdeg (natDegree_ne_zero_of_trace_zero8 hp1 hφne)
    (powerLaw_quartic_root_PConstructible hc₀ hc₁ hc₂ hc₃ hc₄ hpow) rfl

end

end Pconstructible
