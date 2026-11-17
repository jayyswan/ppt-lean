/-
Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Order.Preorder.Finite
import Pptc.Solvable.Roots
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # A cyclic-prime tower for solvable groups

This file contains the group-theoretic input for the converse Abel–Ruffini argument: a
finite nontrivial solvable group has a maximal proper normal subgroup whose quotient is
simple, and a simple solvable group is cyclic of prime order.
-/

namespace Pconstructible

/-- A finite nontrivial solvable group has a maximal proper normal subgroup with
cyclic quotient of prime order.

This is the local form of `Group.IsSolvable.exists_normal_index_prime` in TauCeti
(`TauCeti/GroupTheory/Solvable.lean`). That proof uses `Group.isSimpleGroup_of_isCoatom`, which
is not in the pinned Mathlib v4.33, so the quotient-simple step is proved directly here. -/
theorem exists_maximal_normal_prime_quotient {G : Type*} [Group G] [Finite G]
    (h : Group.IsSolvable G) [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N < ⊤ ∧ (Nat.card (G ⧸ N)).Prime := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G))
      (fun H K h => SetLike.coe_injective h)
  haveI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  let S : Finset (Subgroup G) := Finset.univ.filter fun K => K.Normal ∧ K < ⊤
  have hS : S.Nonempty := by
    refine ⟨⊥, ?_⟩
    have hbot : (⊥ : Subgroup G) < ⊤ := by
      haveI : Nontrivial (Subgroup G) := Subgroup.nontrivial_iff.mpr inferInstance
      exact bot_lt_top
    simp [S, hbot]
  obtain ⟨N, hNmax⟩ := S.exists_maximal hS
  have hNmem : N ∈ S := hNmax.1
  have hNmem' : N.Normal ∧ N < ⊤ := by
    simpa [S] using hNmem
  obtain ⟨hNnormal, hNlt⟩ := hNmem'
  haveI : N.Normal := hNnormal
  have hsimple : IsSimpleGroup (G ⧸ N) := by
    haveI : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNlt.ne
    refine { eq_bot_or_eq_top_of_normal := ?_ }
    intro H hH
    let M : Subgroup G := H.comap (QuotientGroup.mk' N)
    have hMnormal : M.Normal := hH.comap _
    have hNM : N ≤ M := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hxq : (QuotientGroup.mk' N x : G ⧸ N) = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      rw [hxq]
      exact H.one_mem
    have hmap : H = M.map (QuotientGroup.mk' N) :=
      (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) H).symm
    by_cases hMtop : M = ⊤
    · right
      rw [hmap, hMtop, Subgroup.map_top_of_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N)]
    · left
      have hMlt : M < ⊤ := lt_top_iff_ne_top.mpr hMtop
      have hMmem : M ∈ S := by
        simp [S, hMnormal, hMlt]
      have hMN : M ≤ N := hNmax.2 hMmem hNM
      have hMeq : M = N := le_antisymm hMN hNM
      rw [hmap, hMeq, QuotientGroup.map_mk'_self]
  have hsolv : Group.IsSolvable (G ⧸ N) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  have hcomm : ∀ a b : G ⧸ N, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
  letI : CommGroup (G ⧸ N) :=
    { __ := (inferInstance : Group (G ⧸ N))
      mul_comm := hcomm }
  exact ⟨N, hNnormal, hNlt, IsSimpleGroup.prime_card⟩

/-! ### Descending a solvable Galois tower into a root-closed subfield

The main result of this section: if `L/K` is a finite Galois extension with solvable Galois
group, `K` is (as a subfield of `ℂ`) contained in the radical closure of `ℚ`, and `K` contains
all the roots of unity that occur, then `L` is contained in that radical closure.

The proof is the classical one: descend the composition series of `Gal(L/K)`.  At each step
`N ◁ Gal(L/K)` is maximal normal with cyclic quotient of prime order `p`, the fixed field
`F = L^N` is cyclic of degree `p` over `K`, and Kummer theory writes `F = K(β)` with
`β ^ p ∈ K`; root closure then gives `F ⊆ S`.  Recurse on `Gal(L/F) ≅ N`. -/

open IntermediateField

/-- Strong-induction core of `le_solvableByRad_of_solvable_tower`. -/
private theorem solvable_tower_aux (n : ℕ) :
    ∀ (K : Type) [Field K] [Algebra K ℂ] (L : Type) [Field L] [Algebra K L] [Algebra L ℂ]
      [IsScalarTower K L ℂ] [FiniteDimensional K L] [IsGalois K L],
      Nat.card Gal(L/K) = n →
      Group.IsSolvable Gal(L/K) →
      (∀ x : K, algebraMap K ℂ x ∈ solvableByRad ℚ ℂ) →
      (∀ p, p.Prime → p ∣ n → (primitiveRoots p K).Nonempty) →
      ∀ x : L, algebraMap L ℂ x ∈ solvableByRad ℚ ℂ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ L _ _ _ _ _ _ hnc hsolv hK hmu x
    classical
    by_cases hnt : Nontrivial Gal(L/K)
    · -- `Gal(L/K)` is nontrivial: take a maximal normal subgroup with prime cyclic quotient.
      obtain ⟨N, hNnormal, hNlt, hNprime⟩ :=
        exists_maximal_normal_prime_quotient (G := Gal(L/K)) hsolv
      haveI hNn : N.Normal := hNnormal
      -- the fixed field of `N`
      let F : IntermediateField K L := IntermediateField.fixedField N
      -- `Gal(F/K) ≃ Gal(L/K) ⧸ N` is cyclic of prime order
      have hcard_iso : Nat.card Gal(↥F/K) = Nat.card (Gal(L/K) ⧸ N) :=
        Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv.symm
      have hcyclic : IsCyclic Gal(↥F/K) := by
        haveI : Fact (Nat.card (Gal(L/K) ⧸ N)).Prime := ⟨hNprime⟩
        exact isCyclic_of_prime_card hcard_iso
      -- Kummer: `F = K(β)` with `β ^ p ∈ K`
      have hfinrank_eq : Module.finrank K ↥F = Nat.card (Gal(L/K) ⧸ N) := by
        rw [← IsGalois.card_aut_eq_finrank K ↥F, hcard_iso]
      have hpm : Nat.card (Gal(L/K) ⧸ N) ∣ n := by
        rw [← hnc]; exact Subgroup.card_quotient_dvd_card N
      have hmuF : (primitiveRoots (Module.finrank K ↥F) K).Nonempty := by
        rw [hfinrank_eq]
        exact hmu _ hNprime hpm
      obtain ⟨β, hβpow, hβtop⟩ :=
        exists_root_adjoin_eq_top_of_isCyclic (K := K) (L := ↥F) (hK := hmuF)
      -- `algebraMap K ℂ = algebraMap ↥F ℂ ∘ algebraMap K ↥F`
      haveI hSTKF : IsScalarTower K ↥F ℂ :=
        IsScalarTower.of_algebraMap_eq fun a => by
          rw [IsScalarTower.algebraMap_apply K L ℂ]
          rfl
      -- `β` lies in the radical closure
      have hβS : algebraMap ↥F ℂ β ∈ solvableByRad ℚ ℂ := by
        obtain ⟨a, ha⟩ := hβpow
        have h1 : (algebraMap ↥F ℂ β) ^ Module.finrank K ↥F = algebraMap K ℂ a := by
          rw [← map_pow, ← ha]
          exact (IsScalarTower.algebraMap_apply K ↥F ℂ a).symm
        refine solvableByRad.rad_mem (x := algebraMap ↥F ℂ β) (n := Module.finrank K ↥F)
          Module.finrank_pos.ne' ?_
        rw [h1]
        exact hK a
      -- hence `F ⊆ S`, since `F = K(β)`
      have hFsub : ∀ y : ↥F, algebraMap ↥F ℂ y ∈ solvableByRad ℚ ℂ := by
        let T : IntermediateField K ↥F :=
          { carrier := {y : ↥F | algebraMap ↥F ℂ y ∈ solvableByRad ℚ ℂ}
            zero_mem' := by simp
            add_mem' := by intro a b ha hb; simpa using add_mem ha hb
            one_mem' := by simp
            mul_mem' := by intro a b ha hb; simpa using mul_mem ha hb
            inv_mem' := by intro a ha; simpa using (solvableByRad ℚ ℂ).inv_mem ha
            algebraMap_mem' := by
              intro a
              change algebraMap ↥F ℂ ((algebraMap K ↥F) a) ∈ solvableByRad ℚ ℂ
              rw [← IsScalarTower.algebraMap_apply K ↥F ℂ a]
              exact hK a }
        have hβT : β ∈ T := hβS
        have hle : K⟮β⟯ ≤ T := IntermediateField.adjoin_simple_le_iff.mpr hβT
        rw [hβtop] at hle
        intro y
        exact hle trivial
      -- recurse with the subgroup `N`
      haveI hSTFL : IsScalarTower ↥F L ℂ :=
        IsScalarTower.of_algebraMap_eq fun a => rfl
      have hN_dvd_n : Nat.card N ∣ n := by
        rw [← hnc]; exact Subgroup.card_subgroup_dvd_card N
      have hNlt_card : Nat.card N < n := by
        rw [← hnc]
        have h1 : 1 < N.index := Subgroup.one_lt_index_of_ne_top hNlt.ne
        calc Nat.card N < N.index * Nat.card N := lt_mul_of_one_lt_left Nat.card_pos h1
          _ = Nat.card Gal(L/K) := Subgroup.index_mul_card N
      have hmu'' : ∀ p, p.Prime → p ∣ Nat.card N → (primitiveRoots p ↥F).Nonempty := by
        intro p hp hpmN
        obtain ⟨ζ, hζ⟩ := hmu p hp (hpmN.trans hN_dvd_n)
        refine ⟨algebraMap K ↥F ζ, ?_⟩
        rw [mem_primitiveRoots hp.pos] at hζ ⊢
        exact hζ.map_of_injective (algebraMap K ↥F).injective
      have hiso2 : ↥N ≃* Gal(L/↥F) := IntermediateField.subgroupEquivAlgEquiv N
      have hcard' : Nat.card Gal(L/↥F) = Nat.card N := by
        rw [← Nat.card_congr hiso2.toEquiv]
      have hsolv' : Group.IsSolvable Gal(L/↥F) := by
        haveI : Group.IsSolvable ↥N := inferInstance
        exact Group.isSolvable_of_isSolvable_injective (G := Gal(L/↥F)) (G' := ↥N)
          (f := hiso2.symm.toMonoidHom) hiso2.symm.injective
      exact ih (Nat.card N) hNlt_card (K := ↥F) (L := L) hcard' hsolv' hFsub hmu'' x
    · -- `Gal(L/K)` is trivial, so `L = K`
      haveI : Subsingleton Gal(L/K) := not_nontrivial_iff_subsingleton.mp hnt
      have hbotop : (⊥ : Subgroup Gal(L/K)) = ⊤ := by
        refine Subgroup.ext fun g => ?_
        simp [Subsingleton.elim g 1]
      have htopbot : (⊤ : IntermediateField K L) = ⊥ := by
        calc (⊤ : IntermediateField K L)
            = IntermediateField.fixedField (⊥ : Subgroup Gal(L/K)) := by
              rw [IntermediateField.fixedField_bot]
          _ = IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) := by rw [hbotop]
          _ = ⊥ := IsGalois.fixedField_top
      have hx : x ∈ (⊥ : IntermediateField K L) := htopbot ▸ trivial
      rw [IntermediateField.mem_bot] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [← IsScalarTower.algebraMap_apply K L ℂ]
      exact hK a

/-- **Solvable Galois tower lemma.**  If `L/K` is a finite Galois extension whose Galois group
is solvable, if `K` (viewed in `ℂ`) is contained in the radical closure of `ℚ`, and if `K`
contains all roots of unity of prime order dividing `Nat.card Gal(L/K)`, then every element of
`L` lies in the radical closure of `ℚ`.

(`K` is a field in the lowest universe: the recursive step replaces `K` by a fixed field inside
the top field, which for an extension of `ℂ` always lives in the same universe as `ℂ`.) -/
theorem le_solvableByRad_of_solvable_tower
    {K : Type} [Field K] [Algebra ℚ K] [Algebra K ℂ] [IsScalarTower ℚ K ℂ]
    (hK : ∀ x : K, algebraMap K ℂ x ∈ solvableByRad ℚ ℂ)
    (L : IntermediateField K ℂ) [FiniteDimensional K L] [IsGalois K L]
    (hsolv : Group.IsSolvable Gal(L/K))
    (m : ℕ) (hprime : ∀ p, p.Prime → p ∣ Nat.card Gal(L/K) → p ∣ m)
    (hmu : ∀ p, p.Prime → p ∣ m → (primitiveRoots p K).Nonempty) :
    ∀ x : L, (x : ℂ) ∈ solvableByRad ℚ ℂ := by
  have hmu' : ∀ p, p.Prime → p ∣ Nat.card Gal(L/K) → (primitiveRoots p K).Nonempty :=
    fun p hp hpn => hmu p hp (hprime p hp hpn)
  have h := solvable_tower_aux (Nat.card Gal(L/K)) (K := K) (L := ↥L) rfl hsolv hK hmu'
  intro x
  exact h x

/-- **Absolute form.**  A finite solvable Galois extension of `ℚ` (inside `ℂ`) with enough roots
of unity is contained in the radical closure of `ℚ`. -/
theorem le_solvableByRad_of_solvable
    (E : IntermediateField ℚ ℂ) [FiniteDimensional ℚ E] [IsGalois ℚ E]
    (hsolv : Group.IsSolvable Gal(E/ℚ))
    (m : ℕ) (hprime : ∀ p, p.Prime → p ∣ Nat.card Gal(E/ℚ) → p ∣ m)
    (hmu : ∀ p, p.Prime → p ∣ m → (primitiveRoots p ℚ).Nonempty) :
    ∀ x : E, (x : ℂ) ∈ solvableByRad ℚ ℂ := by
  have hmu' : ∀ p, p.Prime → p ∣ Nat.card Gal(E/ℚ) → (primitiveRoots p ℚ).Nonempty :=
    fun p hp hpn => hmu p hp (hprime p hp hpn)
  have h := solvable_tower_aux (Nat.card Gal(E/ℚ)) (K := ℚ) (L := ↥E) rfl hsolv
    (fun a => IntermediateField.algebraMap_mem (solvableByRad ℚ ℂ) a) hmu'
  intro x
  exact h x

end Pconstructible
