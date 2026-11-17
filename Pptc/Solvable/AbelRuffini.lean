/-
Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/

import Pptc.Solvable.Roots
import Pptc.Solvable.Galois
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The converse Abel–Ruffini direction in Lean

Mathlib proves that an element solvable by radicals has a solvable Galois group.  This
file proves the converse over `ℂ`: a complex algebraic number whose minimal polynomial has
solvable Galois group lies in the radical closure of `ℚ`.

The proof uses the tower lemma from `Pptc.Solvable.Galois`.  We adjoin a primitive
`m`-th root of unity, where `m` is a factorial large enough that every prime occurring in
the tower divides `m`, and then take the splitting field of the minimal polynomial over
that cyclotomic field.
-/

namespace Pconstructible

open Polynomial IntermediateField

noncomputable section

/-- Converse Abel–Ruffini over `ℂ`: a complex algebraic number with solvable Galois
group is solvable by radicals. -/
theorem mem_solvableByRad_of_isSolvable_gal {z : ℂ}
    (hz : IsAlgebraic ℚ z) (h : Group.IsSolvable (minpoly ℚ z).Gal) :
    z ∈ solvableByRad ℚ ℂ := by
  classical
  let p : ℚ[X] := minpoly ℚ z
  have hp_ne : p ≠ 0 := minpoly.ne_zero hz.isIntegral
  have hp_sep : p.Separable := (minpoly.irreducible hz.isIntegral).separable
  let d : ℕ := Nat.card p.Gal
  have hd_pos : 0 < d := Nat.card_pos
  let m : ℕ := Nat.factorial d
  have hm_pos : 0 < m := Nat.factorial_pos d
  have hm_ne : m ≠ 0 := hm_pos.ne'
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm_ne
  let K₀ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  let q : ℚ[X] := p * (X ^ m - 1)
  have hq_ne : q ≠ 0 := by
    refine mul_ne_zero hp_ne ?_
    exact X_pow_sub_C_ne_zero hm_pos (1 : ℚ)
  let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (q.rootSet ℂ)
  have hE_split : IsSplittingField ℚ E q :=
    IntermediateField.adjoin_rootSet_isSplittingField
      (IsAlgClosed.splits (q.map (algebraMap ℚ ℂ)))
  haveI : FiniteDimensional ℚ E := IsSplittingField.finiteDimensional E q
  have hE_normal : Normal ℚ E := Normal.of_isSplittingField q
  haveI : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  have hE_sep : Algebra.IsSeparable ℚ E := inferInstance
  haveI hE_galois : IsGalois ℚ E := isGalois_iff.mpr ⟨hE_sep, hE_normal⟩
  have hq_solv : Group.IsSolvable q.Gal :=
    gal_mul_isSolvable h (gal_X_pow_sub_one_isSolvable m)
  have hE_solv : Group.IsSolvable Gal(E/ℚ) := by
    let e : E ≃ₐ[ℚ] q.SplittingField := Polynomial.IsSplittingField.algEquiv E q
    let e' : q.Gal ≃* Gal(E/ℚ) := (AlgEquiv.autCongr e).symm
    exact Group.isSolvable_of_surjective (f := e'.toMonoidHom) e'.surjective
  -- `K₀` is contained in `E`: ζ is a root of `X ^ m - 1`.
  have hζroot_eval : aeval ζ (X ^ m - 1 : ℚ[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_one, hζ.pow_eq_one, sub_self]
  have hζE : ζ ∈ E := by
    change ζ ∈ IntermediateField.adjoin ℚ (q.rootSet ℂ)
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    exact ⟨hq_ne, by rw [aeval_mul, hζroot_eval, mul_zero]⟩
  have hK₀E : K₀ ≤ E := by
    change IntermediateField.adjoin ℚ ({ζ} : Set ℂ) ≤ E
    exact IntermediateField.adjoin_le_iff.mpr (by simpa using hζE)
  -- The splitting field of `p` has degree `d`.
  let E₁ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (p.rootSet ℂ)
  have hE₁_split : IsSplittingField ℚ E₁ p :=
    IntermediateField.adjoin_rootSet_isSplittingField
      (IsAlgClosed.splits (p.map (algebraMap ℚ ℂ)))
  haveI : FiniteDimensional ℚ E₁ := IsSplittingField.finiteDimensional E₁ p
  have hE₁_normal : Normal ℚ E₁ := Normal.of_isSplittingField p
  haveI : Algebra.IsAlgebraic ℚ E₁ := Algebra.IsAlgebraic.of_finite ℚ E₁
  have hE₁_sep : Algebra.IsSeparable ℚ E₁ := inferInstance
  haveI hE₁_galois : IsGalois ℚ E₁ := isGalois_iff.mpr ⟨hE₁_sep, hE₁_normal⟩
  have hE₁_finrank : Module.finrank ℚ E₁ = d := by
    let e₁ : E₁ ≃ₐ[ℚ] p.SplittingField := Polynomial.IsSplittingField.algEquiv E₁ p
    let e₁' : p.Gal ≃* Gal(E₁/ℚ) := (AlgEquiv.autCongr e₁).symm
    have hcard : Nat.card Gal(E₁/ℚ) = Nat.card p.Gal :=
      (Nat.card_congr e₁'.toEquiv).symm
    rw [← IsGalois.card_aut_eq_finrank ℚ E₁, hcard]
  -- The roots of `X ^ m - 1` lie in `K₀`.
  have hX_ne : (X ^ m - 1 : ℚ[X]) ≠ 0 := X_pow_sub_C_ne_zero hm_pos (1 : ℚ)
  haveI : NeZero m := ⟨hm_ne⟩
  have hroots_subset_K₀ : (X ^ m - 1 : ℚ[X]).rootSet ℂ ⊆ K₀ := by
    intro x hx
    rw [Polynomial.mem_rootSet] at hx
    obtain ⟨-, hx0⟩ := hx
    have hx0' : x ^ m - 1 = 0 := by simpa using hx0
    have hxpow : x ^ m = 1 := sub_eq_zero.mp hx0'
    obtain ⟨i, -, hxi⟩ := hζ.eq_pow_of_pow_eq_one hxpow
    rw [← hxi]
    exact K₀.toSubfield.pow_mem (IntermediateField.subset_adjoin ℚ ({ζ} : Set ℂ) (by simp)) i
  -- `E` is the compositum of `E₁` and `K₀`.
  have hE₁_le_E : E₁ ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    change x ∈ IntermediateField.adjoin ℚ (q.rootSet ℂ)
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet] at hx ⊢
    refine ⟨hq_ne, ?_⟩
    dsimp only [q]
    rw [aeval_mul, hx.2, zero_mul]
  have hE_le_sup : E ≤ E₁ ⊔ K₀ := by
    change IntermediateField.adjoin ℚ (q.rootSet ℂ) ≤ E₁ ⊔ K₀
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Polynomial.mem_rootSet] at hx
    obtain ⟨-, hx0⟩ := hx
    dsimp only [q] at hx0
    rw [aeval_mul] at hx0
    rcases mul_eq_zero.mp hx0 with hp0 | hX0
    · exact (le_sup_left : E₁ ≤ E₁ ⊔ K₀) (IntermediateField.subset_adjoin ℚ (p.rootSet ℂ)
        (by rw [Polynomial.mem_rootSet]; exact ⟨hp_ne, hp0⟩))
    · exact (le_sup_right : K₀ ≤ E₁ ⊔ K₀) (hroots_subset_K₀ (by
        rw [Polynomial.mem_rootSet]; exact ⟨hX_ne, hX0⟩))
  have hE_eq : E = E₁ ⊔ K₀ := le_antisymm hE_le_sup (sup_le hE₁_le_E hK₀E)
  -- `K₀` has degree at most `m`.
  have hK₀_finrank_le : Module.finrank ℚ K₀ ≤ m := by
    have hζ_int : IsIntegral ℚ ζ :=
      ⟨X ^ m - 1, monic_X_pow_sub_C 1 hm_ne, by simpa [Polynomial.aeval_def] using hζroot_eval⟩
    have hmin_dvd : minpoly ℚ ζ ∣ (X ^ m - 1 : ℚ[X]) :=
      minpoly.dvd ℚ ζ hζroot_eval
    have hdeg : (minpoly ℚ ζ).natDegree ≤ m := by
      calc (minpoly ℚ ζ).natDegree ≤ (X ^ m - 1 : ℚ[X]).natDegree :=
            Polynomial.natDegree_le_of_dvd hmin_dvd hX_ne
        _ = m := Polynomial.natDegree_X_pow_sub_C
    change Module.finrank ℚ (IntermediateField.adjoin ℚ ({ζ} : Set ℂ)) ≤ m
    rw [IntermediateField.adjoin.finrank hζ_int]
    exact hdeg
  -- `E` has degree at most `d * m`.
  have hE_finrank_le : Module.finrank ℚ E ≤ d * m := by
    rw [hE_eq]
    calc Module.finrank ℚ ↥(E₁ ⊔ K₀) ≤ Module.finrank ℚ E₁ * Module.finrank ℚ K₀ :=
          IntermediateField.finrank_sup_le E₁ K₀
      _ ≤ d * m := Nat.mul_le_mul (le_of_eq hE₁_finrank) hK₀_finrank_le
  -- View `E` as a finite Galois extension of `K₀`.
  let L : IntermediateField K₀ ℂ := IntermediateField.extendScalars hK₀E
  let eEL : E ≃ₐ[ℚ] L :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_mul' := fun x y => by ext; rfl
      map_add' := fun x y => by ext; rfl
      commutes' := fun r => by ext; rfl }
  haveI : FiniteDimensional ℚ L := eEL.toLinearEquiv.finiteDimensional
  haveI : IsGalois ℚ L := IsGalois.of_algEquiv eEL
  haveI : FiniteDimensional K₀ L := Module.Finite.of_restrictScalars_finite ℚ K₀ L
  haveI : IsGalois K₀ L := IsGalois.tower_top_of_isGalois ℚ K₀ L
  have hsolvL : Group.IsSolvable Gal(L/K₀) := by
    haveI : Group.IsSolvable Gal(L/ℚ) := by
      let e' : Gal(E/ℚ) ≃* Gal(L/ℚ) := AlgEquiv.autCongr eEL
      exact Group.isSolvable_of_surjective (f := e'.toMonoidHom) e'.surjective
    exact Group.isSolvable_of_isSolvable_injective
      (G := Gal(L/K₀)) (G' := Gal(L/ℚ))
      (f := AlgEquiv.restrictScalarsHom (R := ℚ) (S := K₀) (A := L))
      (AlgEquiv.restrictScalarsHom_injective (R := ℚ) (S := K₀) (A := L))
  -- The degree of `L / K₀` divides `d`: restrict automorphisms to the splitting field of `p`.
  let inclL : L →ₐ[ℚ] ℂ :=
    { toFun := fun x => x.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun r => rfl }
  let E₁' : IntermediateField ℚ L := E₁.comap inclL
  let K₀' : IntermediateField ℚ L := K₀.comap inclL
  let eE₁' : E₁' ≃ₐ[ℚ] E₁ :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hE₁_le_E y.2⟩, y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_mul' := fun x y => by ext; rfl
      map_add' := fun x y => by ext; rfl
      commutes' := fun r => by ext; rfl }
  haveI hE₁'_normal : Normal ℚ ↥E₁' := Normal.of_algEquiv eE₁'.symm
  have hsup : E₁' ⊔ K₀' = ⊤ := by
    apply le_antisymm le_top
    intro x _
    have hxE : x.1 ∈ E₁ ⊔ K₀ := by
      rw [← hE_eq]
      exact x.2
    have hmap : E₁ ⊔ K₀ ≤ (E₁' ⊔ K₀').map inclL := by
      rw [IntermediateField.sup_def]
      apply IntermediateField.adjoin_le_iff.mpr
      intro y hy
      rcases hy with hy | hy
      · change y ∈ IntermediateField.map inclL (E₁' ⊔ K₀')
        rw [IntermediateField.mem_map]
        exact ⟨⟨y, hE₁_le_E hy⟩, IntermediateField.subset_adjoin ℚ _ (Or.inl hy), rfl⟩
      · change y ∈ IntermediateField.map inclL (E₁' ⊔ K₀')
        rw [IntermediateField.mem_map]
        exact ⟨⟨y, hK₀E hy⟩, IntermediateField.subset_adjoin ℚ _ (Or.inr hy), rfl⟩
    have hxmap : x.1 ∈ IntermediateField.map inclL (E₁' ⊔ K₀') := hmap hxE
    rw [IntermediateField.mem_map] at hxmap
    obtain ⟨y, hy, hyeq⟩ := hxmap
    rw [Subtype.ext hyeq] at hy
    exact hy
  letI : Normal ℚ ↥E₁' := hE₁'_normal
  let res : Gal(L/K₀) →* Gal(E₁'/ℚ) :=
    (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := L) E₁').comp
      (AlgEquiv.restrictScalarsHom (R := ℚ) (S := K₀) (A := L))
  have hres_inj : Function.Injective res := by
    refine (injective_iff_map_eq_one res).mpr fun σ hσ => ?_
    let σ₀ : Gal(L/ℚ) := AlgEquiv.restrictScalars ℚ σ
    have hσ' : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := L) E₁')
        (AlgEquiv.restrictScalars ℚ σ) = 1 := by
      simpa [res] using hσ
    have hσE : σ₀ ∈ E₁'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hσ'' : σ₀.restrictNormal E₁' = 1 := by
        simpa [AlgEquiv.restrictNormalHom] using hσ'
      exact (@AlgEquiv.restrictNormal_eq_one_iff ℚ _ L _ _ E₁' hE₁'_normal σ₀).mp hσ'' x hx
    have hσK : σ₀ ∈ K₀'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hx' : algebraMap K₀ L (⟨x.1, hx⟩ : K₀) = x := by ext; rfl
      simpa [σ₀, AlgEquiv.restrictScalars_apply, hx'] using σ.commutes (⟨x.1, hx⟩ : K₀)
    have hσtop : σ₀ ∈ (E₁' ⊔ K₀').fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hσE, hσK⟩
    have hσbot : σ₀ ∈ (⊥ : Subgroup Gal(L/ℚ)) := by
      rw [← IntermediateField.fixingSubgroup_top, ← hsup]
      exact hσtop
    have hσ₀ : σ₀ = 1 := by simpa using hσbot
    exact AlgEquiv.restrictScalars_injective ℚ hσ₀
  have hcardE₁' : Nat.card Gal(E₁'/ℚ) = d := by
    let e' : Gal(E₁'/ℚ) ≃* Gal(E₁/ℚ) := AlgEquiv.autCongr eE₁'
    calc Nat.card Gal(E₁'/ℚ) = Nat.card Gal(E₁/ℚ) := Nat.card_congr e'.toEquiv
      _ = Module.finrank ℚ E₁ := IsGalois.card_aut_eq_finrank ℚ E₁
      _ = d := hE₁_finrank
  have hdvd : Nat.card Gal(L/K₀) ∣ d := by
    have h := Subgroup.card_dvd_of_injective res hres_inj
    rwa [hcardE₁'] at h
  have hprime : ∀ (p : ℕ), p.Prime → p ∣ Nat.card Gal(L/K₀) → p ∣ m := by
    intro p hp hpn
    have hpd : p ∣ d := hpn.trans hdvd
    have hle : p ≤ d := Nat.le_of_dvd hd_pos hpd
    have h : p ∣ d.factorial := Nat.dvd_factorial hp.pos hle
    simpa [m] using h
  -- `K₀` contains all primitive roots of unity of prime order dividing `m`.
  have hmu : ∀ (p : ℕ), p.Prime → p ∣ m → (primitiveRoots p K₀).Nonempty := by
    intro p hp hpm
    have hmem : ζ ^ (m / p) ∈ K₀ :=
      K₀.toSubfield.pow_mem (IntermediateField.subset_adjoin ℚ ({ζ} : Set ℂ) (by simp)) (m / p)
    have hprim : IsPrimitiveRoot (ζ ^ (m / p)) p :=
      hζ.pow hm_pos (Nat.div_mul_cancel hpm).symm
    refine ⟨⟨ζ ^ (m / p), hmem⟩, ?_⟩
    rw [mem_primitiveRoots hp.pos]
    exact hprim.of_map_of_injective (f := K₀.val) K₀.val.injective
  -- `K₀` is contained in the radical closure.
  have hζS : ζ ∈ solvableByRad ℚ ℂ :=
    solvableByRad.rad_mem hm_ne (by rw [hζ.pow_eq_one]; exact one_mem _)
  have hK₀S : ∀ x : K₀, algebraMap K₀ ℂ x ∈ solvableByRad ℚ ℂ := by
    intro x
    have hK₀_le_S : K₀ ≤ solvableByRad ℚ ℂ := by
      change IntermediateField.adjoin ℚ ({ζ} : Set ℂ) ≤ solvableByRad ℚ ℂ
      exact IntermediateField.adjoin_le_iff.mpr (by simpa using hζS)
    exact hK₀_le_S x.2
  have hL : ∀ x : L, (x : ℂ) ∈ solvableByRad ℚ ℂ :=
    le_solvableByRad_of_solvable_tower hK₀S L hsolvL m hprime hmu
  -- Finally, `z` is a root of `p`, hence lies in `E`, hence in `L`.
  have hzE : z ∈ E := by
    change z ∈ IntermediateField.adjoin ℚ (q.rootSet ℂ)
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hq_ne, ?_⟩
    dsimp only [q]
    rw [aeval_mul, minpoly.aeval, zero_mul]
  have hzL : z ∈ L := by
    change z ∈ E
    exact hzE
  simpa using hL ⟨z, hzL⟩

end

end Pconstructible
