/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.QuadraticForm.Restriction

/-!
# Orthogonal reflections and rank-one isometry transitivity

Mathlib 4.33 has no Witt extension/cancellation theorem, so the Witt-theoretic layer has to
be built here.  This file supplies the base ingredient: for a quadratic form `Q` over a field
`k` with `2` invertible, and a vector `a` with `Q a ≠ 0`, the *orthogonal reflection* in the
hyperplane orthogonal to `a`,

`reflection Q a ha x = x - (2 * (Q.associated x a * (Q a)⁻¹)) • a`,

is a linear involution that fixes the hyperplane `aᗮ` pointwise, sends `a` to `-a`, and
preserves `Q`.

## Main definitions

* `Pptc.HasseMinkowski.reflection`

## Main results

* `reflection_apply`, `reflection_involutive`, `reflection_self`
* `reflection_isometry`
* `exists_isometryEquiv_of_Q_eq` (rank-one transitivity)
-/

open Module QuadraticMap

namespace Pptc.HasseMinkowski

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]

/-! ### Bridging `polar` and `associated` -/

-- Theorem: the polar form is twice the associated bilinear form (characteristic `≠ 2`).
theorem polar_eq_two_mul_associated (Q : QuadraticForm k V) (x y : V) :
    QuadraticMap.polar Q x y = 2 * Q.associated x y := by
  rw [QuadraticMap.polar, QuadraticMap.associated_apply]
  simp only [Module.End.smul_def, QuadraticMap.half_moduleEnd_apply_eq_half_smul,
    smul_eq_mul]
  rw [← mul_assoc, mul_invOf_self, one_mul]

-- Theorem: expansion of `Q` on a sum in terms of the associated bilinear form.
theorem map_add_eq_associated (Q : QuadraticForm k V) (x y : V) :
    Q (x + y) = Q x + Q y + 2 * Q.associated x y := by
  rw [QuadraticMap.map_add Q x y, polar_eq_two_mul_associated]

-- Theorem: expansion of `Q` on a difference in terms of the associated bilinear form.
theorem map_sub_eq_associated (Q : QuadraticForm k V) (x y : V) :
    Q (x - y) = Q x + Q y - 2 * Q.associated x y := by
  rw [sub_eq_add_neg, map_add_eq_associated, QuadraticMap.map_neg]
  have h : Q.associated x (-y) = -Q.associated x y := map_neg (Q.associated x) y
  rw [h]; ring

/-! ### The orthogonal reflection as a linear map -/

/-- The underlying linear map of the orthogonal reflection in `a`:
`x ↦ x - 2 * (Q.associated x a / Q a) • a`. -/
noncomputable def reflectionLinearMap (Q : QuadraticForm k V) (a : V) : V →ₗ[k] V where
  toFun x := x - (2 * (Q.associated x a * (Q a)⁻¹)) • a
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply]
    module
  map_smul' c x := by
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    module

-- Theorem: the defining formula of `reflectionLinearMap`.
theorem reflectionLinearMap_apply (Q : QuadraticForm k V) (a x : V) :
    reflectionLinearMap Q a x = x - (2 * (Q.associated x a * (Q a)⁻¹)) • a :=
  rfl

-- Theorem: `reflectionLinearMap` flips the sign of the associated pairing with `a`.
theorem associated_reflectionLinearMap (Q : QuadraticForm k V) (a : V) (ha : Q a ≠ 0)
    (x : V) :
    Q.associated (reflectionLinearMap Q a x) a = -Q.associated x a := by
  rw [reflectionLinearMap_apply]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    associated_self_eq, smul_eq_mul]
  field_simp
  ring

-- Theorem: `reflectionLinearMap` is an involution.
theorem reflectionLinearMap_involutive (Q : QuadraticForm k V) (a : V) (ha : Q a ≠ 0) :
    Function.Involutive (reflectionLinearMap Q a) := by
  intro x
  rw [reflectionLinearMap_apply, associated_reflectionLinearMap Q a ha,
    reflectionLinearMap_apply]
  module

-- Theorem: `reflectionLinearMap` sends `a` to `-a`.
theorem reflectionLinearMap_self (Q : QuadraticForm k V) (a : V) (ha : Q a ≠ 0) :
    reflectionLinearMap Q a a = -a := by
  rw [reflectionLinearMap_apply, associated_self_eq, mul_inv_cancel₀ ha, mul_one]
  module

/-! ### The orthogonal reflection -/

/-- The orthogonal reflection in the hyperplane orthogonal to `a`, for `Q a ≠ 0`, as a
linear equivalence (`x ↦ x - 2 * (Q.associated x a / Q a) • a`). -/
noncomputable def reflection (Q : QuadraticForm k V) (a : V) (ha : Q a ≠ 0) : V ≃ₗ[k] V :=
  LinearEquiv.ofInvolutive (reflectionLinearMap Q a) (reflectionLinearMap_involutive Q a ha)

-- Theorem: the defining formula of `reflection`.
theorem reflection_apply (Q : QuadraticForm k V) (a : V) (ha : Q a ≠ 0) (x : V) :
    reflection Q a ha x = x - (2 * (Q.associated x a * (Q a)⁻¹)) • a := by
  rw [reflection, LinearEquiv.coe_ofInvolutive, reflectionLinearMap_apply]

-- Theorem: the orthogonal reflection is an involution.
theorem reflection_involutive (Q : QuadraticForm k V) (a : V) (ha : Q a ≠ 0) :
    Function.Involutive (reflection Q a ha) := by
  simpa only [reflection, LinearEquiv.coe_ofInvolutive] using reflectionLinearMap_involutive Q a ha

-- Theorem: the orthogonal reflection sends `a` to `-a`.
theorem reflection_self (Q : QuadraticForm k V) (a : V) (ha : Q a ≠ 0) :
    reflection Q a ha a = -a := by
  rw [reflection, LinearEquiv.coe_ofInvolutive, reflectionLinearMap_self Q a ha]

-- Theorem: the orthogonal reflection preserves `Q`.
noncomputable def reflection_isometry (Q : QuadraticForm k V) (a : V) (ha : Q a ≠ 0) :
    QuadraticMap.IsometryEquiv Q Q where
  toLinearEquiv := reflection Q a ha
  map_app' := by
    intro x
    change Q (reflection Q a ha x) = Q x
    set t : k := 2 * (Q.associated x a * (Q a)⁻¹) with ht
    have hta : t * Q a = 2 * Q.associated x a := by
      rw [ht]; field_simp
    rw [reflection_apply, ← ht, sub_eq_add_neg, map_add_eq_associated,
      QuadraticMap.map_neg, QuadraticMap.map_smul]
    rw [map_neg (Q.associated x), map_smul, smul_eq_mul]
    have hzero : (t * t) * Q a = 2 * (t * Q.associated x a) := by
      rw [mul_assoc, hta]; ring
    rw [hzero]; ring

/-! ### Rank-one isometry transitivity -/

-- Theorem: two vectors with the same nonzero value of `Q` are exchanged by an isometry of `Q`.
theorem exists_isometryEquiv_of_Q_eq (Q : QuadraticForm k V) {v w : V}
    (hv : Q v ≠ 0) (h : Q v = Q w) :
    ∃ φ : QuadraticMap.IsometryEquiv Q Q, φ v = w := by
  have hw : Q w ≠ 0 := by rw [← h]; exact hv
  by_cases hd : Q (v - w) = 0
  · have hBvw : Q.associated v w = Q v := by
      have h0 : Q v + Q v - 2 * Q.associated v w = 0 := by
        have h' := map_sub_eq_associated Q v w
        rw [← h] at h'
        rw [← h']; exact hd
      have h1 : 2 * Q.associated v w = 2 * Q v := by
        rw [(sub_eq_zero.mp h0).symm, two_mul]
      exact mul_left_cancel₀ (Invertible.ne_zero (2 : k)) h1
    have hQplus : Q (v + w) = 2 * (2 * Q v) := by
      rw [map_add_eq_associated, ← h, hBvw]; ring
    have h2ne : (2 : k) ≠ 0 := Invertible.ne_zero 2
    have hplus : Q (v + w) ≠ 0 := by
      rw [hQplus]; exact mul_ne_zero h2ne (mul_ne_zero h2ne hv)
    have hB2 : 2 * Q.associated v (v + w) = Q (v + w) := by
      rw [map_add, associated_self_eq, hBvw, hQplus]; ring
    have hcoef2 : 2 * (Q.associated v (v + w) * (Q (v + w))⁻¹) = 1 := by
      rw [← mul_assoc, hB2, mul_inv_cancel₀ hplus]
    have h1 : reflection Q (v + w) hplus v = -w := by
      rw [reflection_apply, hcoef2, one_smul]; abel
    have h2 : reflection Q w hw (-w) = w := by
      rw [map_neg, reflection_self]; abel
    refine ⟨(reflection_isometry Q (v + w) hplus).trans
      (reflection_isometry Q w hw), ?_⟩
    change reflection Q w hw (reflection Q (v + w) hplus v) = w
    rw [h1, h2]
  · have hB : 2 * Q.associated v (v - w) = Q (v - w) := by
      rw [map_sub, associated_self_eq, map_sub_eq_associated, ← h]; ring
    have hcoef : 2 * (Q.associated v (v - w) * (Q (v - w))⁻¹) = 1 := by
      rw [← mul_assoc, hB, mul_inv_cancel₀ hd]
    refine ⟨reflection_isometry Q (v - w) hd, ?_⟩
    change reflection Q (v - w) hd v = w
    rw [reflection_apply, hcoef, one_smul]; abel

/-! ### Rank-one Witt cancellation

An isometry of `Q` preserves the associated bilinear form (the polar form is determined by
`Q` and `2` is invertible), so the isometry carrying `v` to `w` maps the hyperplane
`vᗮ` onto `wᗮ`.  Restricting it to those submodules and using `Q (φ x) = Q x` gives an
isometry of the restricted forms: isometric non-isotropic vectors have isometric orthogonal
complements. -/

-- Theorem: an isometry of `Q` preserves the associated bilinear form.
theorem associated_isometryEquiv_map (Q : QuadraticForm k V)
    (φ : QuadraticMap.IsometryEquiv Q Q) (x y : V) :
    Q.associated (φ x) (φ y) = Q.associated x y := by
  apply mul_left_cancel₀ (Invertible.ne_zero (2 : k))
  rw [← polar_eq_two_mul_associated Q (φ x) (φ y), ← polar_eq_two_mul_associated Q x y]
  simp only [QuadraticMap.polar]
  rw [show φ x + φ y = φ (x + y) from (map_add φ.toLinearEquiv x y).symm]
  simp only [QuadraticMap.IsometryEquiv.map_app]

-- Theorem: the isometry of `Q` carrying `v` to `w` restricts to their orthocomplements.
noncomputable def isometryEquivOrthoComplSpanOfQeq (Q : QuadraticForm k V)
    (hQ : Q.Nondegenerate) {v w : V} (hv : Q v ≠ 0) (h : Q v = Q w) :
    QuadraticMap.IsometryEquiv
      (restrict Q (orthoCompl Q (Submodule.span k {v})))
      (restrict Q (orthoCompl Q (Submodule.span k {w}))) := by
  have _ := hQ
  have hex := exists_isometryEquiv_of_Q_eq Q hv h
  let φ : QuadraticMap.IsometryEquiv Q Q := Classical.choose hex
  have hφ : φ v = w := Classical.choose_spec hex
  have hmap_le :
      Submodule.map (φ.toLinearEquiv : V →ₗ[k] V) (orthoCompl Q (Submodule.span k {v})) ≤
        orthoCompl Q (Submodule.span k {w}) := by
    intro y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_orthoCompl] at hx ⊢
    intro u hu
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨c, rfl⟩ := hu
    have hx0 : Q.associated x (c • v) = 0 :=
      hx (c • v) (Submodule.mem_span_singleton.mpr ⟨c, rfl⟩)
    have hcw : φ (c • v) = c • w := by rw [map_smul, hφ]
    calc Q.associated (φ x) (c • w)
        = Q.associated (φ x) (φ (c • v)) := by rw [hcw]
      _ = Q.associated x (c • v) := associated_isometryEquiv_map Q φ x (c • v)
      _ = 0 := hx0
  have hmap_ge : orthoCompl Q (Submodule.span k {w}) ≤
      Submodule.map (φ.toLinearEquiv : V →ₗ[k] V) (orthoCompl Q (Submodule.span k {v})) := by
    intro y hy
    refine ⟨φ.symm y, ?_, ?_⟩
    · rw [mem_orthoCompl] at hy
      change ∀ u ∈ Submodule.span k {v}, Q.associated (φ.symm y) u = 0
      intro u hu
      rw [Submodule.mem_span_singleton] at hu
      obtain ⟨c, rfl⟩ := hu
      have hy0 : Q.associated y (c • w) = 0 :=
        hy (c • w) (Submodule.mem_span_singleton.mpr ⟨c, rfl⟩)
      have hcw : φ (c • v) = c • w := by rw [map_smul, hφ]
      calc Q.associated (φ.symm y) (c • v)
          = Q.associated (φ (φ.symm y)) (φ (c • v)) :=
            (associated_isometryEquiv_map Q φ (φ.symm y) (c • v)).symm
        _ = Q.associated y (c • w) := by
            rw [QuadraticMap.IsometryEquiv.apply_symm_apply, hcw]
        _ = 0 := hy0
    · exact LinearEquiv.apply_symm_apply φ.toLinearEquiv y
  have hW : Submodule.map (φ.toLinearEquiv : V →ₗ[k] V) (orthoCompl Q (Submodule.span k {v})) =
      orthoCompl Q (Submodule.span k {w}) := le_antisymm hmap_le hmap_ge
  rw [← hW]
  exact
    { toLinearEquiv :=
        LinearEquiv.submoduleMap φ.toLinearEquiv (orthoCompl Q (Submodule.span k {v}))
      map_app' := by
        intro m
        rw [restrict_apply, restrict_apply]
        exact QuadraticMap.IsometryEquiv.map_app φ (m : V) }

-- Theorem: rank-one Witt cancellation: isometric non-isotropic vectors have isometric
-- orthogonal complements.
theorem isometryEquiv_orthoCompl_span_of_Q_eq (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    {v w : V} (hv : Q v ≠ 0) (h : Q v = Q w) :
    Nonempty (QuadraticMap.IsometryEquiv
      (restrict Q (orthoCompl Q (Submodule.span k {v})))
      (restrict Q (orthoCompl Q (Submodule.span k {w})))) :=
  ⟨isometryEquivOrthoComplSpanOfQeq Q hQ hv h⟩

/-! ### Witt extension and general Witt cancellation

The rank-one result above is upgraded to full Witt cancellation.  The engine is Witt's
extension theorem, proved by induction on the dimension of the embedded space: any two
isometric embeddings `ψ₁, ψ₂` of a nondegenerate quadratic space `Y` into `V` differ by
an isometry of `V` (equivalently, an isometric embedding of a nondegenerate subspace
extends to an isometry of the whole space).  Splitting off one non-isotropic vector `y`
reduces the dimension by one; the induction hypothesis matches `ψ₁, ψ₂` on the
orthogonal complement of `y`, and the remaining discrepancy is repaired by a reflection
isometry that fixes the image of that orthocomplement pointwise.  Applying the extension
to `ψ₁ = W₁.subtype` and `ψ₂ = e` then maps `W₁ᗮ` onto `W₂ᗮ`. -/

/-- A linear map preserving `Q` preserves the associated bilinear form. -/
theorem associated_map_of_apply_eq {Y : Type*} [AddCommGroup Y] [Module k Y]
    {Q : QuadraticForm k V} {QY : QuadraticForm k Y} (ψ : Y →ₗ[k] V)
    (hψ : ∀ y, Q (ψ y) = QY y) (y z : Y) :
    Q.associated (ψ y) (ψ z) = QY.associated y z := by
  have hcomp : QY = Q.comp ψ := by
    ext y
    rw [QuadraticMap.comp_apply, hψ y]
  rw [hcomp]
  simp only [QuadraticMap.associated_comp (S := k), LinearMap.compl₁₂_apply]

-- Theorem: two vectors with the same nonzero `Q`-value lying in the orthocomplement of `U`
-- are exchanged by an isometry of `Q` that fixes `U` pointwise.
theorem exists_isometryEquiv_of_Q_eq_fixing (Q : QuadraticForm k V) {U : Submodule k V}
    {v w : V} (hv : Q v ≠ 0) (h : Q v = Q w)
    (hUv : ∀ u ∈ U, Q.associated u v = 0) (hUw : ∀ u ∈ U, Q.associated u w = 0) :
    ∃ τ : QuadraticMap.IsometryEquiv Q Q, τ v = w ∧ ∀ u ∈ U, τ u = u := by
  have hw : Q w ≠ 0 := by rw [← h]; exact hv
  have hUvw : ∀ u ∈ U, Q.associated u (v - w) = 0 := by
    intro u hu
    rw [map_sub, hUv u hu, hUw u hu, sub_zero]
  have hUadd : ∀ u ∈ U, Q.associated u (v + w) = 0 := by
    intro u hu
    rw [map_add, hUv u hu, hUw u hu, add_zero]
  by_cases hd : Q (v - w) = 0
  · -- `Q (v - w) = 0`: reflect first in `v + w`, then in `w`; both fix `U`.
    have hBvw : Q.associated v w = Q v := by
      have h0 : Q v + Q v - 2 * Q.associated v w = 0 := by
        have h' := map_sub_eq_associated Q v w
        rw [← h] at h'
        rw [← h']; exact hd
      have h1 : 2 * Q.associated v w = 2 * Q v := by
        rw [(sub_eq_zero.mp h0).symm, two_mul]
      exact mul_left_cancel₀ (Invertible.ne_zero (2 : k)) h1
    have hQplus : Q (v + w) = 2 * (2 * Q v) := by
      rw [map_add_eq_associated, ← h, hBvw]; ring
    have h2ne : (2 : k) ≠ 0 := Invertible.ne_zero 2
    have hplus : Q (v + w) ≠ 0 := by
      rw [hQplus]; exact mul_ne_zero h2ne (mul_ne_zero h2ne hv)
    have hB2 : 2 * Q.associated v (v + w) = Q (v + w) := by
      rw [map_add, associated_self_eq, hBvw, hQplus]; ring
    have hcoef2 : 2 * (Q.associated v (v + w) * (Q (v + w))⁻¹) = 1 := by
      rw [← mul_assoc, hB2, mul_inv_cancel₀ hplus]
    have h1 : reflection Q (v + w) hplus v = -w := by
      rw [reflection_apply, hcoef2, one_smul]; abel
    have h2 : reflection Q w hw (-w) = w := by
      rw [map_neg, reflection_self]; abel
    have hfix1 : ∀ u ∈ U, reflection Q (v + w) hplus u = u := by
      intro u hu
      rw [reflection_apply, hUadd u hu, zero_mul, mul_zero, zero_smul, sub_zero]
    have hfix2 : ∀ u ∈ U, reflection Q w hw u = u := by
      intro u hu
      rw [reflection_apply, hUw u hu, zero_mul, mul_zero, zero_smul, sub_zero]
    refine ⟨(reflection_isometry Q (v + w) hplus).trans (reflection_isometry Q w hw),
      ?_, ?_⟩
    · change reflection Q w hw (reflection Q (v + w) hplus v) = w
      rw [h1, h2]
    · intro u hu
      change reflection Q w hw (reflection Q (v + w) hplus u) = u
      rw [hfix1 u hu, hfix2 u hu]
  · -- `Q (v - w) ≠ 0`: one reflection in `v - w` fixes `U` and swaps the vectors.
    have hB : 2 * Q.associated v (v - w) = Q (v - w) := by
      rw [map_sub, associated_self_eq, map_sub_eq_associated, ← h]; ring
    have hcoef : 2 * (Q.associated v (v - w) * (Q (v - w))⁻¹) = 1 := by
      rw [← mul_assoc, hB, mul_inv_cancel₀ hd]
    have hv' : reflection Q (v - w) hd v = w := by
      rw [reflection_apply, hcoef, one_smul]; abel
    have hfix : ∀ u ∈ U, reflection Q (v - w) hd u = u := by
      intro u hu
      rw [reflection_apply, hUvw u hu, zero_mul, mul_zero, zero_smul, sub_zero]
    exact ⟨reflection_isometry Q (v - w) hd, hv', hfix⟩

-- Theorem (Witt extension): any two isometric embeddings of a nondegenerate quadratic
-- space `Y` into `V` differ by an isometry of `V`.
set_option linter.style.haveILetI false in
theorem exists_isometryEquiv_of_isometric_embeddings (Q : QuadraticForm k V)
    [FiniteDimensional k V] :
    ∀ (n : ℕ) (Y : Type*) [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
      (QY : QuadraticForm k Y), QY.Nondegenerate → finrank k Y = n →
      ∀ (ψ₁ ψ₂ : Y →ₗ[k] V), (∀ y, Q (ψ₁ y) = QY y) → (∀ y, Q (ψ₂ y) = QY y) →
      ∃ g : QuadraticMap.IsometryEquiv Q Q, ∀ y, g (ψ₁ y) = ψ₂ y := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Y _ _ _ QY hQY hdim ψ₁ ψ₂ hψ₁ hψ₂
    by_cases hnt : Nontrivial Y
    · haveI := hnt
      obtain ⟨y, hy0⟩ := exists_ne (0 : Y)
      have hex : ∃ y : Y, QY y ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have hyrad : y ∈ QY.radical := by
          rw [QuadraticMap.mem_radical_iff']
          exact ⟨hcon y, fun z => by rw [hcon (y + z), hcon z]⟩
        rw [hQY.radical_eq_bot, Submodule.mem_bot] at hyrad
        exact hy0 hyrad
      obtain ⟨y, hy⟩ := hex
      let Y₀ : Submodule k Y := orthoCompl QY (k ∙ y)
      have hY₀nd : (restrict QY Y₀).Nondegenerate :=
        restrict_orthoCompl_span_singleton_nondegenerate' QY hQY hy
      have hne : Y₀ ≠ ⊤ := by
        intro htop
        have hy0' : y ∈ Y₀ := by rw [htop]; trivial
        have horth := (mem_orthoCompl.mp hy0') y (Submodule.mem_span_singleton_self y)
        rw [associated_self_eq] at horth
        exact hy horth
      have hfin : finrank k Y₀ < n := by
        rw [← hdim]
        exact Submodule.finrank_lt hne
      obtain ⟨g₀, hg₀⟩ := ih (finrank k Y₀) hfin Y₀ (restrict QY Y₀) hY₀nd rfl
        (ψ₁.comp Y₀.subtype) (ψ₂.comp Y₀.subtype)
        (fun z => by rw [LinearMap.comp_apply, restrict_apply]; exact hψ₁ (z : Y))
        (fun z => by rw [LinearMap.comp_apply, restrict_apply]; exact hψ₂ (z : Y))
      have hg₀' : ∀ z : Y₀, g₀ (ψ₁ (z : Y)) = ψ₂ (z : Y) := fun z => hg₀ z
      let U : Submodule k V := Y₀.map ψ₂
      have hUu : ∀ u ∈ U, Q.associated u (g₀ (ψ₁ y)) = 0 := by
        intro u hu
        rw [Submodule.mem_map] at hu
        obtain ⟨z, hz, rfl⟩ := hu
        have hz' : ψ₂ z = g₀ (ψ₁ z) := (hg₀' (⟨z, hz⟩ : Y₀)).symm
        rw [hz', associated_isometryEquiv_map Q g₀ (ψ₁ z) (ψ₁ y),
          associated_map_of_apply_eq ψ₁ hψ₁ z y]
        exact (mem_orthoCompl.mp hz) y (Submodule.mem_span_singleton_self y)
      have hUw : ∀ u ∈ U, Q.associated u (ψ₂ y) = 0 := by
        intro u hu
        rw [Submodule.mem_map] at hu
        obtain ⟨z, hz, rfl⟩ := hu
        rw [associated_map_of_apply_eq ψ₂ hψ₂ z y]
        exact (mem_orthoCompl.mp hz) y (Submodule.mem_span_singleton_self y)
      have hQu : Q (g₀ (ψ₁ y)) ≠ 0 := by
        rw [QuadraticMap.IsometryEquiv.map_app, hψ₁ y]; exact hy
      have hQeq : Q (g₀ (ψ₁ y)) = Q (ψ₂ y) := by
        rw [QuadraticMap.IsometryEquiv.map_app, hψ₁ y, hψ₂ y]
      obtain ⟨τ, hτu, hτfix⟩ := exists_isometryEquiv_of_Q_eq_fixing Q hQu hQeq hUu hUw
      have hgy : (g₀.trans τ) (ψ₁ y) = ψ₂ y := by
        change τ (g₀ (ψ₁ y)) = ψ₂ y; exact hτu
      have hgz : ∀ z : Y₀, (g₀.trans τ) (ψ₁ (z : Y)) = ψ₂ (z : Y) := by
        intro z
        change τ (g₀ (ψ₁ (z : Y))) = ψ₂ (z : Y)
        rw [hg₀' z]
        exact hτfix (ψ₂ (z : Y)) (Submodule.mem_map_of_mem (f := ψ₂) z.2)
      refine ⟨g₀.trans τ, fun y' => ?_⟩
      have hcompl : IsCompl (k ∙ y) Y₀ :=
        isCompl_span_singleton_orthoCompl QY (by rwa [associated_self_eq])
      have hy' : y' ∈ (k ∙ y) ⊔ Y₀ := by rw [hcompl.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [← hab]
      simp only [map_add, map_smul]
      rw [hgy, hgz ⟨b, hb⟩]
    · haveI : Subsingleton Y := not_nontrivial_iff_subsingleton.mp hnt
      refine ⟨QuadraticMap.IsometryEquiv.refl Q, fun y' => ?_⟩
      rw [Subsingleton.elim y' 0]
      simp

-- Theorem (general Witt cancellation): isometric nondegenerate submodules have isometric
-- orthogonal complements.
theorem isometryEquiv_orthoCompl_of_isometryEquiv_restrict (Q : QuadraticForm k V)
    [FiniteDimensional k V] (hQ : Q.Nondegenerate) {W₁ W₂ : Submodule k V}
    (h₁ : (restrict Q W₁).Nondegenerate) (h₂ : (restrict Q W₂).Nondegenerate)
    (e : QuadraticMap.IsometryEquiv (restrict Q W₁) (restrict Q W₂)) :
    Nonempty (QuadraticMap.IsometryEquiv
      (restrict Q (orthoCompl Q W₁)) (restrict Q (orthoCompl Q W₂))) := by
  have _ := hQ
  have _ := h₂
  have hex := exists_isometryEquiv_of_isometric_embeddings Q (finrank k W₁) W₁
    (restrict Q W₁) h₁ rfl W₁.subtype
    (W₂.subtype.comp (e.toLinearEquiv : W₁ →ₗ[k] W₂))
    (fun y => restrict_apply Q W₁ y)
    (fun y => QuadraticMap.IsometryEquiv.map_app e y)
  obtain ⟨g, hg⟩ := hex
  have hg' : ∀ w : W₁, g (w : V) = ((e w : W₂) : V) := fun w => hg w
  have hmap_le : Submodule.map (g.toLinearEquiv : V →ₗ[k] V) (orthoCompl Q W₁) ≤
      orthoCompl Q W₂ := by
    intro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_orthoCompl] at hy ⊢
    intro u hu
    obtain ⟨w, hw⟩ : ∃ w : W₁, (e w : V) = u := ⟨e.symm ⟨u, hu⟩, by simp⟩
    rw [← hw]
    calc Q.associated (g y) ((e w : W₂) : V)
        = Q.associated (g y) (g (w : V)) := by rw [hg' w]
      _ = Q.associated y (w : V) := associated_isometryEquiv_map Q g y (w : V)
      _ = 0 := hy (w : V) w.2
  have hmap_ge : orthoCompl Q W₂ ≤
      Submodule.map (g.toLinearEquiv : V →ₗ[k] V) (orthoCompl Q W₁) := by
    intro x hx
    refine ⟨g.symm x, ?_, ?_⟩
    · rw [mem_orthoCompl] at hx
      change ∀ w ∈ W₁, Q.associated (g.symm x) w = 0
      intro u hu
      rw [← associated_isometryEquiv_map Q g (g.symm x) u,
        QuadraticMap.IsometryEquiv.apply_symm_apply]
      rw [hg' ⟨u, hu⟩]
      exact hx ((e ⟨u, hu⟩ : W₂) : V) (e ⟨u, hu⟩).2
    · exact LinearEquiv.apply_symm_apply g.toLinearEquiv x
  have hW : Submodule.map (g.toLinearEquiv : V →ₗ[k] V) (orthoCompl Q W₁) =
      orthoCompl Q W₂ := le_antisymm hmap_le hmap_ge
  rw [← hW]
  exact ⟨
    { toLinearEquiv :=
        LinearEquiv.submoduleMap g.toLinearEquiv (orthoCompl Q W₁)
      map_app' := by
        intro m
        rw [restrict_apply, restrict_apply]
        exact QuadraticMap.IsometryEquiv.map_app g (m : V) }⟩

end Pptc.HasseMinkowski
