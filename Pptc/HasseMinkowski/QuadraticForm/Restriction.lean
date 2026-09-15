/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Projection

/-!
# Orthogonal complements and restrictions of quadratic forms

> **FROZEN (Plan-v3 §0.2).** Off the v3 route: correct as far as it goes, but do not edit,
> extend, import, or "fix" this file. The v3 development needs neither orthogonal
> complements nor restriction of quadratic forms.

Mathlib 4.33 provides the orthogonal complement of a *bilinear* form
(`LinearMap.BilinForm.orthogonal`) together with the whole dimension theory around it
(`finrank_orthogonal`, `orthogonal_orthogonal`, `isCompl_orthogonal_*`).  It also has
`QuadraticMap.restrict`, but there is no packaging of these for a quadratic form `Q`
through its associated bilinear form `Q.associated`, and no API turning a restriction of `Q`
into a statement about the restriction of `Q.associated`.

This file supplies that layer, used downstream by the Witt-cancellation development
(`Pptc/HasseMinkowski/BasisChain.lean`, `Pptc/HasseMinkowski/HasseInvariantWellDef.lean`):

* `orthoCompl Q W`: the orthogonal complement of a submodule `W` with respect to
  `Q.associated`;
* `restrict Q W`: the restriction of `Q` to `W`, as a quadratic form on `W`;
* the bridge `orthoCompl Q W = Q.associated.orthogonal W`, which lets all of Mathlib's
  bilinear orthogonality theory be reused;
* for nondegenerate `Q`: `finrank W + finrank Wᗮ = finrank V`,
  `orthoCompl Q (orthoCompl Q W) = W`, and the correct form of the orthogonal
  decomposition (`IsCompl` holds exactly when `restrict Q W` is nondegenerate — the
  weaker hypothesis is genuinely needed, since an isotropic line in a hyperbolic plane is
  a nondegenerate form's own orthogonal complement).

## Main definitions

* `Pptc.HasseMinkowski.orthoCompl`
* `Pptc.HasseMinkowski.restrict`

## Main results

* `mem_orthoCompl`, `le_orthoCompl`, `le_orthoCompl_orthoCompl`
* `restrict_apply`, `associated_restrict`, `associated_restrict_eq`
* `finrank_add_finrank_orthoCompl`, `orthoCompl_orthoCompl_eq_of_nondegenerate`
* `restrict_nondegenerate_iff_isCompl_orthoCompl`
* `restrict_orthoCompl_span_singleton_nondegenerate`
-/

open Module QuadraticMap

namespace Pptc.HasseMinkowski

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]

/-! ### The orthogonal complement -/

/-- The orthogonal complement of `W` with respect to the bilinear form `Q.associated`
associated to a quadratic form `Q`: the set of `v` orthogonal to every `w ∈ W`. -/
def orthoCompl (Q : QuadraticForm k V) (W : Submodule k V) : Submodule k V where
  carrier := {v | ∀ w ∈ W, Q.associated v w = 0}
  zero_mem' := by
    intro w _
    simp
  add_mem' := by
    intro x y hx hy w hw
    rw [map_add, LinearMap.add_apply, hx w hw, hy w hw, add_zero]
  smul_mem' := by
    intro a x hx w hw
    rw [map_smul, LinearMap.smul_apply, hx w hw, smul_zero]

-- Theorem: membership in `orthoCompl Q W` is being orthogonal to every element of `W`.
@[simp]
theorem mem_orthoCompl {Q : QuadraticForm k V} {W : Submodule k V} {v : V} :
    v ∈ orthoCompl Q W ↔ ∀ w ∈ W, Q.associated v w = 0 :=
  Iff.rfl

/-- The quadratic orthogonal complement is the bilinear one of the associated form. -/
theorem orthoCompl_eq_orthogonal (Q : QuadraticForm k V) (W : Submodule k V) :
    orthoCompl Q W = LinearMap.BilinForm.orthogonal Q.associated W := by
  ext v
  rw [mem_orthoCompl, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h w hw
    rw [QuadraticMap.associated_isSymm k Q w v]
    exact h w hw
  · intro h w hw
    rw [QuadraticMap.associated_isSymm k Q v w]
    exact h w hw

/-- The associated bilinear form of a quadratic form is reflexive (in characteristic `≠ 2`). -/
theorem isRefl_associated (Q : QuadraticForm k V) : (Q.associated).IsRefl :=
  (QuadraticForm.associated_isSymm (S := k) Q).isRefl

-- Theorem: the orthogonal complement reverses inclusions.
theorem le_orthoCompl {Q : QuadraticForm k V} {W₁ W₂ : Submodule k V} (h : W₁ ≤ W₂) :
    orthoCompl Q W₂ ≤ orthoCompl Q W₁ :=
  fun _ hv _ hw => hv _ (h hw)

-- Theorem: `W` is contained in its double orthogonal complement.
theorem le_orthoCompl_orthoCompl (Q : QuadraticForm k V) (W : Submodule k V) :
    W ≤ orthoCompl Q (orthoCompl Q W) := by
  rw [orthoCompl_eq_orthogonal, orthoCompl_eq_orthogonal]
  exact LinearMap.BilinForm.le_orthogonal_orthogonal (isRefl_associated Q)

-- Theorem: the orthogonal complement of the zero submodule is the whole space.
theorem orthoCompl_bot (Q : QuadraticForm k V) : orthoCompl Q (⊥ : Submodule k V) = ⊤ := by
  rw [orthoCompl_eq_orthogonal, LinearMap.BilinForm.orthogonal_bot]

/-! ### The restriction of a quadratic form to a submodule -/

/-- The restriction of `Q` to a submodule `W`, as a quadratic form on `W`. -/
def restrict (Q : QuadraticForm k V) (W : Submodule k V) : QuadraticForm k W :=
  Q.comp W.subtype

omit [Invertible (2 : k)] in
-- Theorem: the restricted form takes the same values as `Q`.
@[simp]
theorem restrict_apply (Q : QuadraticForm k V) (W : Submodule k V) (v : W) :
    restrict Q W v = Q v :=
  rfl

-- Theorem: the associated form of the restriction is the restriction of the associated form.
theorem associated_restrict (Q : QuadraticForm k V) (W : Submodule k V) (v w : W) :
    (restrict Q W).associated v w = Q.associated v w := by
  simp only [restrict, QuadraticMap.associated_comp (S := k), LinearMap.compl₁₂_apply]
  rfl

-- Theorem: the associated bilinear forms of `restrict Q W` and `Q` agree on `W`.
theorem associated_restrict_eq (Q : QuadraticForm k V) (W : Submodule k V) :
    (restrict Q W).associated = LinearMap.BilinForm.restrict Q.associated W := by
  ext x y
  rw [associated_restrict, LinearMap.BilinForm.restrict_apply]
  rfl

-- Theorem: `restrict Q W` is nondegenerate iff `Q.associated` restricted to `W` is.
theorem nondegenerate_restrict_iff (Q : QuadraticForm k V) (W : Submodule k V) :
    (restrict Q W).Nondegenerate ↔
      (LinearMap.BilinForm.restrict Q.associated W).Nondegenerate := by
  rw [← QuadraticMap.nondegenerate_associated_iff (Q := restrict Q W), associated_restrict_eq]

/-! ### The orthogonal decomposition for nondegenerate forms -/

section FiniteDimensional

variable [FiniteDimensional k V]

-- Theorem: for nondegenerate `Q`, the orthogonal complement has complementary dimension.
theorem finrank_add_finrank_orthoCompl (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (W : Submodule k V) :
    finrank k W + finrank k (orthoCompl Q W) = finrank k V := by
  rw [orthoCompl_eq_orthogonal]
  have hB : (Q.associated).Nondegenerate :=
    (QuadraticMap.nondegenerate_associated_iff (Q := Q)).mpr hQ
  have h := LinearMap.BilinForm.finrank_orthogonal (B := Q.associated) hB W
  have hle : finrank k W ≤ finrank k V := Submodule.finrank_le W
  omega

-- Theorem: for nondegenerate `Q`, `finrank Wᗮ = finrank V - finrank W`.
theorem finrank_orthoCompl (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (W : Submodule k V) :
    finrank k (orthoCompl Q W) = finrank k V - finrank k W := by
  rw [orthoCompl_eq_orthogonal]
  exact LinearMap.BilinForm.finrank_orthogonal
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).mpr hQ) W

-- Theorem: for nondegenerate `Q`, taking the orthogonal complement twice is the identity.
theorem orthoCompl_orthoCompl_eq_of_nondegenerate (Q : QuadraticForm k V)
    (hQ : Q.Nondegenerate) (W : Submodule k V) :
    orthoCompl Q (orthoCompl Q W) = W := by
  rw [orthoCompl_eq_orthogonal, orthoCompl_eq_orthogonal]
  exact LinearMap.BilinForm.orthogonal_orthogonal
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).mpr hQ) (isRefl_associated Q) W

-- Theorem: `W` splits off its orthogonal complement iff `Q|_W` is nondegenerate.
theorem restrict_nondegenerate_iff_isCompl_orthoCompl (Q : QuadraticForm k V)
    (W : Submodule k V) :
    (restrict Q W).Nondegenerate ↔ IsCompl W (orthoCompl Q W) := by
  rw [nondegenerate_restrict_iff, orthoCompl_eq_orthogonal]
  exact LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal (isRefl_associated Q)

-- Theorem: a nondegenerate restriction to `W` makes `W` and `Wᗮ` complementary.
theorem isCompl_orthoCompl_of_restrict_nondegenerate (Q : QuadraticForm k V)
    (W : Submodule k V) (h : (restrict Q W).Nondegenerate) :
    IsCompl W (orthoCompl Q W) :=
  (restrict_nondegenerate_iff_isCompl_orthoCompl Q W).mp h

end FiniteDimensional

/-! ### Splitting off a non-isotropic vector -/

-- Theorem: the span of a vector with `Q.associated v v ≠ 0` is complemented by its orthocompl.
theorem isCompl_span_singleton_orthoCompl (Q : QuadraticForm k V) {v : V}
    (hv : Q.associated v v ≠ 0) :
    IsCompl (k ∙ v) (orthoCompl Q (k ∙ v)) := by
  rw [orthoCompl_eq_orthogonal]
  exact LinearMap.BilinForm.isCompl_span_singleton_orthogonal (B := Q.associated) hv

-- Theorem: `Q.associated v v = Q v` in characteristic `≠ 2`.
theorem associated_self_eq (Q : QuadraticForm k V) (v : V) :
    Q.associated v v = Q v :=
  QuadraticMap.associated_eq_self_apply (S := k) Q v

-- Theorem: the orthogonal complement of the span of a non-isotropic vector is nondegenerate.
theorem restrict_orthoCompl_span_singleton_nondegenerate (Q : QuadraticForm k V)
    (hQ : Q.Nondegenerate) {v : V} (hv : Q.associated v v ≠ 0) :
    (restrict Q (orthoCompl Q (k ∙ v))).Nondegenerate := by
  rw [nondegenerate_restrict_iff, orthoCompl_eq_orthogonal]
  exact LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton Q.associated
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).mpr hQ) (isRefl_associated Q) hv

-- Theorem: same as above, phrased with `Q v ≠ 0`.
theorem restrict_orthoCompl_span_singleton_nondegenerate' (Q : QuadraticForm k V)
    (hQ : Q.Nondegenerate) {v : V} (hv : Q v ≠ 0) :
    (restrict Q (orthoCompl Q (k ∙ v))).Nondegenerate :=
  restrict_orthoCompl_span_singleton_nondegenerate Q hQ
    (fun h => hv ((associated_self_eq Q v).symm.trans h))

/-! ### Orthogonal splitting isometry -/

/-- If `W` is complemented by its orthogonal complement, then `Q` is isometric to the
orthogonal (external) sum `Q|_W ⊥ Q|_{Wᗮ}` of the two restrictions, via addition. -/
noncomputable def isometryEquivProdOfIsCompl (Q : QuadraticForm k V) {W : Submodule k V}
    (h : IsCompl W (orthoCompl Q W)) :
    QuadraticMap.IsometryEquiv ((restrict Q W).prod (restrict Q (orthoCompl Q W))) Q where
  toLinearEquiv := Submodule.prodEquivOfIsCompl W (orthoCompl Q W) h
  map_app' := by
    intro m
    have horth : Q.associated (m.1 : V) (m.2 : V) = 0 :=
      (QuadraticMap.associated_isSymm k Q (m.1 : V) (m.2 : V)).trans
        ((mem_orthoCompl (Q := Q) (W := W)).mp m.2.2 m.1 m.1.2)
    change Q ((m.1 : V) + (m.2 : V)) =
      ((restrict Q W).prod (restrict Q (orthoCompl Q W))) m
    rw [QuadraticMap.prod_apply, restrict_apply, restrict_apply]
    exact (QuadraticMap.associated_isOrtho (Q := Q)).mp horth

-- Theorem: if `W` and its orthogonal complement are complementary, then `Q` is isometric
-- to the orthogonal (external) sum `Q|_W ⊥ Q|_{Wᗮ}` of the two restrictions.
theorem isometryEquiv_prod_of_isCompl (Q : QuadraticForm k V) {W : Submodule k V}
    (h : IsCompl W (orthoCompl Q W)) :
    Nonempty (QuadraticMap.IsometryEquiv
      ((restrict Q W).prod (restrict Q (orthoCompl Q W))) Q) :=
  ⟨isometryEquivProdOfIsCompl Q h⟩

section FiniteDimensional

variable [FiniteDimensional k V]

-- Theorem: version of the splitting isometry with the nondegeneracy hypothesis on `Q|_W`.
theorem isometryEquiv_prod_of_nondegenerate_restrict (Q : QuadraticForm k V)
    (W : Submodule k V) (h : (restrict Q W).Nondegenerate) :
    Nonempty (QuadraticMap.IsometryEquiv
      ((restrict Q W).prod (restrict Q (orthoCompl Q W))) Q) :=
  isometryEquiv_prod_of_isCompl Q ((restrict_nondegenerate_iff_isCompl_orthoCompl Q W).mp h)

-- Theorem: an `IsCompl` orthogonal decomposition has complementary dimensions.
theorem finrank_eq_add_finrank_orthoCompl_of_isCompl (Q : QuadraticForm k V)
    {W : Submodule k V} (h : IsCompl W (orthoCompl Q W)) :
    finrank k V = finrank k W + finrank k (orthoCompl Q W) := by
  have e := Submodule.prodEquivOfIsCompl W (orthoCompl Q W) h
  rw [← e.finrank_eq, Module.finrank_prod]

end FiniteDimensional

end Pptc.HasseMinkowski
