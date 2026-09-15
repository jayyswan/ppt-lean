/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.Basic
import Pptc.HasseMinkowski.QuadraticForm.Witt
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.Tactic

/-!
# Chains of orthogonal bases (WiN7 `Chain.lean`: the definitions)

This file holds the sorry-free *definitions* ported from WiN7's `QuadraticForm/Chain.lean`:
`Module.Basis.IsContiguous`, `Module.Basis.Chain`, and the named residual
`Pptc.HasseMinkowski.ChainHypothesis` (WiN7's `chainOfNondegenerate`).  It sits *below*
`HasseInvariantWellDef.lean` so the well-definedness results can take `ChainHypothesis` as their
geometric input without an import cycle (`Chain.lean`, which refutes the diagonal connectivity,
imports this file as well).

## The chain statement

Two `Q`-orthogonal bases of a nondegenerate form on a space of dimension at least `3` are connected
by a chain of `Q`-orthogonal bases in which consecutive members are *contiguous* (share a basis
vector) — Serre, *Cours d'arithmétique*, Ch. IV §1, Theorem 2.  Existence of such chains
(`chainOfNondegenerate`) is **not** in Mathlib 4.33 nor in this project; it is recorded here as the
named `Prop` `ChainHypothesis`, and no axiom is introduced.
-/

open Module QuadraticMap

namespace Module.Basis

/-- Two bases are called contiguous if they have an element in common. -/
def IsContiguous {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (b b' : Basis ι R M) : Prop :=
  ∃ (i j : ι), b i = b' j

variable {k : Type*} [Field k] [Invertible (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Given a quadratic form `Q` and two bases `b, b'` of the vector space `V`, a chain from `b` to
`b'` is a finite sequence of `Q`-orthogonal bases `(b₀, …, b_m)` of `V` such that `b₀ = b`,
`b_m = b'` and `bᵢ` and `bᵢ₊₁` are contiguous for `0 ≤ i < m`.

Upstream writes the contiguity condition with the same index `⟨i, _⟩` on both sides, which makes it
vacuous (`b.IsContiguous b` holds trivially).  We use the intended consecutive condition `bᵢ`,
`bᵢ₊₁`; this is the statement with content and the one whose existence is the missing geometric
input. -/
structure Chain (Q : QuadraticForm k V) (b b' : Basis (Fin (finrank k V)) k V) : Type _ where
  /-- The chain has length `m + 1`. -/
  m : ℕ
  /-- The underlying collection of bases. -/
  basis : Fin (m + 1) → Basis (Fin (finrank k V)) k V
  basis_ortho (i : Fin (m + 1)) : Q.associated.IsOrthoᵢ (basis i)
  basis_zero : basis 0 = b
  basis_m_sub_one : basis ⟨m, lt_add_one m⟩ = b'
  basis_isContiguous {i : ℕ} (hi : i < m) :
    (basis ⟨i, by omega⟩).IsContiguous (basis ⟨i + 1, by omega⟩)

end Module.Basis

namespace Pptc.HasseMinkowski

/-- The genuine missing geometric input (WiN7's `chainOfNondegenerate`, which upstream proves with
two `sorry`s): any two orthogonal bases of a nondegenerate quadratic form on a space of dimension at
least `3` are connected by a chain of orthogonal bases with consecutive contiguity.  This replaces
the *false* diagonal statement `DiagonalConnectivity` (see `Chain.lean`); no axiom asserting it is
introduced here. -/
def ChainHypothesis (k : Type*) [Field k] [Invertible (2 : k)] : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (Q : QuadraticForm k V), Q.Nondegenerate → 3 ≤ Module.finrank k V →
    ∀ (b b' : Basis (Fin (Module.finrank k V)) k V),
      Q.associated.IsOrthoᵢ b → Q.associated.IsOrthoᵢ b' →
      Nonempty (Module.Basis.Chain Q b b')

end Pptc.HasseMinkowski

namespace Module.Basis

variable {k : Type*} [Field k] [Invertible (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {Q : QuadraticForm k V}

/-! ### WiN7 `exists_const` (the first `sorry` of upstream `Chain.lean`) -/

-- Theorem: given two `Q`-orthogonal bases `b`, `b'` of a nondegenerate quadratic form on a space
-- of dimension at least `3`, satisfying the two WiN7 "discriminant-vanishing" relations `h1`, `h2`
-- on their first two diagonal entries, there is `x` with `b'₁ + x • b'₂` non-isotropic and the
-- restriction of `Q` to `span {b₁, b'₁ + x • b'₂}` nondegenerate.
--
-- Note on the hypotheses: `h1`/`h2` are transcribed verbatim from WiN7.  Since `Q` is nondegenerate
-- and `b`/`b'` are orthogonal bases, every basis vector is non-isotropic, so `h1` says
-- `Q b₁ = Q b'₁` and `h2` says `Q b₁ = Q b'₂`.  No infinitude of `k` is needed: the three
-- candidate values `x ∈ {0, 1, -1}` already supply a witness (the discriminant `φ x` cannot vanish
-- at all of them, and `1 + x² ≠ 0` at each).
theorem exists_const (hdim : 3 ≤ finrank k V) (hQ : Q.Nondegenerate)
    {b b' : Basis (Fin (finrank k V)) k V} (hb : Q.associated.IsOrthoᵢ b)
    (hb' : Q.associated.IsOrthoᵢ b')
    (h1 : (Q.associated (b ⟨1, by omega⟩) (b ⟨1, by omega⟩)) *
      (Q.associated (b' ⟨1, by omega⟩) (b' ⟨1, by omega⟩)) -
      (Q.associated (b' ⟨1, by omega⟩) (b' ⟨1, by omega⟩)) ^ 2 = 0)
    (h2 : (Q.associated (b ⟨1, by omega⟩) (b ⟨1, by omega⟩)) *
      (Q.associated (b' ⟨2, by omega⟩) (b' ⟨2, by omega⟩)) -
      (Q.associated (b' ⟨2, by omega⟩) (b' ⟨2, by omega⟩)) ^ 2 = 0) :
    ∃ (x : k), Q (b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩) ≠ 0 ∧
    ((Pptc.HasseMinkowski.restrict Q (Submodule.span k {b ⟨1, by omega⟩,
      b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩}))).Nondegenerate := by
  classical
  set a : k := Q.associated (b ⟨1, by omega⟩) (b ⟨1, by omega⟩) with ha
  set c1 : k := Q.associated (b' ⟨1, by omega⟩) (b' ⟨1, by omega⟩) with hc1
  set c2 : k := Q.associated (b' ⟨2, by omega⟩) (b' ⟨2, by omega⟩) with hc2
  set p : k := Q.associated (b ⟨1, by omega⟩) (b' ⟨1, by omega⟩) with hp
  set q : k := Q.associated (b ⟨1, by omega⟩) (b' ⟨2, by omega⟩) with hq
  have hsep : Q.associated.SeparatingLeft :=
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).mpr hQ).1
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact LinearMap.IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft hb hsep ⟨1, by omega⟩
  have hc10 : c1 ≠ 0 := by
    rw [hc1]
    exact LinearMap.IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft hb' hsep ⟨1, by omega⟩
  have hc20 : c2 ≠ 0 := by
    rw [hc2]
    exact LinearMap.IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft hb' hsep ⟨2, by omega⟩
  have h2ne : (2 : k) ≠ 0 := (isUnit_of_invertible (2 : k)).ne_zero
  have hc1a : a = c1 := by
    have h : c1 * (a - c1) = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc10)
  have hc2a : a = c2 := by
    have h : c2 * (a - c2) = 0 := by linear_combination h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc20)
  have hdisj : a * c1 - p ^ 2 ≠ 0 ∨ a * (c1 + c2) - (p + q) ^ 2 ≠ 0 ∨
      a * (c1 + c2) - (p - q) ^ 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1e, hme⟩ := hcon
    have hp2 : p ^ 2 = a * c1 := by linear_combination -h0
    have hpq : p * q = 0 := by
      have hsub : (p + q) ^ 2 - (p - q) ^ 2 = 0 := by
        have hpp : (p + q) ^ 2 = a * (c1 + c2) := by linear_combination -h1e
        have hmm : (p - q) ^ 2 = a * (c1 + c2) := by linear_combination -hme
        rw [hpp, hmm, sub_self]
      have hkey : (4 : k) * (p * q) = 0 := by
        have h4eq : (p + q) ^ 2 - (p - q) ^ 2 = 4 * (p * q) := by ring
        rw [h4eq] at hsub
        exact hsub
      have h4 : (4 : k) ≠ 0 := by
        have : (4 : k) = 2 * 2 := by norm_num
        rw [this]
        exact mul_ne_zero h2ne h2ne
      exact (mul_eq_zero.mp hkey).resolve_left h4
    have hq2 : q ^ 2 = a * c2 := by
      have haeq : a * (c1 + c2) = (p + q) ^ 2 := by linear_combination h1e
      have hppq : (p + q) ^ 2 = p ^ 2 + q ^ 2 := by
        have : (p + q) ^ 2 = p ^ 2 + 2 * (p * q) + q ^ 2 := by ring
        rw [this, hpq, mul_zero, add_zero]
      rw [hppq, hp2] at haeq
      linear_combination -haeq
    have hp0 : p ≠ 0 := by
      intro hpzero
      have hz : p ^ 2 = 0 := by rw [hpzero]; ring
      rw [hp2] at hz
      exact (mul_ne_zero ha0 hc10) hz
    have hq0 : q ≠ 0 := by
      intro hqzero
      have hz : q ^ 2 = 0 := by rw [hqzero]; ring
      rw [hq2] at hz
      exact (mul_ne_zero ha0 hc20) hz
    exact (mul_ne_zero hp0 hq0) hpq
  have key : ∀ x : k, c1 + x ^ 2 * c2 ≠ 0 →
      a * (c1 + x ^ 2 * c2) - (p + x * q) ^ 2 ≠ 0 →
      Q (b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩) ≠ 0 ∧
      (Pptc.HasseMinkowski.restrict Q (Submodule.span k {b ⟨1, by omega⟩,
        b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩})).Nondegenerate := by
    intro x hQzx hdet
    set z : V := b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩ with hz
    have hb'12 : Q.associated (b' ⟨1, by omega⟩) (b' ⟨2, by omega⟩) = 0 :=
      LinearMap.isOrthoᵢ_def.mp hb' ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp)
    have horth : Q.associated (b' ⟨1, by omega⟩) (x • b' ⟨2, by omega⟩) = 0 := by
      rw [map_smul, hb'12, smul_zero]
    have hQz : Q z = c1 + x ^ 2 * c2 := by
      rw [hz, Pptc.HasseMinkowski.map_add_eq_associated, horth, mul_zero, add_zero,
        QuadraticMap.map_smul]
      simp only [smul_eq_mul]
      rw [← Pptc.HasseMinkowski.associated_self_eq Q (b' ⟨1, by omega⟩),
        ← Pptc.HasseMinkowski.associated_self_eq Q (b' ⟨2, by omega⟩), ← hc1, ← hc2]
      ring
    constructor
    · rw [hQz]; exact hQzx
    · set W : Submodule k V := Submodule.span k {b ⟨1, by omega⟩, z} with hW
      have hdim' : finrank k V ≤ finrank k W +
          finrank k (Pptc.HasseMinkowski.orthoCompl Q W) :=
        le_of_eq (Pptc.HasseMinkowski.finrank_add_finrank_orthoCompl Q hQ W).symm
      rw [Pptc.HasseMinkowski.restrict_nondegenerate_iff_isCompl_orthoCompl Q W]
      rw [Submodule.isCompl_iff_disjoint W (Pptc.HasseMinkowski.orthoCompl Q W) hdim']
      rw [Submodule.disjoint_def]
      intro v hvW hvWperp
      rw [Pptc.HasseMinkowski.mem_orthoCompl] at hvWperp
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp (hW ▸ hvW)
      have hb1mem : b ⟨1, by omega⟩ ∈ W := by
        rw [hW]; exact Submodule.subset_span (by simp)
      have hzmem : z ∈ W := by
        rw [hW]; exact Submodule.subset_span (by simp)
      have e1 : Q.associated v (b ⟨1, by omega⟩) = 0 := hvWperp _ hb1mem
      have e2 : Q.associated v z = 0 := hvWperp _ hzmem
      have hBbz : Q.associated (b ⟨1, by omega⟩) z = p + x * q := by
        rw [hz, map_add, map_smul, ← hp, ← hq, smul_eq_mul]
      have hBzb1 : Q.associated z (b ⟨1, by omega⟩) = p + x * q := by
        rw [hz, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
          QuadraticMap.associated_isSymm k Q (b' ⟨1, by omega⟩) (b ⟨1, by omega⟩),
          QuadraticMap.associated_isSymm k Q (b' ⟨2, by omega⟩) (b ⟨1, by omega⟩),
          ← hp, ← hq, smul_eq_mul]
      have hBzz : Q.associated z z = c1 + x ^ 2 * c2 :=
        (Pptc.HasseMinkowski.associated_self_eq Q z).trans hQz
      have e1' : α * a + β * (p + x * q) = 0 := by
        have h := e1
        rw [← hαβ] at h
        simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply] at h
        rw [← ha, hBzb1, smul_eq_mul, smul_eq_mul] at h
        exact h
      have e2' : α * (p + x * q) + β * (c1 + x ^ 2 * c2) = 0 := by
        have h := e2
        rw [← hαβ] at h
        simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply] at h
        rw [hBbz, hBzz, smul_eq_mul, smul_eq_mul] at h
        exact h
      have hα : α = 0 := by
        have hΔ : α * (a * (c1 + x ^ 2 * c2) - (p + x * q) ^ 2) = 0 := by
          linear_combination (c1 + x ^ 2 * c2) * e1' - (p + x * q) * e2'
        exact (mul_eq_zero.mp hΔ).resolve_right hdet
      have hβ : β = 0 := by
        have hΔ : β * (a * (c1 + x ^ 2 * c2) - (p + x * q) ^ 2) = 0 := by
          linear_combination a * e2' - (p + x * q) * e1'
        exact (mul_eq_zero.mp hΔ).resolve_right hdet
      rw [← hαβ, hα, hβ]
      simp
  rcases hdisj with hd0 | hd1 | hdm
  · exact ⟨0, key 0 (by simpa using hc10) (by simpa using hd0)⟩
  · have h1z : c1 + 1 ^ 2 * c2 ≠ 0 := by
      have h2a : c1 + 1 ^ 2 * c2 = 2 * a := by rw [← hc1a, ← hc2a]; ring
      rw [h2a]; exact mul_ne_zero h2ne ha0
    exact ⟨1, key 1 h1z (by simpa using hd1)⟩
  · have hmz : c1 + (-1) ^ 2 * c2 ≠ 0 := by
      have h2a : c1 + (-1) ^ 2 * c2 = 2 * a := by rw [← hc1a, ← hc2a]; ring
      rw [h2a]; exact mul_ne_zero h2ne ha0
    exact ⟨-1, key (-1) hmz (by simpa [sub_eq_add_neg] using hdm)⟩

end Module.Basis
