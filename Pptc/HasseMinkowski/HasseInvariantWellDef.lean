/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.HasseInvariant
import Pptc.HasseMinkowski.RankCriteria
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Well-definedness of the Hasse–Minkowski invariant

WiN7's `QuadraticForm/HasseMinkowskiInvariant.lean` states that the Hasse–Minkowski invariant
`ε(w) = ∏_{i<j} (wᵢ, wⱼ)_k` of a diagonal form depends only on the isometry class of the form
(`hasseMinkowskiInvAux.eq_of_equivalent`), and deduces well-definedness of `hasseMinkowskiInv`
together with the two forms of the statement used downstream
(`hasseMinkowskiInv.eq_of_equivalent_weightedSumSquares`, `hasseMinkowskiInv.eq_of_equivalent`).

## Status of the upstream proof

In WiN7 *all four* of these declarations are `sorry`.  In particular `eq_of_equivalent` is not
available to port: it is the algebraically deep statement (Serre, *Cours d'arithmétique*, Ch. IV;
Hasse invariant = second Stiefel–Whitney class), whose standard proof goes through Witt's
cancellation theorem / the contiguity chain of orthogonal bases (`QuadraticForm/Chain.lean`),
neither of which is in Mathlib 4.33 nor in this project.

Accordingly, this file proves:

* `LinearMap.separatingLeft_of_equivalent` unconditionally (pure linear algebra);
* `hasseMinkowskiInvAux.eq_of_equivalent` under `[HasBilinHilbertSym k]`, `[Invertible (2:k)]`
  and one explicit *geometric* hypothesis `hconn` — the connectivity of any two equivalent
  diagonalizations by elementary diagonal moves (reindexings, and a shared rank-one summand with
  equivalent tails);
* the two `hasseMinkowskiInv` statements from `eq_of_equivalent`.

## WARNING: `hconn` is FALSE

`Chain.lean` proves `¬ DiagonalConnectivity ℝ` (`diagonalConnectivity_false`): the diagonal move
relation `hconn` is refuted already at rank one over `ℝ` (`![1] ~ ![4]` are equivalent, but no
diagonal `Step` connects them, since `Step 1` relates only equal tuples).  Consequently the three
theorems below are **vacuous as stated**: well-definedness of the invariant is true, but a general
isometry mixes coordinates, so no diagonal-only relation can supply it.

The correct geometric input is the *basis-level* connectivity
`ChainHypothesis` (WiN7's `chainOfNondegenerate`), now defined in
`Pptc/HasseMinkowski/BasisChain.lean`.  Discharging the reduction from
`ChainHypothesis`, however, requires the orthogonal-complement /
Witt-cancellation machinery, which is **not** in Mathlib 4.33 (no
`orthoCompl`, no `QuadraticForm.restrict`), the same reason upstream leaves
`eq_of_equivalent` as `sorry`.  It is therefore not carried out here; a future
session can restate these results with `ChainHypothesis` once it exists.

## Main results

* `LinearMap.separatingLeft_of_equivalent`
* `hasseMinkowskiInvAux.eq_of_equivalent`
* `hasseMinkowskiInv.eq_of_equivalent_weightedSumSquares`, `hasseMinkowskiInv.eq_of_equivalent`
-/

open Module QuadraticMap

namespace Pptc.HasseMinkowski

variable {k : Type*} [Field k]

/-! ### Nondegeneracy transports along an isometry -/

-- Theorem: `LinearMap.SeparatingLeft` of the associated form transports along an equivalence.
theorem LinearMap.separatingLeft_of_equivalent {R M M' N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M'] [AddCommGroup N] [Module R N]
    [Invertible (2 : R)] {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N} (h : Q.Equivalent Q')
    (hQ : LinearMap.SeparatingLeft Q.associated) :
    LinearMap.SeparatingLeft Q'.associated := by
  have hsymm : ∀ x y : M, Q.associated x y = Q.associated y x := by
    intro x y
    rw [QuadraticMap.associated_apply (S := R), QuadraticMap.associated_apply (S := R)]
    congr 1
    abel
  have hrefl : (Q.associated).IsRefl := fun x y h => by rwa [hsymm x y] at h
  have hQn : Q.Nondegenerate :=
    (QuadraticMap.nondegenerate_associated_iff (Q := Q)).mp
      ((LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr hQ)
  have hQ'n : Q'.Nondegenerate := QuadraticMap.Equivalent.nondegenerate h hQn
  have hsymm' : ∀ x y : M', Q'.associated x y = Q'.associated y x := by
    intro x y
    rw [QuadraticMap.associated_apply (S := R), QuadraticMap.associated_apply (S := R)]
    congr 1
    abel
  have hrefl' : (Q'.associated).IsRefl := fun x y h => by rwa [hsymm' x y] at h
  exact (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl').mp
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q')).mpr hQ'n)

/-! ### The diagonal form attached to a tuple of unit weights -/

/-- The diagonal form `w₀ X₀² + ⋯ + w_{n-1} X_{n-1}²` attached to `w : Fin n → kˣ`. -/
noncomputable abbrev wss {n : ℕ} (w : Fin n → kˣ) : QuadraticForm k (Fin n → k) :=
  weightedSumSquares k w

/-! ### Reindexing the weights does not change the invariant

`hasseMinkowskiInvAux w` is a product over the unordered pairs `{i, j}`.  Reindexing by
`e : Fin n ≃ Fin n` only permutes these pairs, so the invariant is unchanged.  The relevant
bijection sends `p` with `p.1 < p.2` to the *ordered* pair formed by `e p.1`, `e p.2`; the value
is unchanged because the Hilbert symbol is symmetric. -/

section Reindex

variable {n : ℕ}

/-- The ordered pair `(min a b, max a b)`, written as an `if` to keep the case analysis local. -/
private def orderedPair (a b : Fin n) : Fin n × Fin n :=
  if a < b then (a, b) else (b, a)

private theorem orderedPair_lt (a b : Fin n) (h : a ≠ b) :
    (orderedPair a b).1 < (orderedPair a b).2 := by
  unfold orderedPair
  split_ifs with hab
  · exact hab
  · exact lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm h)

private theorem eq_or_swap_of_orderedPair_eq {a b c d : Fin n}
    (h : orderedPair a b = orderedPair c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold orderedPair at h
  split_ifs at h with h1 h2
  · simp only [Prod.mk.injEq] at h
    exact Or.inl h
  · simp only [Prod.mk.injEq] at h
    exact Or.inr h
  · simp only [Prod.mk.injEq] at h
    exact Or.inr ⟨h.2, h.1⟩
  · simp only [Prod.mk.injEq] at h
    exact Or.inl ⟨h.2, h.1⟩

private theorem hilbertSym_orderedPair (w : Fin n → kˣ) (a b : Fin n) :
    hilbertSym (w a : k) (w b) =
      hilbertSym (w (orderedPair a b).1 : k) (w (orderedPair a b).2 : k) := by
  unfold orderedPair
  split_ifs with hab
  · rfl
  · exact hilbertSym_comm _ _

-- Theorem: reindexing the weights along an equivalence does not change `ε`.
theorem hasseMinkowskiInvAux_comp_equiv (w : Fin n → kˣ) (e : Fin n ≃ Fin n) :
    hasseMinkowskiInvAux (w ∘ e) = hasseMinkowskiInvAux w := by
  rw [hasseMinkowskiInvAux_def, hasseMinkowskiInvAux_def]
  refine Finset.prod_bij
    (fun p (_ : p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)) =>
      orderedPair (e p.1) (e p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact orderedPair_lt _ _ (fun h => (ne_of_lt hp) (e.injective h))
  · intro p₁ hp₁ p₂ hp₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    rcases eq_or_swap_of_orderedPair_eq h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (e.injective h1) (e.injective h2)
    · exfalso
      have h1' : p₁.1 = p₂.2 := e.injective h1
      have h2' : p₁.2 = p₂.1 := e.injective h2
      rw [h1', h2'] at hp₁
      omega
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    by_cases h : e.symm b.1 < e.symm b.2
    · refine ⟨(e.symm b.1, e.symm b.2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h
      · simp only [Equiv.apply_symm_apply]
        unfold orderedPair
        rw [if_pos hb]
    · have hne : e.symm b.1 ≠ e.symm b.2 := fun hh => (ne_of_lt hb) (e.symm.injective hh)
      have hlt : e.symm b.2 < e.symm b.1 :=
        lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
      refine ⟨(e.symm b.2, e.symm b.1), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlt
      · simp only [Equiv.apply_symm_apply]
        unfold orderedPair
        rw [if_neg (not_lt.mpr hb.le)]
  · intro p _
    exact hilbertSym_orderedPair w (e p.1) (e p.2)

end Reindex

/-! ### The discriminant argument

Equivalent diagonal forms have discriminants differing by a square (`QuadraticForm.discr_comp`).
Since `(a, s²) = 1`, the Hilbert symbol of a fixed weight against the product of the weights is
an invariant. -/

section Main

variable [Invertible (2 : k)] [HasBilinHilbertSym k]

-- Theorem: equivalent diagonal forms give the same Hilbert symbol against the product of the
-- weights (the discriminant), for any fixed weight `a`.
theorem hilbertSym_prod_eq_of_equivalent {n : ℕ} (a : kˣ) (w w' : Fin n → kˣ)
    (h : (weightedSumSquares k w).Equivalent (weightedSumSquares k w')) :
    hilbertSym (a : k) (∏ i, (w i : k)) = hilbertSym (a : k) (∏ i, (w' i : k)) := by
  obtain ⟨e⟩ := h
  let b := Pi.basisFun k (Fin n)
  let M := LinearMap.toMatrix b b e.toLinearEquiv
  have hcomp : (weightedSumSquares k w').comp e.toLinearEquiv = weightedSumSquares k w := by
    ext x
    rw [QuadraticMap.comp_apply]
    exact e.map_app x
  have hdisc := QuadraticForm.discr_comp (b := b) (b' := b)
      (Q := weightedSumSquares k w') (f := e.toLinearEquiv)
  rw [hcomp, weightedSumSquares_discr, weightedSumSquares_discr] at hdisc
  simp only [Units.smul_def, smul_eq_mul, mul_one] at hdisc
  have hw_ne : (∏ i, (w i : k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero (w i)
  have hw'_ne : (∏ i, (w' i : k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero (w' i)
  have ht_ne : M.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at hdisc
    exact hw_ne hdisc
  rw [hdisc, HasBilinHilbertSym.mul_right_eq]
  have ht1 : hilbertSym (a : k) (M.det * M.det) = 1 := by
    rw [HasBilinHilbertSym.mul_right_eq]
    rcases hilbertSym_eq_one_or_neg_one_of_ne_zero (Units.ne_zero a) ht_ne with hh | hh <;>
      rw [hh] <;> norm_num
  rw [ht1, one_mul]

/-! ### Connectivity of diagonalizations

The one genuinely geometric input (WiN7's `Chain.lean`).  Two equivalent diagonalizations are
connected by a chain of elementary moves: reindex the weights, or split off a common rank-one
summand whose tails are equivalent. -/

/-- One elementary move between weight tuples of the same rank. -/
def Step : (n : ℕ) → (Fin n → kˣ) → (Fin n → kˣ) → Prop
  | 0, _, _ => True
  | n + 1, u, v =>
      (∃ e : Fin (n + 1) ≃ Fin (n + 1), v = u ∘ e) ∨
        (∃ (a : kˣ) (w w' : Fin n → kˣ),
          u = Fin.cons a w ∧ v = Fin.cons a w' ∧
            (weightedSumSquares k w).Equivalent (weightedSumSquares k w'))

-- Theorem: a common rank-one summand can be cancelled, at the level of the invariant.
private theorem hasseMinkowskiInvAux_cons_congr {m : ℕ} (a : kˣ) (w w' : Fin m → kˣ)
    (h : (weightedSumSquares k w).Equivalent (weightedSumSquares k w'))
    (hw : hasseMinkowskiInvAux w = hasseMinkowskiInvAux w') :
    hasseMinkowskiInvAux (Fin.cons a w) = hasseMinkowskiInvAux (Fin.cons a w') := by
  rw [hasseMinkowskiInvAux_prod_rank_one, hasseMinkowskiInvAux_prod_rank_one, hw]
  congr 1
  exact hilbertSym_prod_eq_of_equivalent a w w' h

-- Theorem: well-definedness of `hasseMinkowskiInvAux`, reduced to the connectivity hypothesis.
theorem hasseMinkowskiInvAux.eq_of_equivalent
    (hconn : ∀ {n : ℕ} (w w' : Fin n → kˣ),
      (weightedSumSquares k w).Equivalent (weightedSumSquares k w') →
        Relation.ReflTransGen (Step n) w w') :
    ∀ {n : ℕ} (w w' : Fin n → kˣ),
      (weightedSumSquares k w).Equivalent (weightedSumSquares k w') →
        hasseMinkowskiInvAux w = hasseMinkowskiInvAux w' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      intro w w' _
      rw [hasseMinkowskiInvAux_zero w, hasseMinkowskiInvAux_zero w']
    | m + 1 =>
      intro w w' h
      have hchain := hconn w w' h
      have hstep : ∀ u v : Fin (m + 1) → kˣ,
          Relation.ReflTransGen (Step (m + 1)) u v →
            hasseMinkowskiInvAux u = hasseMinkowskiInvAux v := by
        intro u v hr
        induction hr with
        | refl => rfl
        | tail hab hbc ihab =>
          refine ihab.trans ?_
          rcases hbc with hperm | hcons
          · obtain ⟨e, rfl⟩ := hperm
            exact (hasseMinkowskiInvAux_comp_equiv _ e).symm
          · obtain ⟨a, w0, w0', rfl, rfl, heq⟩ := hcons
            exact hasseMinkowskiInvAux_cons_congr a w0 w0' heq
              (ih m (Nat.lt_succ_self m) w0 w0' heq)
      exact hstep w w' hchain

-- Theorem: reindexing a weighted sum of squares along an equivalence of index types.
noncomputable def wssCongr {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (w : κ → kˣ) : (weightedSumSquares k w).IsometryEquiv (weightedSumSquares k (w ∘ e)) where
  toLinearEquiv :=
    { toFun := fun x => x ∘ e
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro c x; ext i; simp
      invFun := fun y => y ∘ e.symm
      left_inv := by intro x; ext j; simp
      right_inv := by intro y; ext i; simp }
  map_app' := by
    intro x
    rw [QuadraticMap.weightedSumSquares_apply, QuadraticMap.weightedSumSquares_apply]
    exact Fintype.sum_equiv e (fun i => w (e i) • (x (e i) * x (e i)))
      (fun j => w j • (x j * x j)) (fun _ => rfl)

-- Theorem: `ε` is unchanged by transporting the weights along an equality `Fin m = Fin n`.
omit [Invertible (2 : k)] [HasBilinHilbertSym k] in
theorem hasseMinkowskiInvAux_finCongr {m n : ℕ} (h : m = n) (w : Fin n → kˣ) :
    hasseMinkowskiInvAux (w ∘ finCongr h) = hasseMinkowskiInvAux w := by
  subst h
  simp [finCongr]

-- Theorem: the invariant computed from any diagonalization equals `hasseMinkowskiInv`.
theorem hasseMinkowskiInv_eq_aux_of_equiv
    (hconn : ∀ {n : ℕ} (w w' : Fin n → kˣ),
      (weightedSumSquares k w).Equivalent (weightedSumSquares k w') →
        Relation.ReflTransGen (Step n) w w')
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (Q : QuadraticForm k V) (hQ : LinearMap.SeparatingLeft Q.associated)
    {w : Fin (finrank k V) → kˣ} (hw : Q.Equivalent (weightedSumSquares k w)) :
    hasseMinkowskiInv Q hQ = hasseMinkowskiInvAux w := by
  change hasseMinkowskiInvAux _ = _
  have hspec :=
    (QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose_spec
  refine hasseMinkowskiInvAux.eq_of_equivalent hconn _ w (hspec.symm.trans hw)

-- Theorem: the invariant of `Q` agrees with the invariant of an equivalent diagonal form.
theorem hasseMinkowskiInv.eq_of_equivalent_weightedSumSquares
    (hconn : ∀ {n : ℕ} (w w' : Fin n → kˣ),
      (weightedSumSquares k w).Equivalent (weightedSumSquares k w') →
        Relation.ReflTransGen (Step n) w w')
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} {n : ℕ} {w : Fin n → kˣ}
    (hQ : LinearMap.SeparatingLeft Q.associated)
    (h : Q.Equivalent (weightedSumSquares k w)) :
    hasseMinkowskiInv Q hQ =
      hasseMinkowskiInv (weightedSumSquares k w)
        (LinearMap.separatingLeft_of_equivalent h hQ) := by
  have hV : finrank k V = n := by
    obtain ⟨e⟩ := h
    rw [LinearEquiv.finrank_eq e.toLinearEquiv]
    simp
  have hn : finrank k (Fin n → k) = n := Module.finrank_fin_fun (R := k) (n := n)
  let wV : Fin (finrank k V) → kˣ := w ∘ finCongr hV
  have hwV : Q.Equivalent (weightedSumSquares k wV) :=
    h.trans ⟨wssCongr (finCongr hV) w⟩
  have hwF : (weightedSumSquares k w).Equivalent (weightedSumSquares k (w ∘ finCongr hn)) :=
    ⟨wssCongr (finCongr hn) w⟩
  calc hasseMinkowskiInv Q hQ
      = hasseMinkowskiInvAux wV := hasseMinkowskiInv_eq_aux_of_equiv hconn Q hQ hwV
    _ = hasseMinkowskiInvAux w := hasseMinkowskiInvAux_finCongr hV w
    _ = hasseMinkowskiInvAux (w ∘ finCongr hn) := (hasseMinkowskiInvAux_finCongr hn w).symm
    _ = hasseMinkowskiInv (weightedSumSquares k w)
          (LinearMap.separatingLeft_of_equivalent h hQ) :=
        (hasseMinkowskiInv_eq_aux_of_equiv hconn (weightedSumSquares k w)
          (LinearMap.separatingLeft_of_equivalent h hQ) hwF).symm

-- Theorem: the invariant is well-defined on the equivalence class of `Q`.
theorem hasseMinkowskiInv.eq_of_equivalent
    (hconn : ∀ {n : ℕ} (w w' : Fin n → kˣ),
      (weightedSumSquares k w).Equivalent (weightedSumSquares k w') →
        Relation.ReflTransGen (Step n) w w')
    {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {Q : QuadraticForm k V} {Q' : QuadraticForm k W}
    (hQ : LinearMap.SeparatingLeft Q.associated) (h : Q.Equivalent Q') :
    hasseMinkowskiInv Q hQ =
      hasseMinkowskiInv Q' (LinearMap.separatingLeft_of_equivalent h hQ) := by
  have hVW : finrank k V = finrank k W := by
    obtain ⟨e⟩ := h
    exact LinearEquiv.finrank_eq e.toLinearEquiv
  let w' : Fin (finrank k W) → kˣ :=
    (QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q'
      (LinearMap.separatingLeft_of_equivalent h hQ)).choose
  have hw' : Q'.Equivalent (weightedSumSquares k w') :=
    (QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q'
      (LinearMap.separatingLeft_of_equivalent h hQ)).choose_spec
  let wV : Fin (finrank k V) → kˣ := w' ∘ finCongr hVW
  have hwV : Q.Equivalent (weightedSumSquares k wV) :=
    h.trans (hw'.trans ⟨wssCongr (finCongr hVW) w'⟩)
  calc hasseMinkowskiInv Q hQ
      = hasseMinkowskiInvAux wV := hasseMinkowskiInv_eq_aux_of_equiv hconn Q hQ hwV
    _ = hasseMinkowskiInvAux w' := hasseMinkowskiInvAux_finCongr hVW w'
    _ = hasseMinkowskiInv Q' (LinearMap.separatingLeft_of_equivalent h hQ) :=
        (hasseMinkowskiInv_eq_aux_of_equiv hconn Q'
          (LinearMap.separatingLeft_of_equivalent h hQ) hw').symm

end Main

end Pptc.HasseMinkowski
