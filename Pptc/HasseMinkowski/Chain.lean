/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.HasseInvariantWellDef
import Pptc.HasseMinkowski.BasisChain
import Pptc.HasseMinkowski.HilbertSymbol.Real
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Chains of orthogonal bases, and the failure of the diagonal connectivity hypothesis

> **FROZEN (Plan-v3 §0.2).** Off the v3 route: correct as far as it goes, but do not edit,
> extend, import, or "fix" this file. The v3 development needs no Hasse-invariant
> well-definedness (every form over `ℚ` and its completions diagonalizes).

`HasseInvariantWellDef.lean` reduces the well-definedness of the Hasse–Minkowski invariant to a
single explicit hypothesis `hconn`:

```
hconn : ∀ {n : ℕ} (w w' : Fin n → kˣ),
  (weightedSumSquares k w).Equivalent (weightedSumSquares k w') →
    Relation.ReflTransGen (Step n) w w'
```

where `Step n` is the *diagonal* elementary move: either reindex the weights, or split off a
common rank-one summand `a` and replace the tail by an equivalent tail.

## The hypothesis `hconn` is false

`Step` only ever manipulates the weights *diagonally*.  A general isometry of diagonal forms
mixes coordinates, so the two are not comparable, and no choice of diagonal-only elementary
moves can be complete.  The smallest counterexample is at rank one over `ℝ` (where the instance
`HasBilinHilbertSym ℝ` is available in this project):

* `w = ![1]` and `w' = ![4]` satisfy `weightedSumSquares ℝ w ~ weightedSumSquares ℝ w'`
  (the isometry is `x ↦ x / 2`);
* but at rank one a `Step` can only relate *equal* tuples: the permutation disjunct uses the
  unique equivalence `Fin 1 ≃ Fin 1`, and the cons disjunct forces the single entry to be the
  head `a` in both tuples.  Hence `ReflTransGen (Step 1) w w'` implies `w = w'`, which is false.

This is formalized below as `reflTransGen_step_one_eq` and `diagonalConnectivity_false`.

The rank-one example is the one formalized here (since `HasBilinHilbertSym ℝ` is the instance
available in this project).  Over `ℚ` there is an even stronger obstruction at rank two:
`(1, 1)` and `(2, 1/2)` are equivalent via the rational isometry `(x, y) ↦ ((x+y)/2, x-y)`, but
any `Step`-chain starting at `(1, 1)` keeps *both* coordinates squares (a rank-1 equivalence
`(t) ~ (t')` forces `t'/t` to be a square), whereas `2` is not a square in `ℚ`; so the two are
not connected.  The two examples together show that no diagonal-only elementary relation can be
complete.

## What the genuine residual is

The correct geometric input is WiN7's `Chain.lean` (Serre, *Cours d'arithmétique*, Ch. IV §1,
Theorem 2): two `Q`-orthogonal bases of a nondegenerate form on a space of dimension at least
`3` are connected by a chain of `Q`-orthogonal bases in which consecutive members are
*contiguous* (share a basis vector).  That statement is **not** available in Mathlib 4.33 nor in
this project, and upstream proves it with two `sorry`s (`exists_const` and
`chainOfNondegenerate`).  We port its sorry-free definitions (`IsContiguous`, `Chain`) and
record the missing statement as the named `Prop` `ChainHypothesis`; no axiom is introduced.

This file therefore does *not* discharge `hconn` (which is impossible, being false); it
isolates the exact residual and documents the obstruction.

## Main results

* `Module.Basis.IsContiguous`, `Module.Basis.Chain` — ported WiN7 definitions (sorry-free part).
* `ChainHypothesis` — the genuine missing geometric input, as a named hypothesis.
* `DiagonalConnectivity` — the exact shape of `hconn`.
* `step_one_eq`, `reflTransGen_step_one_eq` — rank-one rigidity of `Step`.
* `diagonalConnectivity_false` — `hconn` is false over `ℝ`.
-/

open Module QuadraticMap

-- The chain definitions (`Module.Basis.IsContiguous`, `Module.Basis.Chain`, `ChainHypothesis`)
-- live in `Pptc/HasseMinkowski/BasisChain.lean`, so that `HasseInvariantWellDef.lean` can use
-- `ChainHypothesis` without an import cycle.

namespace Pptc.HasseMinkowski

variable {k : Type*} [Field k]

/-! ### The exact shape of `hconn`, and the genuine residual -/

/-- The connectivity hypothesis `hconn` of `hasseMinkowskiInvAux.eq_of_equivalent`, verbatim:
any two equivalent diagonalizations are linked by finitely many diagonal elementary moves
(reindexings and common rank-one splittings).  We prove below that this statement is **false**
over `ℝ`, so it cannot be used to discharge the reduction. -/
def DiagonalConnectivity (k : Type*) [Field k] : Prop :=
  ∀ {n : ℕ} (w w' : Fin n → kˣ),
    (weightedSumSquares k w).Equivalent (weightedSumSquares k w') →
      Relation.ReflTransGen (Step n) w w'

-- `ChainHypothesis` (the genuine residual, WiN7's `chainOfNondegenerate`) is defined in
-- `Pptc/HasseMinkowski/BasisChain.lean`.

/-! ### Rank-one rigidity of `Step` -/

-- Theorem: at rank one, a `Step` relates only equal weight tuples.  The permutation disjunct is
-- the unique equivalence `Fin 1 ≃ Fin 1`; the cons disjunct forces the single coordinate to be
-- the shared head `a` in both tuples.
theorem step_one_eq {k : Type*} [Field k] (u v : Fin 1 → kˣ) (h : Step 1 u v) : u = v := by
  rcases h with ⟨e, hv⟩ | ⟨a, w, w', hu, hv, _⟩
  · have he0 : e 0 = 0 := Fin.ext (Nat.lt_one_iff.mp (e 0).isLt)
    funext i
    fin_cases i
    have h0 := congr_fun hv 0
    simp only [Function.comp_apply, he0] at h0
    exact h0.symm
  · rw [hu, hv]
    funext i
    fin_cases i
    simp

-- Theorem: `ReflTransGen (Step 1)` relates only equal weight tuples.
theorem reflTransGen_step_one_eq {k : Type*} [Field k] (u v : Fin 1 → kˣ)
    (h : Relation.ReflTransGen (Step 1) u v) : u = v := by
  induction h with
  | refl => rfl
  | tail hab hbc ih => exact ih.trans (step_one_eq _ _ hbc)

/-! ### `hconn` is false -/

-- Theorem: the connectivity hypothesis `hconn` is false, already over `ℝ` at rank one.
theorem diagonalConnectivity_false : ¬ DiagonalConnectivity ℝ := by
  intro h
  have hequiv : (weightedSumSquares ℝ (fun _ : Fin 1 => (1 : ℝˣ))).Equivalent
      (weightedSumSquares ℝ (fun _ : Fin 1 => Units.mk0 (4 : ℝ) (by norm_num))) := by
    have hh := weightedSumSquares_mul_squares_equivalent (R := ℝ) (S := ℝ) (ι := Fin 1)
      (w := fun _ : Fin 1 => (1 : ℝ)) (w' := fun _ : Fin 1 => (4 : ℝ))
      (u := fun _ : Fin 1 => Units.mk0 (1 / 2 : ℝ) (by norm_num))
      (by intro i; fin_cases i; norm_num)
    rwa [weightedSumSquares_units_coe (w := fun _ : Fin 1 => (1 : ℝˣ)),
      weightedSumSquares_units_coe
        (w := fun _ : Fin 1 => Units.mk0 (4 : ℝ) (by norm_num))]
  have hchain : Relation.ReflTransGen (Step 1) (fun _ : Fin 1 => (1 : ℝˣ))
      (fun _ : Fin 1 => Units.mk0 (4 : ℝ) (by norm_num)) :=
    h (fun _ : Fin 1 => (1 : ℝˣ))
      (fun _ : Fin 1 => Units.mk0 (4 : ℝ) (by norm_num)) hequiv
  have heq : (fun _ : Fin 1 => (1 : ℝˣ)) =
      (fun _ : Fin 1 => Units.mk0 (4 : ℝ) (by norm_num)) :=
    reflTransGen_step_one_eq _ _ hchain
  have h01 : (1 : ℝ) = 4 := by
    have hc := congrArg (fun x : ℝˣ => (x : ℝ)) (congr_fun heq 0)
    simp only [Units.val_one, Units.val_mk0] at hc
    exact hc
  norm_num at h01

end Pptc.HasseMinkowski
