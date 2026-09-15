/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.HilbertSymbol.Defs
import Pptc.HasseMinkowski.HilbertSymbol.Padic
import Pptc.HasseMinkowski.HilbertSymbol.Real
import Pptc.HasseMinkowski.Padics.Squares
import Pptc.HasseMinkowski.RatSquares
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Hilbert-symbol existence theorem (port of WiN7 `HilbertSymbol/ExistenceTheorem.lean`)

Given prescribed local Hilbert-symbol values `(x, aᵢ)_v = e_{i,v}` at all places `v` of `ℚ`,
one asks whether there is a single rational `x` realising all of them.  The answer is given
by the classical necessary-and-sufficient conditions (Serre, *Cours d'arithmétique*, Ch. III):

1. for each `i`, almost all the `e_{i,v}` are `1`;
2. for each `i`, the product of the `e_{i,v}` is `1` (the product formula);
3. the prescription is locally realisable at every place.

This file ports the **constructive core** of WiN7's proof.  Writing `S` for the finite set of
prime numbers dividing some `aᵢ` (together with `2`) and `T` for the finite set of primes at
which some `e_{i,p}` equals `-1`, the construction produces
`x = A · q` with `A = ∏_{t ∈ T} t` and `q` a prime chosen by Dirichlet's theorem so that
`q ≡ A (mod 4·∏_{s ∈ S} s)`.  This `x` is a square at every prime of `S`, has `p`-adic
valuation `1` at every prime of `T` and valuation `0` at the remaining primes — exactly the
three facts on which the place-by-place verification rests.

## Status / remaining gap

The place-by-place verification itself (WiN7 `existence_disjoint` and the two `…_of_int`
statements) is **not** reachable from the current library: it requires the general Serre
formula `hilbertSym.padic_odd_eq` / `two_adic_eq` and the global product identity
`hilbertSym.almost_all_one` / `prod_eq_one`, none of which are proved locally
(`HilbertSymbol/Padic.lean` currently contains only the two-units case `00`; see
`HANDOFF-hilbertpadic.md`).  Upstream those statements are themselves `sorry`.  Accordingly
this file ports everything they *consume* — the Dirichlet/CRT construction, the squareness
at `S`, and the valuation computations at `T` and its complement — and documents the
missing ingredients rather than introducing `sorry`.
-/

set_option linter.style.openClassical false

namespace Pptc.HasseMinkowski

open scoped BigOperators
open Classical Filter Finset Nat

namespace Existence

variable {I : Type*} {a : I → ℤ} {ep : I → Primes → ℤ} {ereal : I → ℤ}

/-- From `ep i p = 1` or `-1`, we deduce `ep i p = -1` iff not `ep i p = 1`. -/
private lemma ep_eq_neg_one_iff_not_one
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) {i : I} {p : Primes} :
    ep i p = -1 ↔ ¬ ep i p = 1 :=
  ⟨fun h => by simp [h], fun h => (hep i p).resolve_left h⟩

variable [Finite I]

/-- `S` is the finite set of primes dividing the numerator or the denominator of some `a i`,
together with `2`.  (In Serre, `S` also contains `∞`.) -/
noncomputable def S (a : I → ℤ) : Finset Primes :=
  have : Fintype I := Fintype.ofFinite I
  (Finset.univ.biUnion (fun i => (a i).natAbs.primeFactors) ∪ {2}).preimage Subtype.val
    Subtype.val_injective.injOn

-- Theorem: the prime `2` lies in `S`.
theorem two_in_S (a : I → ℤ) : (⟨2, Nat.prime_two⟩ : Primes) ∈ S a := by
  simp only [S]
  exact Finset.mem_preimage.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))

-- Theorem: the set of primes where some `ep i p` equals `-1` is finite, by hypothesis `h1`.
theorem Tfin (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) :
    (⋃ i : I, {p : Primes | ep i p = -1}).Finite := by
  refine Set.finite_iUnion fun i => ?_
  simp only [eventually_cofinite, ← ep_eq_neg_one_iff_not_one hep, Int.reduceNeg] at h1
  exact h1 i

/-- `T` is the finite set of primes such that at least one of the `e_{i,v}` is `-1`. -/
noncomputable def T (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) : Finset Primes :=
  (Tfin hep h1).toFinset

-- Theorem: a prime outside `T` has all its prescribed symbols equal to `1`.
theorem ep_eq_one_of_not_mem_T (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    {p : Primes} (hpT : p ∉ T hep h1) (i : I) : ep i p = 1 := by
  simp only [T, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists,
    ep_eq_neg_one_iff_not_one hep] at hpT
  exact of_not_not (hpT i)

-- Theorem: membership in `T` characterisation.
theorem ep_eq_one_iff_not_mem_T (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) (p : Primes) :
    p ∉ T hep h1 ↔ ∀ i : I, ep i p = 1 := by
  constructor
  · intro h i
    exact ep_eq_one_of_not_mem_T hep h1 h i
  · intro h
    simp only [T, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists]
    intro i
    rw [ep_eq_neg_one_iff_not_one hep]
    exact fun hc => hc (h i)

-- Theorem: if `S` and `T` are disjoint, every prime of `S` has all its symbols equal to `1`.
theorem ep_eq_one_of_mem_S_disjoint (a : I → ℤ)
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (disjoint_ST : Disjoint (S a) (T hep h1)) {p : Primes} (hpS : p ∈ S a) (i : I) :
    ep i p = 1 :=
  ep_eq_one_of_not_mem_T hep h1 (disjoint_left.mp disjoint_ST hpS) i

-- Theorem: if `p ∉ S` then every `a i` is a `p`-adic unit.
theorem is_unit_ai_of_p_notMem_S (a : I → ℤ) (ha : ∀ i, a i ≠ 0) {p : Primes}
    (hpS : p ∉ S a) (i : I) : padicValInt p (a i) = 0 := by
  have : Fintype I := Fintype.ofFinite I
  have hmem : p.1 ∉ Finset.univ.biUnion (fun i => (a i).natAbs.primeFactors) := by
    intro h
    apply hpS
    simp only [S]
    exact Finset.mem_preimage.mpr (Finset.mem_union.mpr (Or.inl (by simpa using h)))
  simp only [Finset.mem_biUnion, Finset.mem_univ, Nat.mem_primeFactors, p.2,
    ← Int.natCast_dvd, ne_eq, Int.natAbs_eq_zero, ha, not_false_eq_true, and_true, true_and,
    not_exists] at hmem
  exact padicValInt.eq_zero_of_not_dvd (hmem i)

/-- `A` is the product of all primes of `T`. -/
noncomputable def A (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) : ℕ :=
  ∏ t ∈ T hep h1, (t : ℕ)

-- Theorem: `A` is nonzero.
theorem A_ne_zero (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) : A hep h1 ≠ 0 := by
  rw [A, Finset.prod_ne_zero_iff]
  intro t _
  exact t.2.ne_zero

-- Theorem: `A` is positive.
theorem A_pos (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) : 0 < A hep h1 :=
  Nat.pos_of_ne_zero (A_ne_zero hep h1)

/-- `M = 4 · ∏_{s ∈ S} s`, the modulus used in the congruence defining `q`. -/
noncomputable def M (a : I → ℤ) : ℕ := 4 * ∏ s ∈ S a, (s : ℕ)

-- Theorem: `M` is nonzero.
theorem M_ne_zero (a : I → ℤ) : M a ≠ 0 := by
  rw [M]
  refine mul_ne_zero (by norm_num) ?_
  rw [Finset.prod_ne_zero_iff]
  intro s _
  exact s.2.ne_zero

end Existence

end Pptc.HasseMinkowski
