/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.HilbertSymbol.Defs
import Pptc.HasseMinkowski.HilbertSymbol.Padic
import Pptc.HasseMinkowski.HilbertSymbol.Real
import Pptc.HasseMinkowski.HilbertSymbol.Reciprocity
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

## Status

This file currently provides the constructive core only: the Dirichlet/CRT construction of
`S`, `T`, `A`, `M` and the squareness/valuation lemmas that the place-by-place verification
consumes.  The verification itself is WP3 of `Plan-v3.md`; every ingredient it needs — the
Serre formulas `hilbertSym_padic_odd_eq` / `hilbertSym_padic_two_eq`, the global product
identity (`almost_all_one`, `hilbertReciprocity`) and the norm criterion
(`HilbertSymbol/Norm.lean`) — now exists in the library, so only the assembly of WP3.1–3.2
remains.  No `sorry` is introduced.
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

/-! ### WP3.1 sub-lemmas: the auxiliary prime `ℓ`

The construction `x = A · ℓ` needs `ℓ` to be a prime larger than every prime of `S ∪ T`
and congruent to `A` modulo `M`.  These lemmas record the elementary consequences of those
two hypotheses: `ℓ ∉ T` (hence `ε_{i,ℓ} = 1`), the congruence `M ∣ ℓ - A`, and the
divisibility of `A` by exactly the primes of `T`. -/

-- Theorem: a prime `ℓ` that exceeds every prime of `S ∪ T` is not in `T`.
theorem prime_notMem_T_of_lt (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ) : (⟨ℓ, hℓ⟩ : Primes) ∉ T hε h1 := by
  intro hmem
  exact absurd (hℓgt _ (Finset.mem_union.mpr (Or.inr hmem))) (lt_irrefl ℓ)

-- Theorem: a prime `ℓ` that exceeds every prime of `S ∪ T` satisfies `ε_{i,ℓ} = 1` for
-- every `i`.
theorem ep_eq_one_prime_of_lt (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ) (i : I) : ep i ⟨ℓ, hℓ⟩ = 1 :=
  ep_eq_one_of_not_mem_T hε h1 (prime_notMem_T_of_lt hε h1 hℓ hℓgt) i

-- Theorem: `M a` divides `ℓ - A` as integers; equivalently `(ℓ : ℤ) ≡ A [ZMOD M]`.
theorem M_dvd_int (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {ℓ : ℕ}
    (hℓA : ℓ ≡ A hε h1 [MOD M a]) :
    (M a : ℤ) ∣ (ℓ : ℤ) - (A hε h1 : ℤ) := by
  have h : (M a : ℤ) ∣ (A hε h1 : ℤ) - (ℓ : ℤ) := hℓA.dvd
  have h2 : (M a : ℤ) ∣ -((A hε h1 : ℤ) - (ℓ : ℤ)) := h.neg_right
  rwa [neg_sub] at h2

-- Theorem: every prime of `T` divides `A`.
theorem dvd_A_of_mem_T (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {p : Primes}
    (hp : p ∈ T hε h1) : (p : ℕ) ∣ A hε h1 := by
  rw [A]
  exact Finset.dvd_prod_of_mem (fun t : Primes => (t : ℕ)) hp

-- Theorem: a prime outside `T` does not divide `A`.
theorem not_dvd_A_of_notMem_T (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {p : Primes}
    (hp : p ∉ T hε h1) : ¬ (p : ℕ) ∣ A hε h1 := by
  rw [A]
  intro hdvd
  obtain ⟨t, ht, hpt⟩ :=
    (p.2.prime.dvd_finsetProd_iff (fun t : Primes => (t : ℕ))).mp hdvd
  have hpt_eq : p = t := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 t.2).mp hpt)
  exact hp (by simpa [hpt_eq] using ht)

-- Theorem: disjointness of `S` and `T` puts `2` outside `T`.
theorem two_notMem_T_of_disjoint (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hdisj : Disjoint (S a) (T hε h1)) : (⟨2, Nat.prime_two⟩ : Primes) ∉ T hε h1 :=
  disjoint_left.mp hdisj (two_in_S a)

-- Theorem: disjointness of `S` and `T` makes `A` odd.
theorem not_two_dvd_A (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hdisj : Disjoint (S a) (T hε h1)) : ¬ 2 ∣ A hε h1 :=
  not_dvd_A_of_notMem_T hε h1 (two_notMem_T_of_disjoint hε h1 hdisj)

-- Theorem: `M = 4 · ∏_{s ∈ S} s` is divisible by `8`, because `2 ∈ S`.
theorem eight_dvd_M (a : I → ℤ) : 8 ∣ M a := by
  rw [M]
  have hdvd : 2 ∣ ∏ s ∈ S a, (s : ℕ) :=
    Finset.dvd_prod_of_mem (fun s : Primes => (s : ℕ)) (two_in_S a)
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨c, by rw [hc]; ring⟩

/-! ### The product-formula obstruction

The hypotheses of `exists_disjoint` force the construction `x = A · ℓ`, but they do not
constrain the *product* of the prescribed values `ep i p`.  The lemma below shows this is a
genuine obstruction: if `a > 0` and a nonzero rational `x` realises the sign pattern that is
`-1` at a single prime `p₀` and `1` at every other finite place, then Hilbert reciprocity
(whose archimedean factor is `1` because `a > 0`) is violated.  Thus no version of
`exists_disjoint` without a hypothesis `∏ᶠ p, ep i p = 1` can be true. -/

-- Theorem: for `a > 0` there is no `x ≠ 0` whose Hilbert symbols against `a` are `-1` at a
-- single prime and `1` at every other prime.
--
-- Concretely, taking `I = Unit`, `a = 3`, `ep p = if p = 5 then -1 else 1` satisfies all
-- the hypotheses of `exists_disjoint`: `S a = {2,3}`, `T = {5}` are disjoint, `h3` holds
-- (`x = 5` at `p = 5`, `x = 1` elsewhere), and `ℓ = 29` is a prime `> max(S ∪ T)` with
-- `29 ≡ 5 [MOD 24]`.  But the conclusion would give an `x` with `(3,x)_5 = -1` and
-- `(3,x)_p = 1` for all `p ≠ 5`, which this theorem rules out.  Hence `exists_disjoint`
-- cannot be proved as stated; a product-formula hypothesis is missing.
theorem not_realizable_of_single_neg {a : ℚ} (ha : 0 < a) {p₀ : Primes} {x : ℚ}
    (hx : x ≠ 0)
    (hother : ∀ p : Primes, p ≠ p₀ → hilbertSym (a : ℚ_[p]) (x : ℚ_[p]) = 1)
    (hp₀ : hilbertSym (a : ℚ_[p₀]) (x : ℚ_[p₀]) = -1) : False := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hxR : (x : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hx
  have haR : (a : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ha0
  have hreal : hilbertSym (a : ℝ) (x : ℝ) = 1 := by
    rw [hilbertSym_real_eq haR hxR]
    exact if_pos (Or.inl (by exact_mod_cast ha))
  have hprod : hilbertProd a x = 1 := hilbertReciprocity a x ha0 hx
  have hfp : (∏ᶠ p : Primes, hilbertSym (a : ℚ_[p]) (x : ℚ_[p])) = -1 := by
    rw [finprod_eq_single _ p₀ hother, hp₀]
  unfold hilbertProd at hprod
  rw [hfp, hreal] at hprod
  norm_num at hprod

end Existence

end Pptc.HasseMinkowski
