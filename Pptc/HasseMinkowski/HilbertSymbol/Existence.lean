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

-- Theorem: a prime of `S` divides the modulus `M`.
theorem dvd_M_of_mem_S (a : I → ℤ) {p : Primes} (hpS : p ∈ S a) : (p : ℕ) ∣ M a := by
  rw [M]
  by_cases hp2 : (p : ℕ) = 2
  · rw [hp2]
    exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 4) _
  · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun s : Primes => (s : ℕ)) hpS) 4

-- Theorem: a prime strictly below a prime `ℓ` does not divide `ℓ`.
theorem prime_not_dvd_of_lt {p : Primes} {ℓ : ℕ} (hℓ : ℓ.Prime) (hlt : (p : ℕ) < ℓ) :
    ¬ (p : ℕ) ∣ ℓ := by
  have hp2 : 1 < (p : ℕ) := p.2.one_lt
  rintro h
  rcases (Nat.dvd_prime hℓ).mp h with h1 | h2
  · omega
  · omega

/-- Coercion of an integral square to a rational square. -/
private lemma isSquare_ratCast_of_isSquare_intCast {p : ℕ} [Fact (Nat.Prime p)] {n : ℕ}
    (h : IsSquare ((n : ℤ_[p]))) : IsSquare ((n : ℚ_[p])) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨(z : ℚ_[p]), ?_⟩
  have hc := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz
  push_cast at hc
  simpa using hc

/-- An odd-`p` natural whose reduction mod `p` is a square is a square in `ℚ_[p]`. -/
private lemma isSquare_odd_natCast_of_mod {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2)
    {n : ℕ} (hm : ¬ (p : ℤ_[p]) ∣ (n : ℤ_[p])) (hmod : IsSquare ((n : ZMod p))) :
    IsSquare ((n : ℚ_[p])) :=
  isSquare_ratCast_of_isSquare_intCast (PadicInt.isSquare_of_zmod hp hm (by simpa using hmod))

/-- A natural congruent to `1` mod `8` is a square in `ℚ_[2]`. -/
private lemma isSquare_two_natCast_of_mod8 {n : ℕ} (hm8 : (n : ZMod 8) = 1) :
    IsSquare ((n : ℚ_[2])) := by
  have h2 : (n : ZMod 2) = 1 := by
    have hc := congrArg (ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)) hm8
    simpa using hc
  have hndvd : ¬ (2 : ℤ_[2]) ∣ (n : ℤ_[2]) := by
    intro hd
    have hd' : (n : ℤ_[2]).toZMod = 0 :=
      (PadicInt.p_dvd_iff_toZMod_eq_zero (p := 2)).mp hd
    rw [map_natCast, h2] at hd'
    exact one_ne_zero hd'
  obtain ⟨z, hz⟩ := PadicInt.isSquare_of_zmodPow hndvd (by
    rw [map_natCast, hm8]
    exact IsSquare.one)
  refine ⟨(z : ℚ_[2]), ?_⟩
  have hc := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hz
  push_cast at hc
  simpa using hc

-- Theorem: for `p ∈ S a`, the number `A · ℓ` is a square in `ℚ_[p]`.
theorem isSquare_A_mul_ell_of_mem_S
    (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hdisj : Disjoint (S a) (T hε h1)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓA : ℓ ≡ A hε h1 [MOD M a]) (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ)
    {p : Primes} (hpS : p ∈ S a) :
    IsSquare ((((A hε h1) * ℓ : ℕ) : ℚ_[p])) := by
  set A' : ℕ := A hε h1 with hA'
  set n : ℕ := A' * ℓ with hn
  have hpMdvd : (p : ℕ) ∣ M a := dvd_M_of_mem_S a hpS
  have hpT : p ∉ T hε h1 := disjoint_left.mp hdisj hpS
  have hAnot2 : ¬ 2 ∣ A' := by rw [hA']; exact not_two_dvd_A hε h1 hdisj
  have hpAd : ¬ (p : ℕ) ∣ A' := by rw [hA']; exact not_dvd_A_of_notMem_T hε h1 hpT
  have hplt : (p : ℕ) < ℓ := hℓgt p (Finset.mem_union.mpr (Or.inl hpS))
  have hpℓ : ¬ (p : ℕ) ∣ ℓ := prime_not_dvd_of_lt hℓ hplt
  have hpn : ¬ (p : ℕ) ∣ n := by
    rw [hn]
    exact p.2.not_dvd_mul hpAd hpℓ
  have hmodp : ℓ ≡ A' [MOD (p : ℕ)] := by rw [hA']; exact hℓA.of_dvd hpMdvd
  have hzeq : ((ℓ : ZMod (p : ℕ))) = ((A' : ZMod (p : ℕ))) :=
    (ZMod.natCast_eq_natCast_iff ℓ A' (p : ℕ)).mpr hmodp
  have hnz : ((n : ZMod (p : ℕ))) = (A' : ZMod (p : ℕ)) ^ 2 := by
    rw [hn, Nat.cast_mul, hzeq, sq]
  by_cases hp2 : (p : ℕ) = 2
  · have hmod8 : ℓ ≡ A' [MOD 8] := by rw [hA']; exact hℓA.of_dvd (eight_dvd_M a)
    have hℓ8 : ((ℓ : ZMod 8)) = ((A' : ZMod 8)) :=
      (ZMod.natCast_eq_natCast_iff ℓ A' 8).mpr hmod8
    have hn8 : ((n : ZMod 8)) = (A' : ZMod 8) ^ 2 := by
      rw [hn, Nat.cast_mul, hℓ8, sq]
    have hAodd : Odd A' :=
      Nat.not_even_iff_odd.mp (fun he => hAnot2 (even_iff_two_dvd.mp he))
    have hAsq : ((A' : ZMod 8)) ^ 2 = 1 := by
      set r : ℕ := A' % 8 with hr
      have hrval : ((r : ℕ) : ZMod 8) = (A' : ZMod 8) := by
        rw [hr]
        exact (ZMod.natCast_eq_natCast_iff (A' % 8) A' 8).mpr (Nat.mod_modEq A' 8)
      have hlt : r < 8 := by rw [hr]; exact Nat.mod_lt _ (by norm_num)
      have hodd : r % 2 = 1 := by
        rw [hr, Nat.mod_mod_of_dvd A' (by norm_num : 2 ∣ 8)]
        exact Nat.odd_iff.mp hAodd
      rw [← hrval]
      interval_cases r <;> (norm_num at hodd) <;> decide
    have hn1 : ((n : ZMod 8)) = 1 := by rw [hn8, hAsq]
    obtain rfl : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp2
    exact isSquare_two_natCast_of_mod8 hn1
  · have hm : ¬ (p : ℤ_[p]) ∣ (n : ℤ_[p]) := by
      intro hd
      have hd' : (n : ℤ_[p]).toZMod = 0 := (PadicInt.p_dvd_iff_toZMod_eq_zero).mp hd
      rw [map_natCast, ← Nat.cast_zero] at hd'
      exact hpn (Nat.modEq_zero_iff_dvd.mp ((ZMod.natCast_eq_natCast_iff n 0 (p : ℕ)).mp hd'))
    exact isSquare_odd_natCast_of_mod hp2 hm ⟨(A' : ZMod (p : ℕ)), by rw [hnz]; ring⟩

-- Theorem: for `p ∈ S a` and any `i`, the symbol `(a i, A·ℓ)_p` is `1`.
theorem hilbertSym_A_mul_ell_eq_one_of_mem_S (ha : ∀ i, a i ≠ 0)
    (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hdisj : Disjoint (S a) (T hε h1)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓA : ℓ ≡ A hε h1 [MOD M a]) (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ)
    {p : Primes} (hpS : p ∈ S a) (i : I) :
    hilbertSym (a i : ℚ_[p]) (((A hε h1) * ℓ : ℕ) : ℚ_[p]) = 1 := by
  obtain ⟨y, hy⟩ := isSquare_A_mul_ell_of_mem_S hε h1 hdisj hℓ hℓA hℓgt hpS
  have hn0 : (((A hε h1) * ℓ : ℕ) : ℚ_[p]) ≠ 0 := by
    push_cast
    exact mul_ne_zero (by exact_mod_cast A_ne_zero hε h1) (by exact_mod_cast hℓ.ne_zero)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hy
    exact hn0 hy
  have hai : (a i : ℚ_[p]) ≠ 0 := by exact_mod_cast ha i
  rw [hy, ← pow_two]
  exact hilbertSym_sq_right hai hy0

/-! ### The symbol at a `p`-adic unit against an arbitrary element

For odd `p`, if the first argument is a unit then only the parity of the valuation of the
second argument matters: `(u,b)_p = χ(u)` for odd valuation and `= 1` for even valuation. -/

-- Theorem: unfolding `padicUnit` to its underlying `p`-adic number.
private lemma coe_padicUnitE {p : ℕ} [Fact (Nat.Prime p)] (a : ℚ_[p]) (ha : a ≠ 0) :
    ((padicUnit a ha : ℤ_[p]) : ℚ_[p]) = a * (p : ℚ_[p]) ^ (-(a.valuation)) := by
  rw [padicUnit]
  exact congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) (IsUnit.unit_spec _)

-- Theorem: the valuation of a `p`-adic unit is `0`.
private lemma valuation_unit_eq_zero {p : ℕ} [Fact (Nat.Prime p)] (u : ℤ_[p]ˣ) :
    Padic.valuation ((u : ℤ_[p]) : ℚ_[p]) = 0 := by
  have hne : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    rw [PadicInt.coe_ne_zero]
    exact u.ne_zero
  have hnorm : ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [← PadicInt.norm_def, PadicInt.norm_units]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos Fact.out
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast (ne_of_gt (Nat.Prime.one_lt Fact.out))
  have h : (p : ℝ) ^ (-(Padic.valuation ((u : ℤ_[p]) : ℚ_[p]))) = (p : ℝ) ^ (0 : ℤ) := by
    rw [zpow_zero, ← Padic.norm_eq_zpow_neg_valuation hne, hnorm]
  have := (zpow_right_inj₀ hp0 hp1).mp h
  simpa using this

-- Theorem: the unit part of a `p`-adic unit is that unit.
private lemma padicUnit_unit {p : ℕ} [Fact (Nat.Prime p)] (u : ℤ_[p]ˣ)
    (hu : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0) :
    padicUnit ((u : ℤ_[p]) : ℚ_[p]) hu = u := by
  apply Units.ext
  apply Subtype.ext
  rw [coe_padicUnitE, valuation_unit_eq_zero, neg_zero, zpow_zero, mul_one]

-- Theorem: for odd `p`, `(u,b)_p` for a unit `u` depends only on the parity of `b`'s
-- valuation: it is `χ(u)` for odd valuation and `1` for even valuation.
private lemma hilbertSym_unit_eq_parity {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2)
    (u : ℤ_[p]ˣ) {b : ℚ_[p]} (hb : b ≠ 0) :
    hilbertSym ((u : ℤ_[p]) : ℚ_[p]) b =
      if Even b.valuation then 1
        else (quadraticChar (ZMod p)) (PadicInt.toZMod (u : ℤ_[p])) := by
  have hu : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    rw [PadicInt.coe_ne_zero]
    exact u.ne_zero
  rw [hilbertSym_padic_odd_eq hp hu hb, valuation_unit_eq_zero u, padicUnit_unit u hu]
  simp [parityPow]

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
