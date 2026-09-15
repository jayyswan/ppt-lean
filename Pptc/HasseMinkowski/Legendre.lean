import Pptc.HasseMinkowski.HilbertSymbol.Norm
import Pptc.HasseMinkowski.HilbertSymbol.Padic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# WP1 1.1 — norm transfer for the Hilbert symbol

The Hilbert symbol `(a, b)_k` depends on `b` only through its class in `kˣ / kˣ²`, but in the
form used later (the descent in the proof of quadratic reciprocity) the input is not a square
multiple of `b` but a *norm* from `k(√a)`: we are handed `t` with `t ^ 2 - a = b * b'`.

Geometrically, `t + √a` has norm `t ^ 2 - a = b * b'` in `k(√a)`, so if `b` is a norm then so is
`b'` (divide the norm identity by `b`), and conversely. Since a nonzero nonsquare `a` satisfies
`(b, a)_k = 1` exactly when `b` is a norm from `k(√a)`, the two symbols agree.
-/

set_option linter.style.openClassical false

namespace Pptc.HasseMinkowski

open Classical

/-- If `t ^ 2 - a = b * b'` with `b` and `b'` nonzero, then `(a, b)_k = (a, b')_k`: the two
second arguments differ by the norm of `t + √a` in `k(√a)`, and being a norm from `k(√a)` is
invariant under multiplication by a square class, in particular under `b ↦ (t² - a) / b`. -/
-- Theorem: if `t ^ 2 - a = b * b'` with `b`, `b'` nonzero, then `(a,b)_k = (a,b')_k`.
theorem hilbertSym_eq_of_sq_sub_eq_mul {k : Type*} [Field k] [Invertible (2 : k)]
    {a b b' t : k} (hb : b ≠ 0) (hb' : b' ≠ 0) (h : t ^ 2 - a = b * b') :
    hilbertSym a b = hilbertSym a b' := by
  -- If `b` is a norm from `k(√a)` then so is `b'`, and vice versa.
  have aux : ∀ c c' : k, c ≠ 0 → c' ≠ 0 → t ^ 2 - a = c * c' →
      (∃ u : QuadraticAlgebra k a 0, c = u.norm) →
      ∃ u : QuadraticAlgebra k a 0, c' = u.norm := by
    intro c c' hc hc' hcc' ⟨u, hu⟩
    refine ⟨algebraMap k (QuadraticAlgebra k a 0) c⁻¹ * (⟨t, 1⟩ * star u), ?_⟩
    have hw : (⟨t, 1⟩ : QuadraticAlgebra k a 0).norm = c * c' := by
      simp [QuadraticAlgebra.norm_def]
      linear_combination hcc'
    simp only [map_mul, QuadraticAlgebra.norm_algebraMap, QuadraticAlgebra.norm_star, hw, ← hu]
    field_simp
  by_cases ha : a = 0
  · rw [ha]
    simp [hilbertSym_zero_left]
  · by_cases hsq : IsSquare a
    · -- `a` is a nonzero square, so both symbols are `1`.
      rcases hsq with ⟨s, hs⟩
      have h1 : hilbertSym a b = 1 := by
        refine hilbertSym_eq_one_of_sol ha hb ⟨s, 1, 0, by simp, ?_⟩
        rw [hs]
        ring
      have h2 : hilbertSym a b' = 1 := by
        refine hilbertSym_eq_one_of_sol ha hb' ⟨s, 1, 0, by simp, ?_⟩
        rw [hs]
        ring
      rw [h1, h2]
    · -- Main case: `a` is a nonzero nonsquare; use the norm characterization.
      rw [hilbertSym_comm a b, hilbertSym_comm a b']
      have hiff1 := hilbertSym_eq_one_iff_isNorm (a := b) (b := a) hb ha hsq
      have hiff2 := hilbertSym_eq_one_iff_isNorm (a := b') (b := a) hb' ha hsq
      have key : (∃ u : QuadraticAlgebra k a 0, b = u.norm) ↔
          (∃ u : QuadraticAlgebra k a 0, b' = u.norm) :=
        ⟨aux b b' hb hb' h, aux b' b hb' hb (h.trans (mul_comm b b'))⟩
      have hiff : (hilbertSym b a = 1) ↔ (hilbertSym b' a = 1) := by
        rw [hiff1, hiff2]
        exact key
      have hb0 : hilbertSym b a ≠ 0 := by
        intro hc
        rw [hilbertSym_eq_zero_iff] at hc
        exact hc.elim hb ha
      have hb'0 : hilbertSym b' a ≠ 0 := by
        intro hc
        rw [hilbertSym_eq_zero_iff] at hc
        exact hc.elim hb' ha
      rcases hilbertSym_eq_one_or b a with h1 | h0 | hm1
      · rcases hilbertSym_eq_one_or b' a with h2 | h02 | hm2
        · rw [h1, h2]
        · exact absurd h02 hb'0
        · exact absurd (hiff.mp h1) (by rw [hm2]; norm_num)
      · exact absurd h0 hb0
      · rcases hilbertSym_eq_one_or b' a with h2 | h02 | hm2
        · exact absurd (hiff.mpr h2) (by rw [hm1]; norm_num)
        · exact absurd h02 hb'0
        · rw [hm1, hm2]

/-! ### WP1 1.4 — the squarefree normal form

Every nonzero integer is a squarefree integer times a nonzero square, and the same holds for
every nonzero rational after clearing denominators. -/

/-- Every nonzero integer is a squarefree integer times a nonzero square. -/
-- Theorem: nonzero integer normal form `n = m * u ^ 2` with `m` squarefree and `u ≠ 0`.
theorem exists_squarefree_mul_sq_int (n : ℤ) (hn : n ≠ 0) :
    ∃ m u : ℤ, Squarefree m ∧ u ≠ 0 ∧ n = m * u ^ 2 := by
  obtain ⟨a, b, hba, hsf⟩ := Nat.sq_mul_squarefree n.natAbs
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hba
    exact Int.natAbs_ne_zero.mpr hn hba.symm
  have hbZ : (b : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hb
  have hbaZ : (b : ℤ) ^ 2 * (a : ℤ) = (n.natAbs : ℤ) := by exact_mod_cast hba
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  · have hsfZneg : Squarefree (-(a : ℤ)) := by
      rw [← Int.squarefree_natAbs]
      simpa using hsf
    refine ⟨-(a : ℤ), (b : ℤ), hsfZneg, hbZ, ?_⟩
    have hthis : n = -(n.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_neg hneg]
      ring
    rw [hthis, ← hbaZ]
    ring
  · exact absurd hzero hn
  · have hsfZ : Squarefree (a : ℤ) := by simpa using hsf
    refine ⟨(a : ℤ), (b : ℤ), hsfZ, hbZ, ?_⟩
    have hthis : n = (n.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonneg (le_of_lt hpos)]
    rw [hthis, ← hbaZ]
    ring

/-- Every nonzero rational is a squarefree integer times a nonzero square. -/
-- Theorem: nonzero rational normal form `A = a * s ^ 2` with `a : ℤ` squarefree and `s ≠ 0`.
theorem exists_squarefree_mul_sq (A : ℚ) (hA : A ≠ 0) :
    ∃ a : ℤ, Squarefree a ∧ ∃ s : ℚ, s ≠ 0 ∧ A = a * s ^ 2 := by
  set u : ℕ := A.num.natAbs with hu_def
  set v : ℕ := A.den with hv_def
  have hu : 0 < u := by
    rw [hu_def]
    exact Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hA)
  have hv : 0 < v := by
    rw [hv_def]
    exact Nat.pos_of_ne_zero A.den_ne_zero
  obtain ⟨a, b, -, hb, hba, hsf⟩ := Nat.sq_mul_squarefree_of_pos (Nat.mul_pos hu hv)
  have hbne : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hvne : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv.ne'
  have hs : (b : ℚ) / (v : ℚ) ≠ 0 := div_ne_zero hbne hvne
  have habs : |A| = (u : ℚ) / (v : ℚ) := by
    rw [Rat.abs_def, ← hu_def, ← hv_def, Rat.divInt_eq_div]
    norm_num
  have h1 : (b : ℚ) ^ 2 * (a : ℚ) = (u : ℚ) * (v : ℚ) := by exact_mod_cast hba
  have hfrac : (u : ℚ) / (v : ℚ) = (a : ℚ) * ((b : ℚ) / (v : ℚ)) ^ 2 := by
    field_simp
    nlinarith [h1]
  by_cases hneg : A < 0
  · refine ⟨-(a : ℤ), ?_, (b : ℚ) / (v : ℚ), hs, ?_⟩
    · rw [← Int.squarefree_natAbs]
      simpa using hsf
    · have hA' : A = -((u : ℚ) / (v : ℚ)) := by
        rw [abs_of_neg hneg] at habs
        rw [← habs]
        ring
      rw [hA', hfrac]
      push_cast
      ring
  · have hnonneg : 0 ≤ A := le_of_not_gt hneg
    refine ⟨(a : ℤ), by simpa using hsf, (b : ℚ) / (v : ℚ), hs, ?_⟩
    · rw [abs_of_nonneg hnonneg] at habs
      rw [habs, hfrac]
      push_cast
      ring

/-! ### WP1 1.3 — combining the local congruences by CRT

If `t ^ 2 ≡ a (mod p)` is solvable for every prime `p ∣ b` with `b` squarefree, then it is
solvable modulo `b`, and the solution can be chosen in the balanced range `2 |t| ≤ |b|`.
The balanced representative is `Int.bmod`, which preserves the congruence and satisfies the
bound. -/

/-- **CRT plus a size bound.** For squarefree `b`, if `t ^ 2 - a` is divisible by every prime
factor of `b`, then some residue class `t` satisfies `b ∣ t ^ 2 - a` and `2 * |t| ≤ |b|`. -/
-- Theorem: local square-mod-`p` data for all `p ∣ b` combine to `b ∣ t ^ 2 - a` with
-- `2 * |t| ≤ |b|`.
theorem exists_sq_mod_squarefree (a b : ℤ) (hb : Squarefree b)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a) :
    ∃ t : ℤ, b ∣ t ^ 2 - a ∧ 2 * |t| ≤ |b| := by
  classical
  have hb0 : b ≠ 0 := hb.ne_zero
  set m : ℕ := b.natAbs with hm_def
  have hmpos : 0 < m := by rw [hm_def]; exact Int.natAbs_pos.mpr hb0
  have hsfm : Squarefree m := by rw [hm_def]; exact Int.squarefree_natAbs.mpr hb
  -- a chosen witness for every prime dividing `b`
  let w : ℕ → ℤ :=
    fun p => if hp : p.Prime ∧ (p : ℤ) ∣ b then (h p hp.1 hp.2).choose else 0
  have hw : ∀ (p : ℕ) (hp : p.Prime) (hpb : (p : ℤ) ∣ b), (p : ℤ) ∣ (w p) ^ 2 - a := by
    intro p hp hpb
    have hcond : p.Prime ∧ (p : ℤ) ∣ b := ⟨hp, hpb⟩
    simp only [w, dif_pos hcond]
    exact (h p hp hpb).choose_spec
  -- the nonnegative residues used by the Chinese remainder theorem
  let A : ℕ → ℕ := fun p => ((w p) % (p : ℤ)).toNat
  have hAeq : ∀ {p : ℕ} (hp : p ≠ 0), (A p : ℤ) = w p % (p : ℤ) := by
    intro p hp
    exact Int.toNat_of_nonneg (Int.emod_nonneg (w p) (by exact_mod_cast hp))
  have hAdvd : ∀ {p : ℕ} (hp : p ≠ 0), (p : ℤ) ∣ (A p : ℤ) - w p := by
    intro p hp
    rw [hAeq hp]
    exact Int.dvd_emod_sub_self
  have hcop : (m.primeFactors : Set ℕ).Pairwise (fun p q => Nat.Coprime p q) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset A (fun p => p) m.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero) hcop
  -- each prime factor of `m` divides `k ^ 2 - a`
  have hprime : ∀ p ∈ m.primeFactors, (p : ℤ) ∣ (k : ℤ) ^ 2 - a := by
    intro p hpS
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpb : (p : ℤ) ∣ b := by
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      simpa [← hm_def] using Nat.dvd_of_mem_primeFactors hpS
    have hkp : (p : ℤ) ∣ (k : ℤ) - (A p : ℤ) := by
      have h' : (p : ℤ) ∣ (A p : ℤ) - (k : ℤ) := Nat.modEq_iff_dvd.mp (hk p hpS)
      have he : (k : ℤ) - (A p : ℤ) = -((A p : ℤ) - (k : ℤ)) := by ring
      rw [he]
      exact dvd_neg.mpr h'
    have hsq1 : (p : ℤ) ∣ (k : ℤ) ^ 2 - (A p : ℤ) ^ 2 := by
      have he : (k : ℤ) ^ 2 - (A p : ℤ) ^ 2
          = ((k : ℤ) - (A p : ℤ)) * ((k : ℤ) + (A p : ℤ)) := by ring
      rw [he]
      exact hkp.mul_right _
    have hsq2 : (p : ℤ) ∣ (A p : ℤ) ^ 2 - (w p) ^ 2 := by
      have h' : (p : ℤ) ∣ (A p : ℤ) - w p := hAdvd hpp.ne_zero
      have he : (A p : ℤ) ^ 2 - (w p) ^ 2
          = ((A p : ℤ) - w p) * ((A p : ℤ) + w p) := by ring
      rw [he]
      exact h'.mul_right _
    have hsq3 : (p : ℤ) ∣ (w p) ^ 2 - a := hw p hpp hpb
    have hsum : (p : ℤ) ∣ ((k : ℤ) ^ 2 - (A p : ℤ) ^ 2)
        + ((A p : ℤ) ^ 2 - (w p) ^ 2) + ((w p) ^ 2 - a) :=
      dvd_add (dvd_add hsq1 hsq2) hsq3
    have he : ((k : ℤ) ^ 2 - (A p : ℤ) ^ 2) + ((A p : ℤ) ^ 2 - (w p) ^ 2)
        + ((w p) ^ 2 - a) = (k : ℤ) ^ 2 - a := by ring
    rwa [he] at hsum
  -- the product of the prime factors of `m` is `m`, and divides `k ^ 2 - a`
  have hprod : (∏ p ∈ m.primeFactors, (p : ℤ)) ∣ (k : ℤ) ^ 2 - a := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro p hp q hq hpq
      exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq |>.cast
    · exact hprime
  have hprod_eq : (∏ p ∈ m.primeFactors, (p : ℤ)) = (m : ℤ) := by
    have hcast : (∏ p ∈ m.primeFactors, (p : ℤ))
        = ((∏ p ∈ m.primeFactors, p : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [hcast, Nat.prod_primeFactors_of_squarefree hsfm]
  have hmdvd : (m : ℤ) ∣ (k : ℤ) ^ 2 - a := by
    rwa [hprod_eq] at hprod
  -- balance `k` with `Int.bmod`
  refine ⟨Int.bmod (k : ℤ) m, ?_, ?_⟩
  · have ht : (m : ℤ) ∣ (Int.bmod (k : ℤ) m) ^ 2 - (k : ℤ) ^ 2 := by
      have h1 : (m : ℤ) ∣ Int.bmod (k : ℤ) m - (k : ℤ) := Int.dvd_bmod_sub_self
      have he : (Int.bmod (k : ℤ) m) ^ 2 - (k : ℤ) ^ 2
          = (Int.bmod (k : ℤ) m - (k : ℤ)) * (Int.bmod (k : ℤ) m + (k : ℤ)) := by ring
      rw [he]
      exact h1.mul_right _
    have hsum : (m : ℤ) ∣ (Int.bmod (k : ℤ) m) ^ 2 - a := by
      have hs := dvd_add ht hmdvd
      have he : ((Int.bmod (k : ℤ) m) ^ 2 - (k : ℤ) ^ 2) + ((k : ℤ) ^ 2 - a)
          = (Int.bmod (k : ℤ) m) ^ 2 - a := by ring
      rwa [he] at hs
    have hmb : (m : ℤ) = |b| := by
      rw [hm_def]
      exact Int.natCast_natAbs b
    rw [hmb] at hsum
    exact (abs_dvd b _).mp hsum
  · have h1 : Int.bmod (k : ℤ) m ≤ ((m : ℤ) - 1) / 2 := Int.bmod_le hmpos
    have h2 : -((m : ℤ) / 2) ≤ Int.bmod (k : ℤ) m := Int.le_bmod hmpos
    have habs : |Int.bmod (k : ℤ) m| ≤ (m : ℤ) / 2 := by
      rw [abs_le]
      refine ⟨h2, ?_⟩
      have hle : ((m : ℤ) - 1) / 2 ≤ (m : ℤ) / 2 := by omega
      exact le_trans h1 hle
    have h2m : 2 * ((m : ℤ) / 2) ≤ (m : ℤ) := by omega
    have hfin : 2 * |Int.bmod (k : ℤ) m| ≤ (m : ℤ) := by linarith
    rw [show |b| = (m : ℤ) by rw [hm_def]; exact (Int.natCast_natAbs b).symm]
    exact hfin

/-! ### WP1 1.2 — the local symbol being `1` forces a square residue

If `(a, b)_p = 1`, `b` is squarefree and `p ∣ b`, then `a` is a square modulo `p`. The case
`p ∣ a` is trivial (`t = 0`), and `p = 2` follows from `a ^ 2 ≡ a (mod 2)` (`t = a`). For odd
`p` with `p ∤ a`, the integer `b` has `p`-adic valuation `1` (squarefree plus `p ∣ b`), so
its norm is `p⁻¹`, while `p ∤ a` makes `a` a unit of `ℤ_[p]`. Serre's case `10` formula then
reads
`(a, b)_p = (a / p)`, the quadratic character of `a`; being `1` it says `a` is a square mod `p`,
and that square lifts back to an integer `t` with `p ∣ t ^ 2 - a`. -/

/-- **Local square residue.** If the local Hilbert symbol `(a, b)_p` equals `1` for a squarefree
`b` divisible by `p`, then `a ≡ t ^ 2 (mod p)` for some integer `t`. -/
-- Theorem: `(a,b)_p = 1` for `p ∣ b` squarefree implies `∃ t : ℤ, p ∣ t ^ 2 - a`.
theorem exists_sq_mod_of_hilbertSym (a b : ℤ) (hb : Squarefree b) (p : ℕ) [Fact p.Prime]
    (hpb : (p : ℤ) ∣ b) (h : hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) = 1) :
    ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a := by
  have hp : p.Prime := Fact.out
  by_cases hpa : (p : ℤ) ∣ a
  · exact ⟨0, by simpa using (dvd_neg.mpr hpa)⟩
  by_cases hp2 : p = 2
  · refine ⟨a, ?_⟩
    rw [hp2]
    have hz : (((a ^ 2 - a : ℤ)) : ZMod 2) = 0 := by
      push_cast
      exact (show ∀ x : ZMod 2, x ^ 2 - x = 0 by decide) _
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a := a ^ 2 - a) (b := 2)).mp hz
  · have hb0 : b ≠ 0 := hb.ne_zero
    have ha0 : a ≠ 0 := fun h0 => hpa (by rw [h0]; exact dvd_zero _)
    have hbQ : (b : ℚ_[p]) ≠ 0 := by exact_mod_cast hb0
    -- `b` has `p`-adic valuation `1`, hence norm `p⁻¹`
    have hsfnat : Squarefree b.natAbs := Int.squarefree_natAbs.mpr hb
    have hnotsq : ¬ (p : ℤ) ^ 2 ∣ b := by
      intro hd
      have hd' : p ^ 2 ∣ b.natAbs := by
        have h'' := (Int.natAbs_dvd_natAbs (a := (p : ℤ) ^ 2) (b := b)).mpr hd
        simpa using h''
      exact (Nat.squarefree_iff_prime_squarefree.mp hsfnat p hp) (by simpa [pow_two] using hd')
    have hv1 : 1 ≤ padicValInt p b := by
      rcases (padicValInt_dvd_iff (p := p) 1 b).mp (by simpa using hpb) with h' | h'
      · exact absurd h' hb0
      · exact h'
    have hv2 : padicValInt p b < 2 := by
      by_contra hcon
      push Not at hcon
      exact hnotsq ((padicValInt_dvd_iff (p := p) 2 b).mpr (Or.inr hcon))
    have hnorm : ‖((b : ℤ) : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
      have h1 := Padic.norm_eq_zpow_neg_valuation (p := p) hbQ
      rw [Padic.valuation_intCast] at h1
      have hv : padicValInt p b = 1 := by omega
      rw [hv] at h1
      simpa using h1
    -- `a` is a unit of `ℤ_[p]`
    have hunit : IsUnit ((a : ℤ_[p])) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) ?_
      rw [← not_lt]
      intro hlt
      exact hpa ((PadicInt.norm_intCast_lt_one_iff).mp hlt)
    let u : ℤ_[p]ˣ := hunit.unit
    have hu : (u : ℚ_[p]) = (a : ℚ_[p]) :=
      congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (IsUnit.unit_spec hunit)
    -- Serre's case `10`
    have hcase : hilbertSym (a : ℚ_[p]) (b : ℚ_[p])
        = (quadraticChar (ZMod p)) (PadicInt.toZMod (u : ℤ_[p])) := by
      have hc := hilbertSym_padic_odd_case10 (p := p) hp2 u hnorm
      rwa [hu] at hc
    have hchi : (quadraticChar (ZMod p)) (PadicInt.toZMod (u : ℤ_[p])) = 1 := by
      rw [← hcase]
      exact h
    have hu0 : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 :=
      (IsUnit.map (PadicInt.toZMod (p := p)) u.isUnit).ne_zero
    obtain ⟨s, hs⟩ := (quadraticChar_one_iff_isSquare hu0).mp hchi
    -- identify `toZMod u` with the residue of `a`
    have huZ : (u : ℤ_[p]) = (a : ℤ_[p]) :=
      Subtype.coe_injective (by simpa using hu)
    rw [huZ] at hs
    have hsa : ((a : ℤ) : ZMod p) = s * s := by simpa using hs
    obtain ⟨t, ht⟩ := ZMod.intCast_surjective s
    refine ⟨t, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ht]
    have hs2 : s ^ 2 = ((a : ℤ) : ZMod p) := by rw [sq, hsa]
    rw [hs2]
    ring

end Pptc.HasseMinkowski
