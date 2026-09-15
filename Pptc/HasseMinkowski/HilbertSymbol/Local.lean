/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.Basic
import Pptc.HasseMinkowski.Prod
import Pptc.HasseMinkowski.RankCriteria
import Pptc.HasseMinkowski.HilbertSymbol.Padic
import Pptc.HasseMinkowski.HilbertSymbol.Real
import Pptc.HasseMinkowski.HilbertSymbol.Two

/-!
# Local Hilbert symbols at the completions of `ℚ`

This file collects the place-by-place facts about the Hilbert symbol `(·,·)_k` for
`k = ℚ_[p]` (and, later, `ℝ`).  The first item is the bilinearity of the symbol in its
first argument, `HasBilinHilbertSym ℚ_[p]`, which makes the generic rank criteria of
`RankCriteria.lean` available at every `p`-adic place.

The two-adic case is imported from `HilbertSymbol/Two.lean`; for odd `p` the result is
`hilbertSym_padic_odd_mul_left`.
-/

open Module QuadraticMap

namespace Pptc.HasseMinkowski

/-! ### Bilinearity of the `p`-adic Hilbert symbol -/

/-- The Hilbert symbol on the `p`-adic numbers is bilinear in its first argument.

For `p = 2` this is `instHasBilinHilbertSym` from `HilbertSymbol/Two.lean`; for odd `p` it
is `hilbertSym_padic_odd_mul_left`. -/
instance instHasBilinHilbertSymPadic (p : ℕ) [Fact p.Prime] : HasBilinHilbertSym ℚ_[p] := by
  by_cases hp : p = 2
  · subst hp
    infer_instance
  · exact ⟨fun {a a' b} => hilbertSym_padic_odd_mul_left hp a a' b⟩

/-! ### The rank-two representation criterion -/

section TwoRepresents

variable {k : Type*} [Field k]

/-- A nonzero vector of the plane `⟨a, b⟩` represents `x` exactly when the ternary form
`⟨a, b, -x⟩` is isotropic.

This is the bridge between representability by a rank-two form and the ternary isotropy
criterion of `RankCriteria.lean`.  The hard case is when the isotropic vector of `⟨a, b, -x⟩`
has last coordinate `0`: then `⟨a, b⟩` is itself isotropic, and since it is nondegenerate it
represents every value. -/
private lemma weightedSumSquares_two_represents_iff_ternary {a b x : k} [Invertible (2 : k)]
    (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) :
    (weightedSumSquares k ![a, b]).represents x ↔
      (weightedSumSquares k ![a, b, -x]).Isotropic := by
  have key2 : ∀ y : Fin 2 → k,
      (weightedSumSquares k ![a, b]) y = a * y 0 ^ 2 + b * y 1 ^ 2 := by
    intro y
    simp [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul, pow_two]
  have key3 : ∀ y : Fin 3 → k,
      (weightedSumSquares k ![a, b, -x]) y =
        a * y 0 ^ 2 + b * y 1 ^ 2 + (-x) * y 2 ^ 2 := by
    intro y
    simp [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul, pow_two]
  constructor
  · rintro ⟨y, _hy, hyQ⟩
    refine ⟨![y 0, y 1, 1], ?_, ?_⟩
    · intro h0
      have h1 : (1 : k) = 0 := by simpa using congr_fun h0 2
      exact one_ne_zero h1
    · rw [key3]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [key2] at hyQ
      linear_combination hyQ
  · rintro ⟨y, hy, hyQ⟩
    rw [key3] at hyQ
    by_cases hy2 : y 2 = 0
    · have hyQ' : a * y 0 ^ 2 + b * y 1 ^ 2 = 0 := by
        have h := hyQ
        rw [hy2] at h
        simpa using h
      have hneq : (![y 0, y 1] : Fin 2 → k) ≠ 0 := by
        intro h0
        apply hy
        funext j
        fin_cases j
        · simpa using congr_fun h0 0
        · simpa using congr_fun h0 1
        · exact hy2
      have hiso : (weightedSumSquares k ![a, b]).Isotropic := by
        refine ⟨![y 0, y 1], hneq, ?_⟩
        rw [key2]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact hyQ'
      have hnd : (weightedSumSquares k ![a, b]).Nondegenerate := by
        let w : Fin 2 → kˣ := ![Units.mk0 a ha, Units.mk0 b hb]
        have hw : (fun i => (w i : k)) = ![a, b] := by
          funext i
          fin_cases i <;> simp [w]
        rw [← hw]
        exact nondegenerate_weightedSumSquares w
      exact represents_of_isotropic_nondegenerate hnd hiso x
    · set z : Fin 2 → k := ![y 0 / y 2, y 1 / y 2] with hz_def
      have hzval : (weightedSumSquares k ![a, b]) z = x := by
        rw [key2]
        simp only [hz_def, Matrix.cons_val_zero, Matrix.cons_val_one]
        have hdiv : a * (y 0 / y 2) ^ 2 + b * (y 1 / y 2) ^ 2 =
            (a * y 0 ^ 2 + b * y 1 ^ 2) / y 2 ^ 2 := by
          field_simp [hy2]
        rw [hdiv]
        have hthis : a * y 0 ^ 2 + b * y 1 ^ 2 = x * y 2 ^ 2 := by
          linear_combination hyQ
        rw [hthis, mul_div_assoc, div_self (pow_ne_zero 2 hy2), mul_one]
      exact ⟨z, fun h0 => by
        rw [h0, map_zero] at hzval
        exact hx hzval.symm, hzval⟩

-- Theorem: the rank-two criterion for a diagonal form with two named weights.
-- `⟨a, b⟩` represents `x ≠ 0` exactly when `(x, -ab) = (a, b)`.
theorem represents_weightedSumSquares_two_iff {a b x : k} [HasBilinHilbertSym k]
    [Invertible (2 : k)] (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) :
    (weightedSumSquares k ![a, b]).represents x ↔
      hilbertSym x (-(a * b)) = hilbertSym a b := by
  rw [weightedSumSquares_two_represents_iff_ternary ha hb hx,
    weightedSumSquares_isotropic_iff_hilbertSym_eq_one a b (-x) ha hb (neg_ne_zero.mpr hx)]
  rw [show -(-x) * a = x * a by ring, show -(-x) * b = x * b by ring]
  rw [hilbertSym_mul_mul (a := a) (b := b) (c := x)]
  exact mul_eq_one_iff_eq_of_signs
    (hilbertSym_eq_one_or_neg_one_of_ne_zero hx (neg_ne_zero.mpr (mul_ne_zero ha hb)))
    (hilbertSym_eq_one_or_neg_one_of_ne_zero ha hb)

end TwoRepresents

/-! ### Nontriviality of `x ↦ (x, c)` for a nonsquare `c`

For a nonsquare `c ≠ 0` the character `x ↦ (x, c)_k` is nontrivial.  Over `ℝ` this is
immediate from `hilbertSym_real_eq`; over `ℚ_[p]` it is read off Serre's closed formulas,
using the decomposition `c = p ^ α · u`. -/

section Nontriviality

-- Theorem: over `ℝ`, a negative `c` has `(-1, c)_ℝ = -1`.
theorem exists_hilbertSym_eq_neg_one_real {c : ℝ} (hc : c < 0) :
    ∃ x : ℝ, x ≠ 0 ∧ hilbertSym x c = -1 := by
  refine ⟨-1, by norm_num, ?_⟩
  rw [hilbertSym_real_eq (by norm_num) (ne_of_lt hc)]
  have h : ¬ (0 < (-1 : ℝ) ∨ 0 < c) := by
    rintro (h | h) <;> linarith
  rw [if_neg h]

end Nontriviality

section OddPrime

variable {p : ℕ} [Fact p.Prime]

-- Theorem: `p` is nonzero as an element of `ℚ_[p]`.
private lemma padic_p_ne_zero_local : (p : ℚ_[p]) ≠ 0 := by
  intro h
  have hnorm : ‖(p : ℚ_[p])‖ = 0 := by rw [h, norm_zero]
  rw [Padic.norm_p] at hnorm
  exact (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))) hnorm

-- Theorem: the underlying `p`-adic number of `padicUnit a ha` is `a * p ^ (-(a.valuation))`.
private lemma coe_padicUnit_local (a : ℚ_[p]) (ha : a ≠ 0) :
    ((padicUnit a ha : ℤ_[p]) : ℚ_[p]) = a * (p : ℚ_[p]) ^ (-(a.valuation)) := by
  rw [padicUnit]
  exact congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) (IsUnit.unit_spec _)

-- Theorem: every nonzero `p`-adic number is `p ^ a.valuation` times its unit part.
private lemma padicUnit_spec_local (a : ℚ_[p]) (ha : a ≠ 0) :
    a = (p : ℚ_[p]) ^ a.valuation * ((padicUnit a ha : ℤ_[p]) : ℚ_[p]) := by
  have hp0 := padic_p_ne_zero_local (p := p)
  rw [coe_padicUnit_local]
  calc a = a * 1 := (mul_one a).symm
    _ = a * ((p : ℚ_[p]) ^ a.valuation * (p : ℚ_[p]) ^ (-(a.valuation))) := by
          rw [← zpow_add₀ hp0, add_neg_cancel, zpow_zero]
    _ = (p : ℚ_[p]) ^ a.valuation * (a * (p : ℚ_[p]) ^ (-(a.valuation))) := by ring

-- Theorem: a nonzero element of valuation `0` is its own unit part.
private lemma coe_padicUnit_of_valuation_zero (a : ℚ_[p]) (ha : a ≠ 0) (h0 : a.valuation = 0) :
    ((padicUnit a ha : ℤ_[p]) : ℚ_[p]) = a := by
  rw [coe_padicUnit_local, h0, neg_zero, zpow_zero, mul_one]

-- Theorem: the unit part of a natural number of valuation `0` is that natural number.
private lemma padicUnit_eq_natCast_of_valuation_zero {a : ℚ_[p]} (ha : a ≠ 0)
    (h0 : a.valuation = 0) {n : ℕ} (hn : a = (n : ℚ_[p])) :
    (padicUnit a ha : ℤ_[p]) = (n : ℤ_[p]) := by
  apply PadicInt.ext
  rw [coe_padicUnit_of_valuation_zero a ha h0]
  simpa using hn

-- Theorem: a unit (valuation `0`) with quadratic character `-1` pairs to `-1` against an
-- element of odd valuation.
private lemma hilbertSym_padic_odd_unit_of_neg_valuation (hp : p ≠ 2) {x c : ℚ_[p]}
    (hx : x ≠ 0) (hc : c ≠ 0) (hx0 : x.valuation = 0) (hβ : ¬ Even c.valuation)
    (hchi : (quadraticChar (ZMod p))
      (PadicInt.toZMod (padicUnit x hx : ℤ_[p])) = -1) :
    hilbertSym x c = -1 := by
  rw [hilbertSym_padic_odd_eq hp hx hc, hx0]
  simp only [zero_mul]
  rw [show parityPow ((quadraticChar (ZMod p)) (-1 : ZMod p)) 0 = 1 by
        rw [parityPow, if_pos ⟨0, by ring⟩],
      show parityPow ((quadraticChar (ZMod p))
          (PadicInt.toZMod (padicUnit x hx : ℤ_[p]))) c.valuation
          = (quadraticChar (ZMod p)) (PadicInt.toZMod (padicUnit x hx : ℤ_[p])) by
        rw [parityPow, if_neg hβ],
      show parityPow ((quadraticChar (ZMod p))
          (PadicInt.toZMod (padicUnit c hc : ℤ_[p]))) 0 = 1 by
        rw [parityPow, if_pos ⟨0, by ring⟩],
      hchi]
  norm_num

-- Theorem: for even valuation, `(p, c)_p = -1` when the unit part of `c` is a quadratic
-- non-residue.
private lemma hilbertSym_padic_odd_p_of_nonresidue (hp : p ≠ 2) {c : ℚ_[p]} (hc : c ≠ 0)
    (hβ : Even c.valuation)
    (hchi : (quadraticChar (ZMod p))
      (PadicInt.toZMod (padicUnit c hc : ℤ_[p])) = -1) :
    hilbertSym (p : ℚ_[p]) c = -1 := by
  have hx := padic_p_ne_zero_local (p := p)
  have hup : PadicInt.toZMod (padicUnit (p : ℚ_[p]) hx : ℤ_[p]) = 1 := by
    have hcoe : ((padicUnit (p : ℚ_[p]) hx : ℤ_[p]) : ℚ_[p]) = 1 := by
      rw [coe_padicUnit_local, Padic.valuation_p]
      rw [show (-(1 : ℤ)) = -1 by norm_num, zpow_neg_one]
      exact mul_inv_cancel₀ hx
    have hone : (padicUnit (p : ℚ_[p]) hx : ℤ_[p]) = 1 := by
      apply PadicInt.ext
      rw [hcoe]
      simp
    rw [hone, map_one]
  rw [hilbertSym_padic_odd_eq hp hx hc, Padic.valuation_p]
  simp only [one_mul]
  rw [hup,
    show parityPow ((quadraticChar (ZMod p)) (-1 : ZMod p)) c.valuation = 1 by
      rw [parityPow, if_pos hβ],
    show parityPow ((quadraticChar (ZMod p)) (1 : ZMod p)) c.valuation = 1 by
      rw [map_one, parityPow, if_pos hβ],
    show parityPow ((quadraticChar (ZMod p))
        (PadicInt.toZMod (padicUnit c hc : ℤ_[p]))) 1
        = (quadraticChar (ZMod p)) (PadicInt.toZMod (padicUnit c hc : ℤ_[p])) by
      rw [parityPow, if_neg (show ¬ Even (1 : ℤ) by norm_num)],
    hchi]
  norm_num

-- Theorem: for odd `p` and nonsquare `c ≠ 0`, some `x` has `(x, c)_p = -1`.
private theorem exists_hilbertSym_eq_neg_one_odd (hp : p ≠ 2) {c : ℚ_[p]}
    (hc : c ≠ 0) (hcsq : ¬ IsSquare c) :
    ∃ x : ℚ_[p], x ≠ 0 ∧ hilbertSym x c = -1 := by
  by_cases hβ : Even c.valuation
  · -- even valuation: use `x = p`, the unit part of `c` is a non-residue
    refine ⟨(p : ℚ_[p]), padic_p_ne_zero_local (p := p), ?_⟩
    refine hilbertSym_padic_odd_p_of_nonresidue hp hc hβ ?_
    rw [quadraticChar_neg_one_iff_not_isSquare]
    intro hmod
    have hnd : ¬ (p : ℤ_[p]) ∣ (padicUnit c hc : ℤ_[p]) := by
      rw [PadicInt.p_dvd_iff_toZMod_eq_zero]
      exact (IsUnit.map (PadicInt.toZMod (p := p)) (padicUnit c hc).isUnit).ne_zero
    obtain ⟨z, hz⟩ := PadicInt.isSquare_of_zmod hp hnd hmod
    obtain ⟨k, hk⟩ := hβ
    have hv : ((padicUnit c hc : ℤ_[p]) : ℚ_[p]) = (z : ℚ_[p]) ^ 2 := by
      rw [hz]; push_cast; ring
    have hpβ : (p : ℚ_[p]) ^ c.valuation = ((p : ℚ_[p]) ^ k) ^ 2 := by
      rw [hk, pow_two, ← zpow_add₀ (padic_p_ne_zero_local (p := p))]
    refine (hcsq ⟨(z : ℚ_[p]) * (p : ℚ_[p]) ^ k, ?_⟩)
    rw [padicUnit_spec_local c hc, hpβ, hv]
    ring
  · -- odd valuation: use a quadratic non-residue `x` of valuation `0`
    have hring : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      exact hp
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) hring
    let n : ℕ := (a : ZMod p).val
    have hnZ : (n : ZMod p) = (a : ZMod p) := ZMod.natCast_zmod_val _
    have hnd : ¬ p ∣ n := by
      intro hd
      have h0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hd
      rw [hnZ] at h0
      exact a.ne_zero h0
    let x : ℚ_[p] := (n : ℚ_[p])
    have hx : x ≠ 0 := by
      intro h
      have hn0 : n = 0 := by simpa [x] using h
      exact hnd (by rw [hn0]; exact dvd_zero p)
    have hxval : x.valuation = 0 := by
      change (n : ℚ_[p]).valuation = 0
      rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd hnd]
      norm_num
    refine ⟨x, hx, ?_⟩
    refine hilbertSym_padic_odd_unit_of_neg_valuation hp hx hc hxval hβ ?_
    have hunit : (padicUnit x hx : ℤ_[p]) = (n : ℤ_[p]) :=
      padicUnit_eq_natCast_of_valuation_zero (a := x) (n := n) hx hxval rfl
    rw [hunit, map_natCast, hnZ]
    exact ha

end OddPrime

section TwoAdic

-- Theorem: every nonzero `2`-adic number is `2 ^ a.valuation` times its unit part.
private lemma twoAdicUnit_spec_local (a : ℚ_[2]) (ha : a ≠ 0) :
    a = (2 : ℚ_[2]) ^ a.valuation * ((twoAdicUnit a ha : ℤ_[2]) : ℚ_[2]) := by
  simpa [twoAdicUnit] using padicUnit_spec_local (p := 2) a ha

-- Theorem: `(5, c)_2` is the parity of `c.valuation` (`5 ≡ 1 (mod 4)`, `5 ≢ ±1 (mod 8)`).
private lemma hilbertSym_two_five_eq {c : ℚ_[2]} (hc : c ≠ 0) :
    hilbertSym (5 : ℚ_[2]) c = parityPow (-1) c.valuation := by
  have hx : (5 : ℚ_[2]) ≠ 0 := by norm_num
  have hval : ((5 : ℚ_[2])).valuation = 0 := by
    rw [show (5 : ℚ_[2]) = ((5 : ℕ) : ℚ_[2]) by norm_num, Padic.valuation_natCast,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 5)]
    norm_num
  have hunit : (twoAdicUnit (5 : ℚ_[2]) hx : ℤ_[2]) = ((5 : ℕ) : ℤ_[2]) :=
    padicUnit_eq_natCast_of_valuation_zero hx hval rfl
  have heps : eps (twoAdicUnit (5 : ℚ_[2]) hx) = 0 := by
    have h : (twoAdicUnit (5 : ℚ_[2]) hx : ℤ_[2]).toZModPow 2 = 1 := by
      rw [hunit, map_natCast]
      decide
    rw [eps, if_pos h]
  have homg : omg (twoAdicUnit (5 : ℚ_[2]) hx) = 1 := by
    have h : ¬ ((twoAdicUnit (5 : ℚ_[2]) hx : ℤ_[2]).toZModPow 3 = 1 ∨
        (twoAdicUnit (5 : ℚ_[2]) hx : ℤ_[2]).toZModPow 3 = 7) := by
      rw [hunit, map_natCast]
      decide
    rw [omg, if_neg h]
  rw [hilbertSym_padic_two_eq hx hc, hval, heps, homg]
  simp only [zero_mul, mul_one, zero_add]

-- Theorem: `(7, c)_2` is the `ε` character of the unit part of `c` (`7 ≡ 3 (mod 4)`,
-- `7 ≡ -1 (mod 8)`).
private lemma hilbertSym_two_seven_eq {c : ℚ_[2]} (hc : c ≠ 0) :
    hilbertSym (7 : ℚ_[2]) c = parityPow (-1) (eps (twoAdicUnit c hc)) := by
  have hx : (7 : ℚ_[2]) ≠ 0 := by norm_num
  have hval : ((7 : ℚ_[2])).valuation = 0 := by
    rw [show (7 : ℚ_[2]) = ((7 : ℕ) : ℚ_[2]) by norm_num, Padic.valuation_natCast,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 7)]
    norm_num
  have hunit : (twoAdicUnit (7 : ℚ_[2]) hx : ℤ_[2]) = ((7 : ℕ) : ℤ_[2]) :=
    padicUnit_eq_natCast_of_valuation_zero hx hval rfl
  have heps : eps (twoAdicUnit (7 : ℚ_[2]) hx) = 1 := by
    have h : ¬ ((twoAdicUnit (7 : ℚ_[2]) hx : ℤ_[2]).toZModPow 2 = 1) := by
      rw [hunit, map_natCast]
      decide
    rw [eps, if_neg h]
  have homg : omg (twoAdicUnit (7 : ℚ_[2]) hx) = 0 := by
    have h : (twoAdicUnit (7 : ℚ_[2]) hx : ℤ_[2]).toZModPow 3 = 7 := by
      rw [hunit, map_natCast]
      decide
    rw [omg, if_pos (Or.inr h)]
  rw [hilbertSym_padic_two_eq hx hc, hval, heps, homg]
  simp only [one_mul, zero_mul, mul_zero, add_zero]

-- Theorem: `(2, c)_2` is the `ω` character of the unit part of `c`.
private lemma hilbertSym_two_two_eq {c : ℚ_[2]} (hc : c ≠ 0) :
    hilbertSym (2 : ℚ_[2]) c = parityPow (-1) (omg (twoAdicUnit c hc)) := by
  have hx : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hval : ((2 : ℚ_[2])).valuation = 1 := Padic.valuation_p (p := 2)
  have hunit : (twoAdicUnit (2 : ℚ_[2]) hx : ℤ_[2]) = 1 := by
    apply PadicInt.ext
    rw [twoAdicUnit, coe_padicUnit_local (p := 2), hval]
    rw [show (-(1 : ℤ)) = -1 by norm_num, zpow_neg_one]
    simp
  have heps : eps (twoAdicUnit (2 : ℚ_[2]) hx) = 0 := by
    have h : (twoAdicUnit (2 : ℚ_[2]) hx : ℤ_[2]).toZModPow 2 = 1 := by
      rw [hunit, map_one]
    rw [eps, if_pos h]
  have homg : omg (twoAdicUnit (2 : ℚ_[2]) hx) = 0 := by
    have h : (twoAdicUnit (2 : ℚ_[2]) hx : ℤ_[2]).toZModPow 3 = 1 := by
      rw [hunit, map_one]
    rw [omg, if_pos (Or.inl h)]
  rw [hilbertSym_padic_two_eq hx hc, hval, heps, homg]
  simp only [zero_mul, one_mul, mul_zero, zero_add, add_zero]

-- Theorem: for even valuation and nonsquare `c`, if the `ε` character of the unit part of
-- `c` vanishes then the `ω` character does not.
private lemma omg_eq_one_of_eps_eq_zero {c : ℚ_[2]} (hc : c ≠ 0)
    (hcsq : ¬ IsSquare c) (hβ : Even c.valuation)
    (hε0 : eps (twoAdicUnit c hc) = 0) : omg (twoAdicUnit c hc) = 1 := by
  have hpow2 : (twoAdicUnit c hc : ℤ_[2]).toZModPow 2 = 1 := by
    by_contra h
    rw [show eps (twoAdicUnit c hc) = 1 by rw [eps, if_neg h]] at hε0
    exact one_ne_zero hε0
  have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (twoAdicUnit c hc : ℤ_[2]) := by
    rw [PadicInt.p_dvd_iff_toZMod_eq_zero]
    exact (IsUnit.map (PadicInt.toZMod (p := 2)) (twoAdicUnit c hc).isUnit).ne_zero
  have hnot : ¬ ((twoAdicUnit c hc : ℤ_[2]).toZModPow 3 = 1 ∨
      (twoAdicUnit c hc : ℤ_[2]).toZModPow 3 = 7) := by
    rintro (h3 | h3)
    · obtain ⟨z, hz⟩ := PadicInt.isSquare_of_zmodPow hnd ⟨1, by rw [h3]; ring⟩
      apply hcsq
      obtain ⟨k, hk⟩ := hβ
      have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
      have hpβ : (2 : ℚ_[2]) ^ c.valuation = ((2 : ℚ_[2]) ^ k) ^ 2 := by
        rw [hk, pow_two, ← zpow_add₀ h2]
      have huval : ((twoAdicUnit c hc : ℤ_[2]) : ℚ_[2]) = (z : ℚ_[2]) ^ 2 := by
        rw [hz]; push_cast; ring
      refine ⟨(2 : ℚ_[2]) ^ k * (z : ℚ_[2]), ?_⟩
      rw [twoAdicUnit_spec_local c hc, hpβ, huval]
      ring
    · have hcast : (twoAdicUnit c hc : ℤ_[2]).toZModPow 2
          = ZMod.cast ((twoAdicUnit c hc : ℤ_[2]).toZModPow 3) :=
        (PadicInt.cast_toZModPow 2 3 (by norm_num) (twoAdicUnit c hc : ℤ_[2])).symm
      rw [h3, hpow2] at hcast
      exact absurd hcast (by decide)
  rw [omg, if_neg hnot]

-- Theorem: for `p = 2` and nonsquare `c ≠ 0`, some `x` has `(x, c)_2 = -1`.
private theorem exists_hilbertSym_eq_neg_one_two {c : ℚ_[2]} (hc : c ≠ 0)
    (hcsq : ¬ IsSquare c) : ∃ x : ℚ_[2], x ≠ 0 ∧ hilbertSym x c = -1 := by
  by_cases hβ : Even c.valuation
  · by_cases hε : eps (twoAdicUnit c hc) = 1
    · refine ⟨7, by norm_num, ?_⟩
      rw [hilbertSym_two_seven_eq hc, hε]
      rw [show parityPow (-1) 1 = -1 by rw [parityPow, if_neg (by norm_num)]]
    · have hε0 : eps (twoAdicUnit c hc) = 0 := by
        by_cases h : (twoAdicUnit c hc : ℤ_[2]).toZModPow 2 = 1
        · rw [eps, if_pos h]
        · exact absurd (by rw [eps, if_neg h]) hε
      have hω : omg (twoAdicUnit c hc) = 1 := omg_eq_one_of_eps_eq_zero hc hcsq hβ hε0
      refine ⟨2, by norm_num, ?_⟩
      rw [hilbertSym_two_two_eq hc, hω]
      rw [show parityPow (-1) 1 = -1 by rw [parityPow, if_neg (by norm_num)]]
  · refine ⟨5, by norm_num, ?_⟩
    rw [hilbertSym_two_five_eq hc]
    rw [show parityPow (-1) c.valuation = -1 by rw [parityPow, if_neg hβ]]

end TwoAdic

/-! ### Nontriviality of the local Hilbert symbol character -/

-- Theorem: for a nonsquare nonzero `c` over `ℚ_[p]`, the character `x ↦ (x, c)_p` is
-- nontrivial: some `x` has `(x, c)_p = -1`.
theorem exists_hilbertSym_eq_neg_one_padic (p : ℕ) [Fact p.Prime] {c : ℚ_[p]}
    (hc : c ≠ 0) (hcsq : ¬ IsSquare c) :
    ∃ x : ℚ_[p], x ≠ 0 ∧ hilbertSym x c = -1 := by
  by_cases hp : p = 2
  · subst hp
    exact exists_hilbertSym_eq_neg_one_two hc hcsq
  · exact exists_hilbertSym_eq_neg_one_odd hp hc hcsq

/-! ### Two prescribed Hilbert symbols (WP2.4) and the pair of non-squares (WP2.5) -/

section Prescribed

-- Theorem: a square in `ℚ_[p]` has even valuation.
private lemma even_valuation_of_isSquare {p : ℕ} [Fact p.Prime] {x : ℚ_[p]}
    (h : IsSquare x) : Even x.valuation := by
  obtain ⟨y, hy⟩ := h
  rw [hy, ← pow_two, Padic.valuation_pow]
  exact ⟨y.valuation, by ring⟩

-- Theorem: an element of odd valuation is not a square.
private lemma not_isSquare_of_odd_valuation {p : ℕ} [Fact p.Prime] {x : ℚ_[p]}
    (h : ¬ Even x.valuation) : ¬ IsSquare x :=
  fun hs => h (even_valuation_of_isSquare hs)

-- Theorem: over `ℚ_[p]` there is a unit (element of valuation `0`) that is not a square.
private lemma exists_nonsquare_unit (p : ℕ) [Fact p.Prime] :
    ∃ u : ℚ_[p], u ≠ 0 ∧ u.valuation = 0 ∧ ¬ IsSquare u := by
  by_cases hp : p = 2
  · subst hp
    refine ⟨(7 : ℚ_[2]), by norm_num, ?_, ?_⟩
    · rw [show (7 : ℚ_[2]) = ((7 : ℕ) : ℚ_[2]) by norm_num, Padic.valuation_natCast,
        padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 7)]
      norm_num
    · intro hs
      have h7 : (7 : ℚ_[2]) ≠ 0 := by norm_num
      have h1 : hilbertSym (7 : ℚ_[2]) (7 : ℚ_[2]) = 1 := by
        obtain ⟨y, hy⟩ := hs
        have hy_ne : y ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hy
          exact h7 hy
        nth_rewrite 1 [hy]
        rw [← pow_two]
        exact hilbertSym_sq_left hy_ne h7
      have h2 : hilbertSym (7 : ℚ_[2]) (7 : ℚ_[2]) = -1 := by
        have hval7 : ((7 : ℚ_[2])).valuation = 0 := by
          rw [show (7 : ℚ_[2]) = ((7 : ℕ) : ℚ_[2]) by norm_num, Padic.valuation_natCast,
            padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 7)]
          norm_num
        have hunit : (twoAdicUnit (7 : ℚ_[2]) h7 : ℤ_[2]) = ((7 : ℕ) : ℤ_[2]) :=
          padicUnit_eq_natCast_of_valuation_zero h7 hval7 rfl
        have heps : eps (twoAdicUnit (7 : ℚ_[2]) h7) = 1 := by
          have h : ¬ ((twoAdicUnit (7 : ℚ_[2]) h7 : ℤ_[2]).toZModPow 2 = 1) := by
            rw [hunit, map_natCast]
            decide
          rw [eps, if_neg h]
        rw [hilbertSym_two_seven_eq h7, heps]
        rw [show parityPow (-1) 1 = -1 by rw [parityPow, if_neg (by norm_num)]]
      linarith
  · -- odd `p`: lift a quadratic non-residue modulo `p`
    have hring : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) hring
    let n : ℕ := (a : ZMod p).val
    have hnZ : (n : ZMod p) = (a : ZMod p) := ZMod.natCast_zmod_val _
    have hnd : ¬ p ∣ n := by
      intro hd
      have h0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hd
      rw [hnZ] at h0
      exact a.ne_zero h0
    have hn0 : n ≠ 0 := fun h => hnd (by rw [h]; exact dvd_zero p)
    have huval : ((n : ℚ_[p])).valuation = 0 := by
      rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd hnd]
      norm_num
    refine ⟨(n : ℚ_[p]), Nat.cast_ne_zero.mpr hn0, huval, ?_⟩
    intro hs
    obtain ⟨y, hy⟩ := hs
    have hy_ne : y ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hy
      exact (Nat.cast_ne_zero.mpr hn0) hy
    have hyval : y.valuation = 0 := by
      have h : (y * y).valuation = 0 := by rw [← hy]; exact huval
      rw [← pow_two, Padic.valuation_pow] at h
      omega
    have hynorm : ‖y‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation hy_ne, hyval, neg_zero, zpow_zero]
    let Y : ℤ_[p] := ⟨y, le_of_eq hynorm⟩
    have hYcoe : ((Y : ℤ_[p]) : ℚ_[p]) = y := rfl
    have hYsq : Y * Y = (n : ℤ_[p]) := by
      apply PadicInt.ext
      rw [PadicInt.coe_mul, hYcoe, ← hy]
      simp
    have hnsqZ : IsSquare ((n : ZMod p)) := by
      refine ⟨PadicInt.toZMod (p := p) Y, ?_⟩
      have h := congrArg (PadicInt.toZMod (p := p)) hYsq
      simp only [map_mul, map_natCast] at h
      rw [h]
    have hchi1 : (quadraticChar (ZMod p)) ((n : ZMod p)) = 1 :=
      (quadraticChar_one_iff_isSquare (by rw [hnZ]; exact a.ne_zero)).mpr hnsqZ
    rw [hnZ] at hchi1
    linarith [ha, hchi1]

-- Theorem: for a nonsquare `c` over `ℚ_[p]` there is a nonsquare `c₂` with `c * c₂` also
-- nonsquare.
theorem exists_not_isSquare_and_not_isSquare_mul (p : ℕ) [Fact p.Prime] {c : ℚ_[p]}
    (hc : c ≠ 0) (hcsq : ¬ IsSquare c) :
    ∃ c₂ : ℚ_[p], ¬ IsSquare c₂ ∧ ¬ IsSquare (c * c₂) := by
  have _ := hcsq
  by_cases hβ : Even c.valuation
  · refine ⟨(p : ℚ_[p]), ?_, ?_⟩
    · exact not_isSquare_of_odd_valuation (by rw [Padic.valuation_p]; norm_num)
    · apply not_isSquare_of_odd_valuation
      rw [Padic.valuation_mul hc (padic_p_ne_zero_local (p := p)), Padic.valuation_p]
      intro h
      obtain ⟨k, hk⟩ := hβ
      obtain ⟨m, hm⟩ := h
      omega
  · obtain ⟨u, hu_ne, huval, hu⟩ := exists_nonsquare_unit p
    refine ⟨u, hu, ?_⟩
    apply not_isSquare_of_odd_valuation
    rw [Padic.valuation_mul hc hu_ne, huval, add_zero]
    exact hβ

-- Theorem: two prescribed values `e₁, e₂ ∈ {±1}` of the Hilbert symbol against `c₁`,
-- `c₂` can be realised by a single nonzero `x`, when `c₁`, `c₂`, `c₁ c₂` are all nonsquares.
theorem exists_hilbertSym_two_prescribed {k : Type*} [Field k] [HasBilinHilbertSym k]
    {c₁ c₂ : k} (h1 : c₁ ≠ 0) (h2 : c₂ ≠ 0)
    (hc1 : ¬ IsSquare c₁) (hc2 : ¬ IsSquare c₂) (hc12 : ¬ IsSquare (c₁ * c₂))
    (hnd : ∀ c : k, c ≠ 0 → ¬ IsSquare c → ∃ x : k, x ≠ 0 ∧ hilbertSym x c = -1)
    {e₁ e₂ : ℤ} (he1 : e₁ = 1 ∨ e₁ = -1) (he2 : e₂ = 1 ∨ e₂ = -1) :
    ∃ x : k, x ≠ 0 ∧ hilbertSym x c₁ = e₁ ∧ hilbertSym x c₂ = e₂ := by
  obtain ⟨y, hy_ne, hy⟩ := hnd c₁ h1 hc1
  obtain ⟨w, hw_ne, hw⟩ := hnd c₂ h2 hc2
  obtain ⟨z, hz_ne, hz⟩ := hnd (c₁ * c₂) (mul_ne_zero h1 h2) hc12
  have hzprod : hilbertSym z c₁ * hilbertSym z c₂ = -1 := by
    rw [← HasBilinHilbertSym.mul_right_eq, hz]
  have hs_or : hilbertSym y c₂ = 1 ∨ hilbertSym y c₂ = -1 :=
    hilbertSym_eq_one_or_neg_one_of_ne_zero hy_ne h2
  have ht_or : hilbertSym w c₁ = 1 ∨ hilbertSym w c₁ = -1 :=
    hilbertSym_eq_one_or_neg_one_of_ne_zero hw_ne h1
  have ha_or : hilbertSym z c₁ = 1 ∨ hilbertSym z c₁ = -1 :=
    hilbertSym_eq_one_or_neg_one_of_ne_zero hz_ne h1
  rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl
  · refine ⟨w * w, mul_ne_zero hw_ne hw_ne, ?_, ?_⟩
    · rw [HasBilinHilbertSym.mul_left_eq]
      rcases ht_or with ht | ht <;> rw [ht] <;> norm_num
    · rw [HasBilinHilbertSym.mul_left_eq, hw]; norm_num
  · by_cases ht1 : hilbertSym w c₁ = 1
    · exact ⟨w, hw_ne, ht1, hw⟩
    · have ht' : hilbertSym w c₁ = -1 := by
        rcases ht_or with h | h
        · exact absurd h ht1
        · exact h
      by_cases hs1 : hilbertSym y c₂ = 1
      · refine ⟨y * w, mul_ne_zero hy_ne hw_ne, ?_, ?_⟩
        · rw [HasBilinHilbertSym.mul_left_eq, hy, ht']; norm_num
        · rw [HasBilinHilbertSym.mul_left_eq, hs1, hw]; norm_num
      · have hs' : hilbertSym y c₂ = -1 := by
          rcases hs_or with h | h
          · exact absurd h hs1
          · exact h
        rcases ha_or with ha | ha
        · have hzb : hilbertSym z c₂ = -1 := by
            have h := hzprod; rw [ha] at h; linarith
          exact ⟨z, hz_ne, ha, hzb⟩
        · have hzb : hilbertSym z c₂ = 1 := by
            have h := hzprod; rw [ha] at h; linarith
          refine ⟨y * z, mul_ne_zero hy_ne hz_ne, ?_, ?_⟩
          · rw [HasBilinHilbertSym.mul_left_eq, hy, ha]; norm_num
          · rw [HasBilinHilbertSym.mul_left_eq, hs', hzb]; norm_num
  · by_cases hs1 : hilbertSym y c₂ = 1
    · exact ⟨y, hy_ne, hy, hs1⟩
    · have hs' : hilbertSym y c₂ = -1 := by
        rcases hs_or with h | h
        · exact absurd h hs1
        · exact h
      by_cases ht1 : hilbertSym w c₁ = 1
      · refine ⟨y * w, mul_ne_zero hy_ne hw_ne, ?_, ?_⟩
        · rw [HasBilinHilbertSym.mul_left_eq, hy, ht1]; norm_num
        · rw [HasBilinHilbertSym.mul_left_eq, hs', hw]; norm_num
      · have ht' : hilbertSym w c₁ = -1 := by
          rcases ht_or with h | h
          · exact absurd h ht1
          · exact h
        rcases ha_or with ha | ha
        · have hzb : hilbertSym z c₂ = -1 := by
            have h := hzprod; rw [ha] at h; linarith
          refine ⟨y * z, mul_ne_zero hy_ne hz_ne, ?_, ?_⟩
          · rw [HasBilinHilbertSym.mul_left_eq, hy, ha]; norm_num
          · rw [HasBilinHilbertSym.mul_left_eq, hs', hzb]; norm_num
        · have hzb : hilbertSym z c₂ = 1 := by
            have h := hzprod; rw [ha] at h; linarith
          exact ⟨z, hz_ne, ha, hzb⟩
  · by_cases hs1 : hilbertSym y c₂ = -1
    · exact ⟨y, hy_ne, hy, hs1⟩
    · have hs' : hilbertSym y c₂ = 1 := by
        rcases hs_or with h | h
        · exact h
        · exact absurd h hs1
      by_cases ht1 : hilbertSym w c₁ = -1
      · exact ⟨w, hw_ne, ht1, hw⟩
      · have ht' : hilbertSym w c₁ = 1 := by
          rcases ht_or with h | h
          · exact h
          · exact absurd h ht1
        refine ⟨y * w, mul_ne_zero hy_ne hw_ne, ?_, ?_⟩
        · rw [HasBilinHilbertSym.mul_left_eq, hy, ht']; norm_num
        · rw [HasBilinHilbertSym.mul_left_eq, hs', hw]; norm_num

end Prescribed

end Pptc.HasseMinkowski
