import Pptc.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Separable

open Polynomial

namespace Pconstructible

/-! ### Separability is free for the degree-7 problem

The `s ≥ 2` theorem `root_Pconstructible_of_two_conjugate_pairs` currently assumes
`q.Separable`, because the spectral identity that produces the Tschirnhaus map needs seven
distinct roots.  This file removes that hypothesis: a non-separable polynomial of degree at
most `7` has a repeated root, so its gcd with its derivative is nonconstant, and every real
root is a root of one of two polynomials of degree at most `6` (the gcd itself, or the exact
quotient of `q` by its monic normalization).  Both have P-constructible coefficients, so the
sextic engine `root_Pconstructible_le_six_coeffs` finishes.

The work is the coefficient constructibility of `gcd` and of division with remainder by a
monic polynomial, which is what the Euclidean algorithm is built from. -/

-- Theorem: the constant polynomial `C c` has P-constructible coefficients whenever `c` is
-- P-constructible.
theorem coeff_C_Pconstructible {c : ℝ} (hc : PConstructible c) (i : ℕ) :
    PConstructible ((Polynomial.C c).coeff i) := by
  rw [Polynomial.coeff_C]
  split_ifs with h
  · exact hc
  · exact zero_Pconstructible

-- Theorem: multiplying by `C c` with `c` P-constructible preserves coefficient
-- P-constructibility.
theorem C_mul_coeff_Pconstructible {c : ℝ} (hc : PConstructible c) {p : Polynomial ℝ}
    (hp : ∀ k, PConstructible (p.coeff k)) (i : ℕ) :
    PConstructible ((Polynomial.C c * p).coeff i) := by
  rw [Polynomial.coeff_C_mul]
  exact PConstructible.mul hc (hp i)

-- Theorem: a product of polynomials all of whose coefficients are P-constructible again
-- has P-constructible coefficients.
theorem coeff_mul_Pconstructible {p q : Polynomial ℝ}
    (hp : ∀ i, PConstructible (p.coeff i)) (hq : ∀ i, PConstructible (q.coeff i))
    (n : ℕ) : PConstructible ((p * q).coeff n) := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun x _ => ?_)
  exact PConstructible.mul (hp x.1) (hq x.2)

-- Theorem: if `d` is monic with P-constructible coefficients, then both the quotient and
-- the remainder of any P-constructible `p` by `d` have P-constructible coefficients.
--
-- The proof is strong induction on `p.natDegree`.  In the recursive step one removes the
-- leading term of `p` with `z = C (leadingCoeff p) * X ^ (natDegree p - natDegree d)`, so
-- that `p' = p - d * z` has strictly smaller degree; the quotient and remainder of `p` are
-- then `z + p' /ₘ d` and `p' %ₘ d` by `div_modByMonic_unique`.  The case `d = 1` is handled
-- separately because then `p'` can equal `0` without the degree dropping.
theorem divModByMonic_coeff_Pconstructible {d : Polynomial ℝ} (hd : d.Monic)
    (hdc : ∀ i, PConstructible (d.coeff i)) :
    ∀ p, (∀ i, PConstructible (p.coeff i)) →
      (∀ i, PConstructible ((p /ₘ d).coeff i)) ∧
      (∀ i, PConstructible ((p %ₘ d).coeff i)) := by
  by_cases hd1 : d = 1
  · subst hd1
    intro p hp
    refine ⟨?_, ?_⟩
    · simpa using hp
    · intro i
      rw [Polynomial.modByMonic_one, Polynomial.coeff_zero]
      exact zero_Pconstructible
  · have hdne : d ≠ 0 := hd.ne_zero
    have hdpos : 0 < d.natDegree := by
      rcases Nat.eq_zero_or_pos d.natDegree with h | h
      · exact absurd (Polynomial.eq_one_of_monic_natDegree_zero hd h) hd1
      · exact h
    have hddegpos : (0 : WithBot ℕ) < d.degree := by
      rw [Polynomial.degree_eq_natDegree hdne]
      exact WithBot.coe_lt_coe.mpr hdpos
    intro p hp
    suffices H : ∀ n, ∀ p, p.natDegree = n → (∀ i, PConstructible (p.coeff i)) →
        (∀ i, PConstructible ((p /ₘ d).coeff i)) ∧
        (∀ i, PConstructible ((p %ₘ d).coeff i)) from H p.natDegree p rfl hp
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hpdeg hp
      by_cases hlt : p.degree < d.degree
      · have hdiv0 : p /ₘ d = 0 := (Polynomial.divByMonic_eq_zero_iff hd).mpr hlt
        have hmodp : p %ₘ d = p := (Polynomial.modByMonic_eq_self_iff hd).mpr hlt
        exact ⟨fun i => by rw [hdiv0, Polynomial.coeff_zero]; exact zero_Pconstructible,
          fun i => by rw [hmodp]; exact hp i⟩
      · have hge : d.degree ≤ p.degree := not_lt.mp hlt
        have hpdegpos : (0 : WithBot ℕ) < p.degree := lt_of_lt_of_le hddegpos hge
        have hpne : p ≠ 0 := by
          intro h0
          rw [h0, Polynomial.degree_zero] at hpdegpos
          exact absurd hpdegpos (not_lt_of_ge bot_le)
        set z : Polynomial ℝ :=
          Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - d.natDegree)
          with hzdef
        set pp : Polynomial ℝ := p - d * z with hppdef
        have hzcoeff : ∀ i, PConstructible (z.coeff i) := by
          intro i
          rw [hzdef, Polynomial.coeff_C_mul_X_pow]
          split_ifs with h
          · exact hp p.natDegree
          · exact zero_Pconstructible
        have hppcoeff : ∀ i, PConstructible (pp.coeff i) := by
          intro i
          rw [hppdef, Polynomial.coeff_sub]
          exact PConstructible.sub (hp i) (coeff_mul_Pconstructible hdc hzcoeff i)
        have hppdeg : pp.degree < p.degree := by
          rw [hppdef, hzdef]
          exact Polynomial.div_wf_lemma ⟨hge, hpne⟩ hd
        have hpplt : pp.natDegree < p.natDegree := by
          rcases eq_or_ne pp 0 with h0 | h0
          · rw [h0, Polynomial.natDegree_zero]
            exact Polynomial.natDegree_pos_iff_degree_pos.mpr hpdegpos
          · exact Polynomial.natDegree_lt_natDegree h0 hppdeg
        obtain ⟨hq', hr'⟩ := ih pp.natDegree (hpdeg ▸ hpplt) pp rfl hppcoeff
        have hkey : p /ₘ d = z + pp /ₘ d ∧ p %ₘ d = pp %ₘ d :=
          Polynomial.div_modByMonic_unique (z + pp /ₘ d) (pp %ₘ d) hd
            ⟨?_, Polynomial.degree_modByMonic_lt pp hd⟩
        · exact ⟨fun i => by
              rw [hkey.1, Polynomial.coeff_add]
              exact PConstructible.add (hzcoeff i) (hq' i),
            fun i => by rw [hkey.2]; exact hr' i⟩
        · have hmid : pp %ₘ d + d * (pp /ₘ d) = pp := Polynomial.modByMonic_add_div pp d
          calc pp %ₘ d + d * (z + pp /ₘ d)
              = (pp %ₘ d + d * (pp /ₘ d)) + d * z := by ring
            _ = pp + d * z := by rw [hmid]
            _ = p := by rw [hppdef]; ring

-- Theorem: the quotient of a P-constructible polynomial by a monic P-constructible one has
-- P-constructible coefficients.
theorem divByMonic_coeff_Pconstructible {d : Polynomial ℝ} (hd : d.Monic)
    (hdc : ∀ i, PConstructible (d.coeff i)) {p : Polynomial ℝ}
    (hp : ∀ i, PConstructible (p.coeff i)) :
    ∀ i, PConstructible ((p /ₘ d).coeff i) :=
  (divModByMonic_coeff_Pconstructible hd hdc p hp).1

-- Theorem: the remainder of a P-constructible polynomial modulo a monic P-constructible one
-- has P-constructible coefficients.
theorem modByMonic_coeff_Pconstructible {d : Polynomial ℝ} (hd : d.Monic)
    (hdc : ∀ i, PConstructible (d.coeff i)) {p : Polynomial ℝ}
    (hp : ∀ i, PConstructible (p.coeff i)) :
    ∀ i, PConstructible ((p %ₘ d).coeff i) :=
  (divModByMonic_coeff_Pconstructible hd hdc p hp).2

-- Theorem: the gcd of two polynomials with P-constructible coefficients has
-- P-constructible coefficients.  This follows the Euclidean recursion `gcd a b = if a = 0
-- then b else gcd (b % a) a` (`EuclideanDomain.GCD.induction`), using that the remainder
-- `b % a = b %ₘ (a * C a.leadingCoeff⁻¹)` is division by a monic polynomial.
theorem gcd_coeff_Pconstructible (a b : Polynomial ℝ)
    (ha : ∀ i, PConstructible (a.coeff i)) (hb : ∀ i, PConstructible (b.coeff i)) :
    ∀ i, PConstructible ((EuclideanDomain.gcd a b).coeff i) := by
  revert ha hb
  refine EuclideanDomain.GCD.induction a b ?_ ?_
  · intro x _ hx i
    rw [EuclideanDomain.gcd_zero_left]
    exact hx i
  · intro a b ha0 ih ha hb i
    rw [EuclideanDomain.gcd_val]
    refine ih ?_ ha i
    intro j
    rw [Polynomial.mod_def]
    refine modByMonic_coeff_Pconstructible
      (Polynomial.monic_mul_leadingCoeff_inv ha0) ?_ hb j
    intro k
    exact coeff_mul_Pconstructible ha
      (fun l => coeff_C_Pconstructible (inv_Pconstructible (ha a.natDegree)) l) k

/-! ### The non-separable case of the septic problem

If `q` is a monic polynomial of degree at most `7` that is not separable, then it has a
repeated root and `gcd q q'` is nonconstant.  Every real root of `q` is either a root of
`d := gcd q q'` (degree `≤ 6` because `d ∣ q'`) or of the quotient `q / d`, and the quotient
also has degree `≤ 6` because `d` is nonconstant.  Since `d` can be normalised to a monic
polynomial `d₀` without changing its degree or root set and the quotient by `d₀` still has
degree `≤ 6`, the sextic engine applies in either branch. -/

-- Theorem: a non-separable monic polynomial `q` of degree at most `7` with P-constructible
-- coefficients has P-constructible real roots.
theorem root_Pconstructible_of_nonSeparable {q : Polynomial ℝ} (hmon : q.Monic)
    (hcoeff : ∀ k, PConstructible (q.coeff k)) (hdeg : q.natDegree ≤ 7)
    (hns : ¬ q.Separable) {β : ℝ} (hβ : q.eval β = 0) : PConstructible β := by
  have hq0 : q ≠ 0 := hmon.ne_zero
  have hnat_ne : q.natDegree ≠ 0 := by
    intro h0
    exact hns (by
      rw [Polynomial.eq_one_of_monic_natDegree_zero hmon h0]
      exact Polynomial.separable_one)
  have hderiv_ne : q.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hnat_ne
  have hdcoeff : ∀ i, PConstructible (q.derivative.coeff i) := by
    intro i
    rw [Polynomial.coeff_derivative]
    exact PConstructible.mul (hcoeff (i + 1))
      (PConstructible.add (nat_Pconstructible i) PConstructible.base_one)
  set d : Polynomial ℝ := EuclideanDomain.gcd q q.derivative with hddef
  have hdcoeffd : ∀ i, PConstructible (d.coeff i) := by
    rw [hddef]
    exact gcd_coeff_Pconstructible q q.derivative hcoeff hdcoeff
  have hdvd_q : d ∣ q := by
    rw [hddef]; exact EuclideanDomain.gcd_dvd_left q q.derivative
  have hdvd_dq : d ∣ q.derivative := by
    rw [hddef]; exact EuclideanDomain.gcd_dvd_right q q.derivative
  have hdne : d ≠ 0 := by
    rw [hddef]
    intro hzero
    exact hq0 ((EuclideanDomain.gcd_eq_zero_iff).mp hzero).1
  have hddeg : d.natDegree ≤ 6 := by
    have hderiv_deg : q.derivative.natDegree ≤ 6 := by
      have := Polynomial.natDegree_derivative_le q
      omega
    rw [hddef]
    exact le_trans
      (Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right q q.derivative)
        hderiv_ne) hderiv_deg
  have hdpos : 0 < d.natDegree := by
    have hnotunit : ¬ IsUnit d := by
      intro hu
      rw [hddef] at hu
      exact hns ((Polynomial.separable_def q).mpr (EuclideanDomain.gcd_isUnit_iff.mp hu))
    rw [Polynomial.isUnit_iff_degree_eq_zero] at hnotunit
    apply Nat.pos_of_ne_zero
    intro h0
    exact hnotunit (by simp [Polynomial.degree_eq_natDegree hdne, h0])
  have hlc_ne : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hdne
  have hlc_inv_ne : d.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero hlc_ne
  set d0 : Polynomial ℝ := d * Polynomial.C d.leadingCoeff⁻¹ with hd0def
  have hd0monic : d0.Monic := by
    rw [hd0def]; exact Polynomial.monic_mul_leadingCoeff_inv hdne
  have hd0coeff : ∀ i, PConstructible (d0.coeff i) := by
    intro i
    rw [hd0def]
    exact coeff_mul_Pconstructible hdcoeffd
      (fun j => coeff_C_Pconstructible (inv_Pconstructible (hdcoeffd d.natDegree)) j) i
  have hd0ne : d0 ≠ 0 := by
    rw [hd0def]
    exact mul_ne_zero hdne (Polynomial.C_ne_zero.mpr hlc_inv_ne)
  have hd0nat : d0.natDegree = d.natDegree := by
    rw [hd0def]
    exact Polynomial.natDegree_mul_C hlc_inv_ne
  have hd0deg : d0.natDegree ≤ 6 := by rw [hd0nat]; exact hddeg
  have hd0pos : 1 ≤ d0.natDegree := by rw [hd0nat]; omega
  by_cases hd0β : d0.eval β = 0
  · exact root_Pconstructible_le_six_coeffs hd0ne hd0deg hd0coeff hd0β
  · have h0dvd_d : d0 ∣ d := ⟨Polynomial.C d.leadingCoeff, by
        rw [hd0def, mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlc_ne,
          Polynomial.C_1, mul_one]⟩
    have h0dvd_q : d0 ∣ q := dvd_trans h0dvd_d hdvd_q
    have hq_eq : d0 * (q /ₘ d0) = q := by
      have hmod0 : q %ₘ d0 = 0 :=
        (Polynomial.modByMonic_eq_zero_iff_dvd hd0monic).mpr h0dvd_q
      have h := Polynomial.modByMonic_add_div q d0
      rw [hmod0, zero_add] at h
      exact h
    have hrcoeff : ∀ i, PConstructible ((q /ₘ d0).coeff i) :=
      fun i => (divModByMonic_coeff_Pconstructible hd0monic hd0coeff q hcoeff).1 i
    have hrdeg : (q /ₘ d0).natDegree ≤ 6 := by
      rw [Polynomial.natDegree_divByMonic q hd0monic]
      omega
    have hrne : q /ₘ d0 ≠ 0 := by
      intro h0
      have : q = 0 := by rw [← hq_eq, h0, mul_zero]
      exact hq0 this
    have hrβ : (q /ₘ d0).eval β = 0 := by
      have h := congrArg (fun p : Polynomial ℝ => p.eval β) hq_eq
      rw [Polynomial.eval_mul, hβ] at h
      exact (mul_eq_zero.mp h).resolve_left hd0β
    exact root_Pconstructible_le_six_coeffs hrne hrdeg hrcoeff hrβ

end Pconstructible
