import Pptc.ScratchSep
import Pptc.DegreeSeven
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IsAlgClosed.Basic

open Polynomial

namespace Pconstructible

/-! ### §2.3 The quadratic factor of a one-conjugate-pair septic

Let `q` be a septic (degree at most `7`) with P-constructible coefficients that factors as
`q = g * q5`, where `g` is the monic quadratic carrying the single conjugate pair and `q5`
is its totally-real quintic cofactor.  This file records that constructibility of the real
roots of `q` is *equivalent* to constructibility of the coefficients of `g`.

The forward direction (`roots_Pconstructible_of_quadratic_factor`) needs no real-root
hypothesis at all: since `g` is monic, `q5 = q /ₘ g` has P-constructible coefficients by
`divByMonic_coeff_Pconstructible`, and then `root_Pconstructible_le_six_coeffs` finishes on
any root of `q5`.

The converse (`quadratic_factor_coeff_Pconstructible_of_real_roots`) assumes that every
complex root of `q5` is real and that every real root of `q5` is P-constructible.  Then
`q5` splits over `ℝ`, so `q5 = ∏_{r ∈ q5.roots} (X - C r)` is a product of lines whose
constant terms are the P-constructible roots, whence its coefficients are P-constructible;
finally `g = q /ₘ q5`. -/

-- Theorem: if `q = g * q5` with `g` monic and `q5` of degree at most `6`, and the
-- coefficients of `q`, `g` are P-constructible, then every real root of `q5` is
-- P-constructible.  (The hypothesis `q5 ≠ 0` is needed: for `q5 = 0` the root equation is
-- vacuous and the conclusion would assert that every real is P-constructible.)
theorem roots_Pconstructible_of_quadratic_factor {q g q5 : Polynomial ℝ}
    (hq : ∀ k, PConstructible (q.coeff k)) (hgmon : g.Monic) (hfact : q = g * q5)
    (hg : ∀ k, PConstructible (g.coeff k)) (hdeg : q5.natDegree ≤ 6)
    (hq5ne : q5 ≠ 0) {β : ℝ} (hβ : q5.eval β = 0) : PConstructible β := by
  have hdvd : g ∣ q := ⟨q5, hfact⟩
  have hmod : q %ₘ g = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hgmon).mpr hdvd
  have hdiv : q /ₘ g = q5 := by
    have h := Polynomial.modByMonic_add_div q g
    rw [hmod, zero_add] at h
    have h2 : g * (q /ₘ g) = g * q5 := by rw [h, hfact]
    exact mul_left_cancel₀ hgmon.ne_zero h2
  have hcoeff : ∀ k, PConstructible (q5.coeff k) := by
    intro k
    rw [← hdiv]
    exact divByMonic_coeff_Pconstructible hgmon hg hq k
  exact root_Pconstructible_le_six_coeffs hq5ne hdeg hcoeff hβ

-- Theorem: conversely, if the real roots of `q5` are P-constructible and every complex
-- root of `q5` is real, then the monic quadratic factor `g` of `q = g * q5` has
-- P-constructible coefficients.  (`hmon` and `hgmon` are not needed by the argument but are
-- part of the statement as posed: the uniqueness hypothesis `q = g * q5` with `g` monic
-- already pins `g` down.)
set_option linter.unusedVariables false in
theorem quadratic_factor_coeff_Pconstructible_of_real_roots {q g q5 : Polynomial ℝ}
    (hmon : q.Monic) (hq : ∀ k, PConstructible (q.coeff k)) (hgmon : g.Monic)
    (hfact : q = g * q5) (hq5mon : q5.Monic)
    (hsplit : ∀ z : ℂ, (q5.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0)
    (hroots : ∀ β : ℝ, q5.eval β = 0 → PConstructible β) :
    ∀ k, PConstructible (g.coeff k) := by
  have hq5ne : q5 ≠ 0 := hq5mon.ne_zero
  -- `q5` has real coefficients and every complex root is real, so it splits over `ℝ`.
  have hmapne : q5.map (algebraMap ℝ ℂ) ≠ 0 := by
    intro h0
    have hinj : Function.Injective (Polynomial.map (algebraMap ℝ ℂ)) :=
      Polynomial.map_injective _ Complex.ofReal_injective
    refine hq5ne (hinj ?_)
    rw [h0, Polynomial.map_zero]
  have hsp : q5.Splits := by
    refine Polynomial.Splits.of_splits_map_of_injective (i := algebraMap ℝ ℂ)
      Complex.ofReal_injective (IsAlgClosed.splits _) ?_
    intro a ha
    rw [Polynomial.mem_roots hmapne] at ha
    have him : a.im = 0 := hsplit a ha
    exact ⟨a.re, Complex.ext (by simp) (by simpa [Complex.ofReal_im] using him.symm)⟩
  -- Expand `q5` as the product of its linear factors.
  have hprod : q5 = (q5.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod := by
    have h := hsp.eq_prod_roots
    rw [hq5mon, Polynomial.C_1, one_mul] at h
    exact h
  -- A product of lines with P-constructible roots has P-constructible coefficients.
  have hXc : ∀ j, PConstructible ((Polynomial.X : Polynomial ℝ).coeff j) := by
    intro j
    rw [Polynomial.coeff_X]
    split_ifs with h
    · exact PConstructible.base_one
    · exact zero_Pconstructible
  have hprodc : ∀ s : Multiset ℝ, (∀ r ∈ s, PConstructible r) →
      ∀ i, PConstructible (((s.map (fun r => Polynomial.X - Polynomial.C r)).prod).coeff i) := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
        intro _ i
        rw [Multiset.map_zero, Multiset.prod_zero, Polynomial.coeff_one]
        split_ifs with h
        · exact PConstructible.base_one
        · exact zero_Pconstructible
    | cons a s ih =>
        intro hs
        have ha : PConstructible a := hs a (by simp)
        have hs' : ∀ r ∈ s, PConstructible r := fun r hr => hs r (by simp [hr])
        have hlin : ∀ j, PConstructible ((Polynomial.X - Polynomial.C a).coeff j) := by
          intro j
          rw [Polynomial.coeff_sub]
          exact PConstructible.sub (hXc j) (coeff_C_Pconstructible ha j)
        intro i
        rw [Multiset.map_cons, Multiset.prod_cons]
        exact coeff_mul_Pconstructible hlin (ih hs') i
  have hq5coeff : ∀ k, PConstructible (q5.coeff k) := by
    have hp := hprodc q5.roots (fun r hr => ?_)
    · intro k
      rw [hprod]
      exact hp k
    · rw [Polynomial.mem_roots hq5ne] at hr
      exact hroots r hr
  -- Finally `g = q /ₘ q5`.
  have hdvd : q5 ∣ q := ⟨g, by rw [hfact, mul_comm]⟩
  have hmod : q %ₘ q5 = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hq5mon).mpr hdvd
  have hdiv : q /ₘ q5 = g := by
    have h := Polynomial.modByMonic_add_div q q5
    rw [hmod, zero_add] at h
    have h2 : q5 * (q /ₘ q5) = q5 * g := by rw [h, hfact, mul_comm g q5]
    exact mul_left_cancel₀ hq5mon.ne_zero h2
  intro k
  rw [← hdiv]
  exact divByMonic_coeff_Pconstructible hq5mon hq5coeff hq k

end Pconstructible
