import Pptc.Basic

/-! # The recovery step of the nonic construction

Steps 5--6 of the nonic plan: a P-constructible value `y = φ (ψ β)` of a composition of
two nonconstant rational polynomials `ψ, φ` of degree at most `6` determines `β`. Both
inversions are roots of degree-`≤ 6` polynomials over the P-constructible reals, so
`root_Pconstructible_le_six_coeffs` applies twice: first to `φ X - y` to recover
`z = ψ β`, then to `ψ X - z` to recover `β`.

The engine is stated for a single rational polynomial `p` whose `aeval` at `β` is a
P-constructible value `y`; `nonic_recovery` composes it. -/

open Polynomial

namespace Pconstructible

-- Theorem: if `p ∈ ℚ[X]` is nonconstant of degree at most 6 and `y = aeval β p` is
-- P-constructible, then `β` is P-constructible. `β` is a root of
-- `p.map (algebraMap ℚ ℝ) - C y`, whose coefficients are those of `p` cast to `ℝ` except
-- at `X ^ 0`, where `y` is subtracted off.
theorem rat_eval_root_Pconstructible {p : Polynomial ℚ} (hdeg : p.natDegree ≤ 6)
    (hnc : 1 ≤ p.natDegree) {β y : ℝ} (hy : PConstructible y)
    (h : y = aeval β p) : PConstructible β := by
  set P : Polynomial ℝ := p.map (algebraMap ℚ ℝ) - Polynomial.C y with hP
  have hf : Function.Injective (algebraMap ℚ ℝ) := fun a b hab => Rat.cast_injective hab
  have hcoeff : ∀ i, PConstructible (P.coeff i) := by
    intro i
    rw [hP, Polynomial.coeff_sub, Polynomial.coeff_map]
    by_cases hi : i = 0
    · subst hi
      simp only [Polynomial.coeff_C, if_pos]
      simpa using PConstructible.sub (rat_Pconstructible (p.coeff 0)) hy
    · rw [Polynomial.coeff_C, if_neg hi, sub_zero]
      simpa using rat_Pconstructible (p.coeff i)
  have hdeg' : P.natDegree ≤ 6 := by
    rw [hP]
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    rw [Polynomial.natDegree_C]
    exact max_le (le_trans Polynomial.natDegree_map_le hdeg) (Nat.zero_le 6)
  have hne : P ≠ 0 := by
    intro h0
    have hmap : p.map (algebraMap ℚ ℝ) = Polynomial.C y := by
      rw [hP, sub_eq_zero] at h0
      exact h0
    have hnd := Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℚ ℝ) hf p
    rw [hmap, Polynomial.natDegree_C] at hnd
    omega
  have hroot : P.eval β = 0 := by
    rw [hP, Polynomial.eval_sub, Polynomial.eval_C]
    have hev : (p.map (algebraMap ℚ ℝ)).eval β = aeval β p := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [hev, h, sub_self]
  exact root_Pconstructible_le_six_coeffs hne hdeg' hcoeff hroot

-- Theorem: if `y` is P-constructible and `y = φ(ψ β)` where `ψ, φ ∈ ℚ[X]` are nonconstant of
-- degree at most 6, then `β` is P-constructible.
theorem nonic_recovery {ψ φ : Polynomial ℚ} (hψdeg : ψ.natDegree ≤ 6) (hψnc : 1 ≤ ψ.natDegree)
    (hφdeg : φ.natDegree ≤ 6) (hφnc : 1 ≤ φ.natDegree)
    {β y : ℝ} (hy : PConstructible y)
    (hy_eq : y = aeval (aeval β ψ) φ) : PConstructible β := by
  set z : ℝ := aeval β ψ with hz
  have hzP : PConstructible z :=
    rat_eval_root_Pconstructible hφdeg hφnc hy (by rw [hz]; exact hy_eq)
  exact rat_eval_root_Pconstructible hψdeg hψnc hzP hz.symm

end Pconstructible
