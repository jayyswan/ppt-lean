/- Copyright (c) 2024 Lean Community. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file is part of the Pptc (PowerPoint Constructibility) project.
-/

import Pptc.Octic.TwoPairs
import Pptc.Octic.OnePair

/-! # Pptc.Octic.Main

The nonreal octic case of `Pptc/Octic/PLAN.md`, assembling the two Tschirnhaus routes:

* `s ≥ 2`: a second conjugacy class supplies a totally isotropic plane through a
  P-constructible cone point, and `binary_cubic_zero` produces the Tschirnhaus map
  (`root_Pconstructible_of_two_conjugate_pairs8`);
* `s = 1`: there is no totally isotropic plane (`isotropic_plane_trivial8`), so the
  stereographic sign change is used instead
  (`root_Pconstructible_of_one_conjugate_pair8`).

Both routes end in `root_Pconstructible_of_tschirnhaus8`, which reduces to the septic theorem.
Together with `root_Pconstructible_totallyReal_eight` (splitting case) and
`root_Pconstructible_of_nonSeparable_eight`, this gives every real root of every octic with
P-constructible coefficients.

The signature bookkeeping: on the 7-dimensional trace-zero space the trace form has signature
`(7 - s, s)`. For `s = 1` this is `(6, 1)`, and no isotropic plane exists; for `s ≥ 2` a
negative 2-plane exists and the positive part has dimension `7 - s ≥ 3`. The sextic along the
stereographic line is still of degree 6, because `stereoN` is quadratic in the direction and
`p3vec8` is cubic.
-/

namespace Pconstructible

open Polynomial Matrix

noncomputable section

/-! ### The nonreal case -/

-- Theorem: a real root `β` of a monic separable octic with a nonreal root `z` is
-- P-constructible. Split on whether a second conjugate pair exists.
theorem root_Pconstructible_of_nonreal_separable8 {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    {β : ℝ} (hβ : q.eval β = 0) : PConstructible β := by
  by_cases hsecond : ∃ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 ∧ w.im ≠ 0 ∧
      w ≠ z ∧ w ≠ starRingEnd ℂ z
  · obtain ⟨w, hw, hwim, hwz, hwz'⟩ := hsecond
    have hzw' : z ≠ starRingEnd ℂ w := by
      intro h
      exact hwz' (by
        have := congrArg (starRingEnd ℂ) h
        simpa using this.symm)
    exact root_Pconstructible_of_two_conjugate_pairs8 hmon hnat hsep hq hz hzim
      hw hwim hwz.symm hzw' hβ
  · have hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
        w = z ∨ w = starRingEnd ℂ z := by
      intro w hw hwim
      by_contra hc
      rcases not_or.mp hc with ⟨hwz, hwz'⟩
      exact hsecond ⟨w, hw, hwim, hwz, hwz'⟩
    exact root_Pconstructible_of_one_conjugate_pair8 hmon hnat hsep hq hz hzim hone hβ

-- Theorem: a real root `β` of any octic `q` with P-constructible coefficients and a
-- nonreal complex root `z` is P-constructible: normalise to monic, then split on
-- separability and, in the separable branch, on whether a second conjugate pair exists.
theorem root_Pconstructible_of_nonreal_root8 {q : ℝ[X]} (hnat : q.natDegree = 8)
    (hq : ∀ k, PConstructible (q.coeff k)) {z : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    {β : ℝ} (hβ : q.eval β = 0) : PConstructible β := by
  classical
  have hne : q ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  set q₀ : ℝ[X] := C q.leadingCoeff⁻¹ * q with hq₀
  have hmon : q₀.Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hnat₀ : q₀.natDegree = 8 := by
    rw [hq₀, Polynomial.natDegree_C_mul (inv_ne_zero hlc), hnat]
  have hq₀c : ∀ k, PConstructible (q₀.coeff k) :=
    C_mul_coeff_Pconstructible (inv_Pconstructible (hq q.natDegree)) hq
  have hroot₀ : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 →
      (q₀.map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx
    simp [hq₀, Polynomial.map_mul, hx]
  have hz₀ : (q₀.map (algebraMap ℝ ℂ)).eval z = 0 := hroot₀ z hz
  have hβ₀ : q₀.eval β = 0 := by simp [hq₀, hβ]
  by_cases hsep : q₀.Separable
  · exact root_Pconstructible_of_nonreal_separable8 hmon hnat₀ hsep hq₀c hz₀ hzim hβ₀
  · exact root_Pconstructible_of_nonSeparable_eight hmon hq₀c (le_of_eq hnat₀) hsep hβ₀

/-! ### The degree-8 theorem -/

-- Theorem: every real root of an octic with P-constructible coefficients is
-- P-constructible. The cases are: degree `≤ 7` (the septic theorem), totally real
-- (`root_Pconstructible_totallyReal_eight`), non-separable
-- (`root_Pconstructible_of_nonSeparable_eight`), and separable with a nonreal root
-- (`root_Pconstructible_of_nonreal_root8`).
theorem root_Pconstructible_deg8_coeffs {q : ℝ[X]} (hq : q ≠ 0) (h8 : q.natDegree ≤ 8)
    (hcoef : ∀ k, PConstructible (q.coeff k)) {α : ℝ} (hα : q.eval α = 0) :
    PConstructible α := by
  by_cases hdeg7 : q.natDegree ≤ 7
  · exact root_Pconstructible_deg7_coeffs hq hdeg7 hcoef hα
  · have hnat : q.natDegree = 8 := by omega
    have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
    set q₀ : ℝ[X] := Polynomial.C q.leadingCoeff⁻¹ * q with hq₀
    have hq₀ne : q₀ ≠ 0 := by
      rw [hq₀]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero hlc)) hq
    have hmon : q₀.Monic :=
      Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
    have hnat₀ : q₀.natDegree = 8 := by
      rw [hq₀, Polynomial.natDegree_C_mul (inv_ne_zero hlc), hnat]
    have hcoef₀ : ∀ k, PConstructible (q₀.coeff k) :=
      C_mul_coeff_Pconstructible (inv_Pconstructible (hcoef q.natDegree)) hcoef
    have hα₀ : q₀.eval α = 0 := by simp [hq₀, hα]
    by_cases hsep : q₀.Separable
    · by_cases hsp : q₀.Splits
      · exact root_Pconstructible_totallyReal_eight hmon hnat₀ hsp hcoef₀ hα₀
      · obtain ⟨z, hz, hzim⟩ := exists_nonreal_root_of_not_splits hq₀ne hsep hsp
        exact root_Pconstructible_of_nonreal_root8 hnat₀ hcoef₀ hz hzim hα₀
    · exact root_Pconstructible_of_nonSeparable_eight hmon hcoef₀ (le_of_eq hnat₀)
        hsep hα₀

end

end Pconstructible
