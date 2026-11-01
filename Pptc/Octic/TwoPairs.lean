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

import Pptc.Octic.Cone
import Pptc.Octic.Resolvent

/-! # Pptc.Octic.TwoPairs

The `s ≥ 2` case of the nonreal octic.

When `q` has two distinct conjugate pairs `{z, z̄}` and `{w, w̄}`, the trace form
`Q = qform (Gram8 q)` on the trace-zero hyperplane `{p1vec8 = 0} ≅ Fin 7 → ℝ` is
negative definite on a P-constructible 2-plane (`neg_dir_of_pair8`) and positive
definite on another (`pos_dir_of_pair8`); the signature of `Q` on `V` is `(7 - s, s)`,
so with `s ≥ 2` both are available.  Projecting these 2-planes orthogonally to a
P-constructible cone point `P₀` (`exists_orth_neg_PconstructibleN`, applied to
`Gram8 q` and to `-Gram8 q`) and rationalising gives P-constructible `e ⊥ P₀` with
`Q e < 0` and `f ⊥ P₀` with `Q f < 0` for `-Q`, i.e. `Q f > 0`.  The line
`e + t • f` therefore meets the cone at a P-constructible isotropic `x ⊥ P₀`
(`exists_isotropic_orth_Pconstructible8`), and `x` is not parallel to `P₀`, so
`span(P₀, x)` is a totally isotropic plane inside `{p1vec8 = 0}`.

Pulled back to coefficient vectors `cv = Lcomb8 q P₀` and `cw = Lcomb8 q x` in
`Fin 8 → ℝ`, this plane is spanned by two isotropic orthogonal vectors with vanishing
first moment.  On it `p3vec8` is a binary cubic

`a s³ + b s² t + c s t² + d t³ = Tr ((s • cv + t • cw) ^ 3)`,

and `binary_cubic_zero` produces P-constructible `s, t`, not both zero, where it
vanishes.  The combination `ψ = s • cv + t • cw` is nonzero, has vanishing first and
second trace power sums (isotropy and orthogonality) and vanishing third one (the
cubic equation), so `φ = polyOfVec8 ψ` has degree `≤ 7`, P-constructible coefficients
and `Tr φ = Tr φ² = Tr φ³ = 0` on `ℝ[X]/(q)`.

The resolvent tail `root_Pconstructible_of_tschirnhaus8` then recovers `β`: the
characteristic polynomial of `φ(companionN q)` has no `X⁷, X⁶, X⁵` terms, so
`y = φ(β)` satisfies `y⁸ = quartic`, `y` is P-constructible by the quartic power-law
engine, and `β` is a root of the nonzero polynomial `φ - C y` of degree `≤ 7`, which
the septic theorem handles.
-/

namespace Pconstructible

open Polynomial Matrix

noncomputable section

-- Theorem: if a monic separable octic `q` with P-constructible coefficients has two
-- non-real roots `z, w` in distinct conjugate classes, then there is a nonzero
-- polynomial `φ` of degree `≤ 7` with P-constructible coefficients whose first three
-- trace power sums at `companionN (n := 8) q` vanish.
theorem exists_tschirnhaus_traces_two_pairs8 (q : ℝ[X]) (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ φ : ℝ[X], (∀ k, PConstructible (φ.coeff k)) ∧ φ.natDegree ≤ 7 ∧ φ ≠ 0 ∧
      Matrix.trace (aeval (companionN (n := 8) q) φ) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 2) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 3) = 0 := by
  obtain ⟨P₀, hP₀P, hQ₀, hP₀ne⟩ :=
    exists_cone_point8 q hmon hnat hsep hq hz hzim
  obtain ⟨v1, v2, hneg⟩ := neg_dir_of_pair8 q hmon hnat hsep hz hzim hw hwim hzw hzw'
  obtain ⟨w1, w2, hpos⟩ := pos_dir_of_pair8 q hmon hnat hsep hz hzim hw hwim hzw hzw'
  obtain ⟨e, heP, hBe, heQ⟩ :=
    exists_orth_neg_PconstructibleN (n := 7) (A := Gram8 q)
      (Gram8_Pconstructible q hq) hP₀P hneg
  have hdefpos :
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → qform (-Gram8 q) (a • w1 + b • w2) < 0 := by
    intro a b hab
    rw [qform_neg]
    linarith [hpos a b hab]
  obtain ⟨f, hfP, hBfneg, hfQneg⟩ :=
    exists_orth_neg_PconstructibleN (n := 7) (A := -Gram8 q)
      (fun i j => neg_Pconstructible (Gram8_Pconstructible q hq i j)) hP₀P hdefpos
  have hBf : bilin (Gram8 q) P₀ f = 0 := by
    rw [bilin_neg] at hBfneg
    linarith
  have hfQ : 0 < qform (Gram8 q) f := by
    rw [qform_neg] at hfQneg
    linarith
  obtain ⟨x, hxP, hQx, hBx, hxpar⟩ :=
    exists_isotropic_orth_Pconstructible8 q hq hQ₀ heP hfP hBe hBf heQ hfQ
  set cv : Fin 8 → ℝ := Lcomb8 q P₀ with hcv
  set cw : Fin 8 → ℝ := Lcomb8 q x with hcw
  have hcvP : ∀ i, PConstructible (cv i) := Lcomb8_Pconstructible q hq hP₀P
  have hcwP : ∀ i, PConstructible (cw i) := Lcomb8_Pconstructible q hq hxP
  have hqformv : qform (Hmat8 q) cv = 0 := by
    rw [hcv, qform_Gram8_Lcomb8, hQ₀]
  have hqformw : qform (Hmat8 q) cw = 0 := by
    rw [hcw, qform_Gram8_Lcomb8, hQx]
  have hbilinc : bilin (Hmat8 q) cv cw = 0 := by
    rw [hcv, hcw, bilin_Hmat8_Lcomb8, hBx]
  have hp1v : p1vec8 q cv = 0 := by rw [hcv, p1vec8_Lcomb8]
  have hp1w : p1vec8 q cw = 0 := by rw [hcw, p1vec8_Lcomb8]
  have hindep' : ¬ ∃ c : ℝ, cw = c • cv := by
    rintro ⟨c, hc⟩
    apply hxpar
    refine ⟨c, ?_⟩
    have h1 : Lcomb8 q (x - c • P₀) = 0 := by
      rw [Lcomb8_sub, Lcomb8_smul, ← hcw, ← hcv, hc, sub_self]
    exact sub_eq_zero.mp (Lcomb8_injective q h1)
  have hcvne : cv ≠ 0 := by
    intro h0
    have h1 : P₀ = 0 := Lcomb8_injective q (by rw [hcv] at h0; exact h0)
    exact hP₀ne h1
  set Ncv : Matrix (Fin 8) (Fin 8) ℝ := aeval (companionN (n := 8) q) (polyOfVec8 cv)
    with hNcv
  set Ncw : Matrix (Fin 8) (Fin 8) ℝ := aeval (companionN (n := 8) q) (polyOfVec8 cw)
    with hNcw
  have hNcvP : ∀ i j, PConstructible (Ncv i j) := by
    intro i j
    rw [hNcv]
    exact aeval_entries_Pconstructible _ (companionN_entries_Pconstructible 8 q hq) _
      (polyOfVec8_coeff_Pconstructible cv hcvP) i j
  have hNcwP : ∀ i j, PConstructible (Ncw i j) := by
    intro i j
    rw [hNcw]
    exact aeval_entries_Pconstructible _ (companionN_entries_Pconstructible 8 q hq) _
      (polyOfVec8_coeff_Pconstructible cw hcwP) i j
  have hA : PConstructible (p3vec8 q cv) := by
    rw [p3vec8, ← hNcv]; exact trace_pow_Pconstructible8 hNcvP 3
  have hDc : PConstructible (p3vec8 q cw) := by
    rw [p3vec8, ← hNcw]; exact trace_pow_Pconstructible8 hNcwP 3
  have hB : PConstructible (3 * Matrix.trace (Ncv ^ 2 * Ncw)) :=
    PConstructible.mul (by pconstructible)
      (trace_mul_Pconstructible8 (matrix_pow_entries_Pconstructible hNcvP 2) hNcwP)
  have hC : PConstructible (3 * Matrix.trace (Ncv * Ncw ^ 2)) :=
    PConstructible.mul (by pconstructible)
      (trace_mul_Pconstructible8 hNcvP (matrix_pow_entries_Pconstructible hNcwP 2))
  obtain ⟨s, t, hsP, htP, _hstne, hcub⟩ :=
    binary_cubic_zero (a := p3vec8 q cv) (b := 3 * Matrix.trace (Ncv ^ 2 * Ncw))
      (c := 3 * Matrix.trace (Ncv * Ncw ^ 2)) (d := p3vec8 q cw) hA hB hC hDc
  set ψ : Fin 8 → ℝ := s • cv + t • cw with hψ
  have hψP : ∀ i, PConstructible (ψ i) := by
    intro i
    rw [hψ, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact PConstructible.add (PConstructible.mul hsP (hcvP i))
      (PConstructible.mul htP (hcwP i))
  have hψne : ψ ≠ 0 := by
    intro h0
    have hcomb : s • cv + t • cw = 0 := by rw [← hψ]; exact h0
    obtain ⟨hs0, ht0⟩ := smul_add_smul_eq_zero_of_not_parallel hcvne hindep' hcomb
    rcases _hstne with h | h
    · exact h hs0
    · exact h ht0
  refine ⟨polyOfVec8 ψ, polyOfVec8_coeff_Pconstructible ψ hψP, polyOfVec8_natDegree_le ψ,
    polyOfVec8_ne_zero hψne, ?_, ?_, ?_⟩
  · rw [← p1vec8_eq_trace, hψ, p1vec8_smul_add, hp1v, hp1w]
    ring
  · rw [← hermiteForm8_eq_trace_sq q ψ, ← qform_Hmat8_eq_hermiteForm8, hψ,
      qform_smul_add (Hmat8 q) (Hmat8_symm q), hqformv, hbilinc, hqformw]
    ring
  · have haeval : aeval (companionN (n := 8) q) (polyOfVec8 ψ) = s • Ncv + t • Ncw := by
      rw [hψ, aeval_polyOfVec8_smul_add, hNcv, hNcw]
    have hAc : p3vec8 q cv = Matrix.trace (Ncv ^ 3) := by rw [p3vec8, ← hNcv]
    have hDc' : p3vec8 q cw = Matrix.trace (Ncw ^ 3) := by rw [p3vec8, ← hNcw]
    rw [haeval, trace_cube_smul_add8]
    rw [hAc, hDc'] at hcub
    ring_nf at hcub ⊢
    linarith

-- Theorem: a real root `β` of a monic separable octic `q` with P-constructible
-- coefficients and two non-real roots `z, w` in distinct conjugate classes is
-- P-constructible. This is the `s ≥ 2` case of the octic; the non-separable case is
-- handled in `Pptc/Octic/Main.lean`.
theorem root_Pconstructible_of_two_conjugate_pairs8 {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β := by
  obtain ⟨φ, hφc, hφdeg, hφne, hp1, hp2, hp3⟩ :=
    exists_tschirnhaus_traces_two_pairs8 q hmon hnat hsep hq hz hzim hw hwim hzw hzw'
  exact root_Pconstructible_of_tschirnhaus8 hmon hnat hsep hq hφc hφdeg hφne hp1 hp2 hp3 hβ

end

end Pconstructible
