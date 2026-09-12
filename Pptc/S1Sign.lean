/-
Copyright (c) 2024 Lean Community. All rights reserved.

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

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
import Pptc.S1Cert
import Pptc.S1Iso

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### The sign certificate for the one-conjugate-pair septic

With a single non-real conjugate pair `{z, z̄}` the trace form `Q = qform (Gram q)` has no
totally isotropic plane (`isotropic_plane_trivial`).  The plan of `PLAN-degree7-s1.md` turns
that into a strict sign change of the reduced cubic `p3vec` on the light cone, using the
conjugation symmetry only inside the proof.  This file formalises the sign certificate: on the
cone `{Q = 0}` through a nonzero `P₀`, the stereographic parametrisation `stereo` produces
directions on which `p3vec` takes both signs.

The lynchpin is a Lagrange polynomial `X` with `X(x_j) = 1` at one real root, `0` at the other
real roots, and `ω = -1/2 + (√3/2) i` at `z`.  Its conjugate has `ω̄` at `z`.  Writing
`b = bilin (Gram q) P₀ (coeff6 (vecOf X))`, the trace split identity gives
`b = y_j + u ω + ū ω̄` with `y_j` the value of `F₀ = polyOfVec (Lcomb q P₀)` at `x_j` and `u =
F₀(z)`, so the two `b`'s multiply to `(y_j - Re u)² - 3 (Im u)²`, which is negative for some
`j` because `Q P₀ = 0` forces `(Im u)² = (Re u)² + S/2`. -/

/-- The primitive sixth root of unity `-1/2 + (√3/2) i`. -/
noncomputable def omegaC : ℂ := ⟨-1/2, Real.sqrt 3 / 2⟩

lemma omegaC_conj : starRingEnd ℂ omegaC = ⟨-1/2, -(Real.sqrt 3 / 2)⟩ := by
  simp [omegaC, Complex.ext_iff, Complex.conj_re, Complex.conj_im]

lemma omegaC_add_conj : omegaC + starRingEnd ℂ omegaC = -1 := by
  apply Complex.ext
  · simp [omegaC]
  · simp [omegaC]

lemma omegaC_mul_conj : omegaC * starRingEnd ℂ omegaC = 1 := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.one_re, Complex.conj_re, Complex.conj_im, omegaC]
    ring_nf
    rw [show (Real.sqrt 3) ^ 2 = 3 from Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  · simp only [Complex.mul_im, Complex.one_im, Complex.conj_re, Complex.conj_im, omegaC]
    ring

/-! ### Transport helpers

`vecOf` is a left inverse of `polyOfVec`, and evaluations of a mapped real polynomial at a
real point are the real evaluations cast to `ℂ`.  These are used to move between polynomials
and their coefficient vectors in the trace identities. -/

/-- `vecOf` is a left inverse of `polyOfVec`. -/
lemma vecOf_polyOfVec (v : Fin 7 → ℝ) : vecOf (polyOfVec v) = v := by
  funext i
  have hc : (polyOfVec v).coeff i.val = v i := by
    rw [polyOfVec, coeff_finset_sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Polynomial.coeff_monomial]
      split_ifs with h
      · exact absurd (Fin.ext h) hji
      · rfl
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simpa [vecOf] using hc

/-- Evaluation of a mapped real polynomial at a real point. -/
lemma eval_map_ofReal (f : ℝ[X]) (r : ℝ) :
    (f.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = ((f.eval r : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (f := algebraMap ℝ ℂ) (r := r) (p := f)

/-- Coercing a multiset sum of real values into `ℂ`. -/
lemma ofReal_multiset_sum (R : Multiset ℝ) (F : ℝ → ℝ) :
    (R.map (fun r => (F r : ℂ))).sum = (((R.map F).sum : ℝ) : ℂ) := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih]
      push_cast
      ring

/-! ### The trace split identity

`trace (N_f N_g)` is the sum of `f(w) g(w)` over the complex roots `w` of `q`.  Under the
root decomposition `z ::ₘ z̄ ::ₘ R` this is the real sum over `R` plus the terms at `z` and
`z̄`.  This is the computational core of the sign certificate. -/

-- Theorem: the trace of `N_f N_g` splits as the sum over the five real roots plus the two
-- non-real terms `f(z) g(z)` and `f(z̄) g(z̄)`.
lemma ofReal_trace_mul_eq_sum (q f g : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ))) :
    algebraMap ℝ ℂ (Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)))
      = ((R.map (fun r => f.eval r * g.eval r)).sum : ℂ)
        + ((f.map (algebraMap ℝ ℂ)).eval z) * ((g.map (algebraMap ℝ ℂ)).eval z)
        + ((f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z))
            * ((g.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)) := by
  have h := companion7_trace_pow_aeval q (f * g) hmon hnat hsep 1
  rw [pow_one, map_mul] at h
  rw [hroots, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons] at h
  simp only [Polynomial.map_mul, Polynomial.eval_mul, pow_one] at h
  have hR : ((R.map (algebraMap ℝ ℂ)).map
      (fun w => ((f.map (algebraMap ℝ ℂ)).eval w)
        * ((g.map (algebraMap ℝ ℂ)).eval w))).sum
      = (((R.map (fun r => f.eval r * g.eval r)).sum : ℝ) : ℂ) := by
    rw [Multiset.map_map]
    have hcongr : (R.map (((fun w => ((f.map (algebraMap ℝ ℂ)).eval w)
          * ((g.map (algebraMap ℝ ℂ)).eval w)) ∘ (algebraMap ℝ ℂ))))
        = R.map (fun r => ((f.eval r * g.eval r : ℝ) : ℂ)) := by
      apply Multiset.map_congr rfl
      intro r _
      simp only [Function.comp_apply]
      rw [eval_map_ofReal, eval_map_ofReal]
      exact (map_mul (algebraMap ℝ ℂ) (f.eval r) (g.eval r)).symm
    rw [hcongr, ofReal_multiset_sum]
  rw [hR] at h
  rw [h]
  ring

-- Theorem: a real number whose image in `ℂ` is a root of the mapped septic, and which is
-- neither `z` nor `z̄`, lies in `R`.
lemma mem_R_of_root {q : ℝ[X]} (hmon : q.Monic) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)))
    {x : ℝ} (hx : q.eval x = 0) (hxz : (x : ℂ) ≠ z)
    (hxz' : (x : ℂ) ≠ starRingEnd ℂ z) : x ∈ R := by
  have hqCne : (q.map (algebraMap ℝ ℂ)) ≠ 0 := (hmon.map (algebraMap ℝ ℂ)).ne_zero
  have hxrootC : (q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hx, map_zero]
  have hmem : (algebraMap ℝ ℂ x) ∈ (q.map (algebraMap ℝ ℂ)).roots :=
    (Polynomial.mem_roots hqCne).mpr hxrootC
  rw [hroots] at hmem
  simp only [Multiset.mem_cons] at hmem
  rcases hmem with h | h | h
  · exact absurd h hxz
  · exact absurd h hxz'
  · exact (Multiset.mem_map_of_injective (algebraMap ℝ ℂ).injective).mp h

-- Theorem: every element of `R` is a real root of `q`.
lemma root_of_mem_R {q : ℝ[X]} (hmon : q.Monic) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ))) :
    ∀ r ∈ R, q.eval r = 0 := by
  intro r hr
  have hqCne : (q.map (algebraMap ℝ ℂ)) ≠ 0 := (hmon.map (algebraMap ℝ ℂ)).ne_zero
  have hmemR : (algebraMap ℝ ℂ r) ∈ R.map (algebraMap ℝ ℂ) :=
    (Multiset.mem_map_of_injective (algebraMap ℝ ℂ).injective).mpr hr
  have hmem : (algebraMap ℝ ℂ r) ∈ (q.map (algebraMap ℝ ℂ)).roots := by
    rw [hroots]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hmemR)
  have hroot := (Polynomial.mem_roots hqCne).mp hmem
  change (q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = 0 at hroot
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply] at hroot
  exact (algebraMap ℝ ℂ).injective (by simpa using hroot)

-- Theorem: a degree-`≤ 6` real polynomial vanishing at all complex roots of a separable
-- septic `q` is zero.
lemma eq_zero_of_vanishes_on_roots {q H : ℝ[X]} (hnat : q.natDegree = 7) (hsep : q.Separable)
    (hHdeg : H.natDegree ≤ 6)
    (h : ∀ w : ℂ, w ∈ (q.map (algebraMap ℝ ℂ)).roots →
      (H.map (algebraMap ℝ ℂ)).eval w = 0) : H = 0 := by
  have hnodup : (q.map (algebraMap ℝ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots (hsep.map)
  have hcardC : (q.map (algebraMap ℝ ℂ)).roots.card = 7 := by
    rw [show (q.map (algebraMap ℝ ℂ)).roots.card
        = (q.map (algebraMap ℝ ℂ)).natDegree from
      (IsAlgClosed.splits (q.map (algebraMap ℝ ℂ))).natDegree_eq_card_roots.symm]
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, hnat]
  have hcardfin : Fintype.card ((q.map (algebraMap ℝ ℂ)).roots.toFinset) = 7 := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcardC]
  have hdegC : (H.map (algebraMap ℝ ℂ)).natDegree < 7 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    omega
  refine (Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective).mp ?_
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (H.map (algebraMap ℝ ℂ)) (ι := (q.map (algebraMap ℝ ℂ)).roots.toFinset)
    (f := Subtype.val) Subtype.val_injective ?_ ?_
  · intro w
    exact h (w : ℂ) (Multiset.mem_toFinset.mp w.2)
  · rw [hcardfin]; exact hdegC

-- Theorem: `bilin (Hmat q) (vecOf f) (vecOf g) = trace (N_f N_g)`.
lemma bilin_Hmat_vecOf (q : ℝ[X]) (f g : ℝ[X]) (hf : f.natDegree ≤ 6)
    (hg : g.natDegree ≤ 6) :
    bilin (Hmat q) (vecOf f) (vecOf g)
      = Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)) := by
  have hfg : (f + g).natDegree ≤ 6 :=
    le_trans (Polynomial.natDegree_add_le f g) (max_le hf hg)
  have h1 := qform_add (Hmat q) (Hmat_symm q) (vecOf f) (vecOf g)
  have hv : vecOf f + vecOf g = vecOf (f + g) := by
    ext i
    simp [vecOf, Polynomial.coeff_add]
  rw [hv] at h1
  have hqf : qform (Hmat q) (vecOf f)
      = Matrix.trace ((aeval (companion7 q) f) ^ 2) := by
    rw [qform_Hmat_eq_hermiteForm, hermiteForm_eq_trace_sq, polyOfVec_vecOf hf]
  have hqg : qform (Hmat q) (vecOf g)
      = Matrix.trace ((aeval (companion7 q) g) ^ 2) := by
    rw [qform_Hmat_eq_hermiteForm, hermiteForm_eq_trace_sq, polyOfVec_vecOf hg]
  have hqfg : qform (Hmat q) (vecOf (f + g))
      = Matrix.trace ((aeval (companion7 q) (f + g)) ^ 2) := by
    rw [qform_Hmat_eq_hermiteForm, hermiteForm_eq_trace_sq, polyOfVec_vecOf hfg]
  rw [hqfg, hqf, hqg] at h1
  have htr := trace_sq_smul_add (aeval (companion7 q) f) (aeval (companion7 q) g) 1 1
  have hmap : aeval (companion7 q) (f + g)
      = (1 : ℝ) • aeval (companion7 q) f + (1 : ℝ) • aeval (companion7 q) g := by
    rw [map_add]; simp
  rw [hmap] at h1
  rw [h1] at htr
  simp only [one_pow, one_mul] at htr
  linarith

/-! ### The complex product identity

For `ω = -1/2 + (√3/2) i` and any `u`, the two numbers `y + u ω + ū ω̄` and
`y + u ω̄ + ū ω` multiply to `(y - Re u)² - 3 (Im u)²`. -/

/-- The conjugate-free part of the product identity. -/
lemma omegaC_prod_aux (y : ℝ) (u : ℂ) :
    (y - starRingEnd ℂ u) * (y - u) + (u - starRingEnd ℂ u) ^ 2
      = (((y - u.re) ^ 2 - 3 * u.im ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, pow_two]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.sub_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, pow_two]
    ring

-- Theorem: `(y + u ω + ū ω̄)(y + u ω̄ + ū ω) = (y - Re u)² - 3 (Im u)²`.
lemma omegaC_prod (y : ℝ) (u : ℂ) :
    ((y : ℂ) + u * omegaC + starRingEnd ℂ u * starRingEnd ℂ omegaC)
      * ((y : ℂ) + u * starRingEnd ℂ omegaC + starRingEnd ℂ u * omegaC)
      = (((y - u.re) ^ 2 - 3 * u.im ^ 2 : ℝ) : ℂ) := by
  have hw' : starRingEnd ℂ omegaC = -1 - omegaC := by
    rw [← omegaC_add_conj]; ring
  have hwsq : omegaC + omegaC ^ 2 = -1 := by
    have h := omegaC_mul_conj
    rw [hw'] at h
    linear_combination -h
  have hmain : ((y : ℂ) + u * omegaC + starRingEnd ℂ u * starRingEnd ℂ omegaC)
      * ((y : ℂ) + u * starRingEnd ℂ omegaC + starRingEnd ℂ u * omegaC)
      = (y - starRingEnd ℂ u) * (y - u) + (u - starRingEnd ℂ u) ^ 2 := by
    rw [hw']
    linear_combination (-(u - starRingEnd ℂ u) ^ 2) * hwsq
  rw [hmain, omegaC_prod_aux]

/-! ### One direction from one prescribed value at `z`

For a real root `x_j ∈ R` and a complex value `c` with `c + c̄ = -1`, `c c̄ = 1`, the
Lagrange polynomial `X` of `exists_lagrange_value` gives a direction `d = coeff6 (vecOf X)`
on the cone with `p3vec q (Lcomb q d) = 3`, together with `b = bilin (Gram q) P₀ d` satisfying
`b = F₀(x_j) + u c + ū c̄` with `u = F₀(z)`. -/

-- Theorem: for a prescribed value `c` at `z` on the unit circle with `Re c = -1/2`, the
-- Lagrange polynomial yields a cone direction `d` with `p3vec = 3` and the stated bilinear
-- value against `P₀`.
lemma exists_direction_of_value {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)))
    (hRroot : ∀ r ∈ R, q.eval r = 0) (hRnodup : R.Nodup)
    {P₀ : Fin 6 → ℝ} {xj : ℝ} (hxjmem : xj ∈ R)
    {c : ℂ} (hc1 : c + starRingEnd ℂ c = -1) (hc2 : c * starRingEnd ℂ c = 1) :
    ∃ (d : Fin 6 → ℝ) (b : ℝ),
      qform (Gram q) d = 0 ∧
      p3vec q (Lcomb q d) = 3 ∧
      (b : ℂ) = (((polyOfVec (Lcomb q P₀)).eval xj : ℝ) : ℂ)
        + ((polyOfVec (Lcomb q P₀)).map (algebraMap ℝ ℂ)).eval z * c
        + starRingEnd ℂ (((polyOfVec (Lcomb q P₀)).map (algebraMap ℝ ℂ)).eval z)
          * starRingEnd ℂ c ∧
      bilin (Gram q) P₀ d = b := by
  classical
  set F0 : ℝ[X] := polyOfVec (Lcomb q P₀) with hF0
  have hF0deg : F0.natDegree ≤ 6 := by rw [hF0]; exact polyOfVec_natDegree_le _
  have hvecF0 : vecOf F0 = Lcomb q P₀ := by rw [hF0, vecOf_polyOfVec]
  have hxjroot : q.eval xj = 0 := hRroot xj hxjmem
  have hxjz : (algebraMap ℝ ℂ xj) ≠ z := fun h => hzim (by rw [← h]; simp)
  have hxjz' : (algebraMap ℝ ℂ xj) ≠ starRingEnd ℂ z := fun h => by
    have hc := congrArg Complex.im h
    simp at hc
    exact hzim (by linarith)
  obtain ⟨X, hXdeg, hXz, hXzbar, hXxj, hXother, ht1, ht2, ht3⟩ :=
    exists_lagrange_value hmon hnat hsep hz hzim hone hxjroot hxjz hxjz' hc1 hc2
  have hp1X : p1vec q (vecOf X) = 0 := by
    rw [p1vec_vecOf q X hXdeg, ht1]
  have hLcombX : Lcomb q (coeff6 (vecOf X)) = vecOf X := Lcomb_coeff6 q hp1X
  have hqform_d : qform (Gram q) (coeff6 (vecOf X)) = 0 := by
    rw [← qform_Hmat_Lcomb q (coeff6 (vecOf X)), hLcombX, qform_Hmat_eq_hermiteForm,
      hermiteForm_eq_trace_sq, polyOfVec_vecOf hXdeg, ht2]
  have hp3_d : p3vec q (Lcomb q (coeff6 (vecOf X))) = 3 := by
    rw [hLcombX, p3vec, polyOfVec_vecOf hXdeg, ht3]
  have hRval : (R.map (fun r => F0.eval r * X.eval r)).sum = F0.eval xj := by
    have hReq : R = xj ::ₘ R.erase xj := (Multiset.cons_erase hxjmem).symm
    rw [hReq]
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have hhead : F0.eval xj * X.eval xj = F0.eval xj := by rw [hXxj, mul_one]
    have htail : ((R.erase xj).map (fun r => F0.eval r * X.eval r)).sum = 0 := by
      have hmap0 : (R.erase xj).map (fun r => F0.eval r * X.eval r)
          = (R.erase xj).map (fun _ => (0 : ℝ)) := by
        apply Multiset.map_congr rfl
        intro r hr
        have hrne : r ≠ xj := (hRnodup.mem_erase_iff.mp hr).1
        have hroot : q.eval r = 0 := hRroot r (Multiset.mem_of_mem_erase hr)
        rw [hXother r hroot hrne, mul_zero]
      rw [hmap0, Multiset.sum_map_zero]
    rw [hhead, htail, add_zero]
  have htrace_eq : Matrix.trace ((aeval (companion7 q) F0) * (aeval (companion7 q) X))
      = bilin (Gram q) P₀ (coeff6 (vecOf X)) := by
    rw [← bilin_Hmat_vecOf q F0 X hF0deg hXdeg]
    conv_lhs => rw [hvecF0, ← hLcombX]
    rw [bilin_Hmat_Lcomb]
  have hsplit := ofReal_trace_mul_eq_sum q F0 X hmon hnat hsep hroots
  rw [hRval, hXz, hXzbar, eval_map_conj F0 z] at hsplit
  refine ⟨coeff6 (vecOf X), bilin (Gram q) P₀ (coeff6 (vecOf X)), hqform_d, hp3_d, ?_,
    rfl⟩
  rw [← htrace_eq]
  exact hsplit

-- Theorem: the real arithmetic behind the sign certificate.  If `y₁² + y₂² ≤ S` and
-- `γ² = α² + S/2`, then either one of the two products `b_j = (y_j - α)² - 3γ²` is negative,
-- or `S = α = γ = 0` (the degenerate case excluded by `F₀ ≠ 0`).
set_option maxHeartbeats 400000 in
-- the `nlinarith` chain on the products `(y - α)² - 3γ²` needs more than the default budget
private lemma sign_neg_aux {y1 y2 α γ S b1 b2 : ℝ}
    (hS : y1 ^ 2 + y2 ^ 2 ≤ S) (hg : γ ^ 2 = α ^ 2 + S / 2)
    (h1 : b1 = (y1 - α) ^ 2 - 3 * γ ^ 2) (h2 : b2 = (y2 - α) ^ 2 - 3 * γ ^ 2) :
    b1 < 0 ∨ b2 < 0 ∨ (S = 0 ∧ α = 0 ∧ γ = 0) := by
  by_cases hb1 : b1 < 0
  · exact Or.inl hb1
  by_cases hb2 : b2 < 0
  · exact Or.inr (Or.inl hb2)
  push Not at hb1 hb2
  have hb1' : b1 = y1 ^ 2 - 2 * α * y1 - 2 * α ^ 2 - (3 / 2) * S := by rw [h1, hg]; ring
  have hb2' : b2 = y2 ^ 2 - 2 * α * y2 - 2 * α ^ 2 - (3 / 2) * S := by rw [h2, hg]; ring
  have hbd1 : b1 ≤ -((1 / 2) * (y1 + 2 * α) ^ 2 + (3 / 2) * y2 ^ 2) := by
    rw [hb1']; nlinarith [hS]
  have hbd2 : b2 ≤ -((1 / 2) * (y2 + 2 * α) ^ 2 + (3 / 2) * y1 ^ 2) := by
    rw [hb2']; nlinarith [hS]
  have e1 : (1 / 2) * (y1 + 2 * α) ^ 2 + (3 / 2) * y2 ^ 2 = 0 := by
    nlinarith [hb1, hbd1, sq_nonneg (y1 + 2 * α), sq_nonneg y2]
  have e2 : (1 / 2) * (y2 + 2 * α) ^ 2 + (3 / 2) * y1 ^ 2 = 0 := by
    nlinarith [hb2, hbd2, sq_nonneg (y2 + 2 * α), sq_nonneg y1]
  have hy1 : y1 = 0 := by
    have h2' : y1 ^ 2 = 0 := by nlinarith [e2, sq_nonneg (y2 + 2 * α), sq_nonneg y1]
    exact sq_eq_zero_iff.mp h2'
  have hy2 : y2 = 0 := by
    have h2' : y2 ^ 2 = 0 := by nlinarith [e1, sq_nonneg (y1 + 2 * α), sq_nonneg y2]
    exact sq_eq_zero_iff.mp h2'
  have hα0 : α = 0 := by
    have h2' : (2 * α) ^ 2 = 0 := by nlinarith [e1, hy1, hy2]
    have h3 : 2 * α = 0 := sq_eq_zero_iff.mp h2'
    linarith
  have hb1zero : b1 = 0 := by nlinarith [hb1, hbd1, e1]
  have hS0 : S = 0 := by nlinarith [hb1', hb1zero, hy1, hy2, hα0]
  have hγ0 : γ = 0 := by
    have h1' : γ ^ 2 = 0 := by rw [hg, hS0, hα0]; ring
    exact sq_eq_zero_iff.mp h1'
  exact Or.inr (Or.inr ⟨hS0, hα0, hγ0⟩)

-- Theorem: on the light cone through a nonzero `P₀` the reduced cubic `p3vec` takes both
-- signs.  This is the sign certificate of `PLAN-degree7-s1.md` §3 Step 3.
theorem exists_sign_change {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable)
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {P₀ : Fin 6 → ℝ} (hQ₀ : qform (Gram q) P₀ = 0) (hP₀ne : P₀ ≠ 0) :
    ∃ dplus dminus : Fin 6 → ℝ,
      0 < p3vec q (Lcomb q (stereo (Gram q) P₀ dplus)) ∧
      p3vec q (Lcomb q (stereo (Gram q) P₀ dminus)) < 0 := by
  classical
  obtain ⟨R, hRnodup, hRcard, hroots⟩ :=
    roots_eq_pair_add_real hmon hnat hsep hz hzim hone
  have hRroot : ∀ r ∈ R, q.eval r = 0 := root_of_mem_R hmon hroots
  have hne1 : R ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hRcard; omega
  obtain ⟨x1, hx1mem⟩ := Multiset.exists_mem_of_ne_zero hne1
  have hx1erase : 0 < (R.erase x1).card := by
    rw [Multiset.card_erase_of_mem hx1mem, hRcard]; norm_num
  have hne2 : R.erase x1 ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hx1erase; omega
  obtain ⟨x2, hx2erase⟩ := Multiset.exists_mem_of_ne_zero hne2
  have hx2mem : x2 ∈ R := Multiset.mem_of_mem_erase hx2erase
  have hx21 : x2 ≠ x1 := (hRnodup.mem_erase_iff.mp hx2erase).1
  set F0 : ℝ[X] := polyOfVec (Lcomb q P₀) with hF0
  have hF0deg : F0.natDegree ≤ 6 := by rw [hF0]; exact polyOfVec_natDegree_le _
  have hF0ne : F0 ≠ 0 := by
    rw [hF0]
    exact polyOfVec_ne_zero (fun h => hP₀ne (Lcomb_injective q h))
  have hvecF0 : vecOf F0 = Lcomb q P₀ := by rw [hF0, vecOf_polyOfVec]
  set S : ℝ := (R.map (fun r => (F0.eval r) ^ 2)).sum with hS
  set u : ℂ := (F0.map (algebraMap ℝ ℂ)).eval z with hu
  set α : ℝ := u.re with hα
  set γ : ℝ := u.im with hγ
  have htrF0sq : Matrix.trace ((aeval (companion7 q) F0) ^ 2) = 0 := by
    have h1 : qform (Hmat q) (vecOf F0) = 0 := by
      rw [hvecF0, qform_Hmat_Lcomb q P₀, hQ₀]
    rw [qform_Hmat_eq_hermiteForm, hermiteForm_eq_trace_sq,
      polyOfVec_vecOf hF0deg] at h1
    exact h1
  have hsplit2 := ofReal_trace_mul_eq_sum q F0 F0 hmon hnat hsep hroots
  have hzero : algebraMap ℝ ℂ
      (Matrix.trace ((aeval (companion7 q) F0) * (aeval (companion7 q) F0))) = 0 := by
    rw [← pow_two, htrF0sq, map_zero]
  rw [hzero, eval_map_conj F0 z, ← hu] at hsplit2
  have hSsum : (R.map (fun r => F0.eval r * F0.eval r)).sum = S := by
    rw [hS]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro r _
    rw [sq]
  have hpair : u * u + starRingEnd ℂ u * starRingEnd ℂ u
      = ((2 * (u ^ 2).re : ℝ) : ℂ) := by
    have h2 : starRingEnd ℂ u * starRingEnd ℂ u = starRingEnd ℂ (u * u) := by
      rw [map_mul]
    rw [h2, ← sq, Complex.add_conj]
  have hSreal : S + 2 * (u ^ 2).re = 0 := by
    have h5 : ((R.map (fun r => F0.eval r * F0.eval r)).sum : ℂ)
        + (u * u + starRingEnd ℂ u * starRingEnd ℂ u) = 0 := by
      rw [← add_assoc]; exact hsplit2.symm
    rw [hSsum, hpair] at h5
    exact_mod_cast h5
  have hu2re : (u ^ 2).re = u.re ^ 2 - u.im ^ 2 := by
    rw [sq, Complex.mul_re]; ring
  have hgamma : γ ^ 2 = α ^ 2 + S / 2 := by
    rw [hu2re, ← hα, ← hγ] at hSreal
    linarith
  have hSbound : (F0.eval x1) ^ 2 + (F0.eval x2) ^ 2 ≤ S := by
    have hR1 : R = x1 ::ₘ R.erase x1 := (Multiset.cons_erase hx1mem).symm
    have hx2e : x2 ∈ R.erase x1 := hRnodup.mem_erase_iff.mpr ⟨hx21, hx2mem⟩
    have hR2 : R.erase x1 = x2 ::ₘ (R.erase x1).erase x2 :=
      (Multiset.cons_erase hx2e).symm
    rw [hS, hR1, hR2]
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have hnn : 0 ≤ (((R.erase x1).erase x2).map (fun r => (F0.eval r) ^ 2)).sum :=
      Multiset.sum_nonneg (fun s hs => by
        obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hs
        exact sq_nonneg _)
    linarith
  have homega1c : starRingEnd ℂ omegaC + starRingEnd ℂ (starRingEnd ℂ omegaC) = -1 := by
    simpa [star_star, add_comm] using omegaC_add_conj
  have homega2c : starRingEnd ℂ omegaC * starRingEnd ℂ (starRingEnd ℂ omegaC) = 1 := by
    simpa [star_star, mul_comm] using omegaC_mul_conj
  obtain ⟨d1w, b1w, hd1w, hp1w, hb1w, hbl1w⟩ :=
    exists_direction_of_value (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup hx1mem
      omegaC_add_conj omegaC_mul_conj
  obtain ⟨d1c, b1c, hd1c, hp1c, hb1c, hbl1c⟩ :=
    exists_direction_of_value (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup hx1mem
      homega1c homega2c
  obtain ⟨d2w, b2w, hd2w, hp2w, hb2w, hbl2w⟩ :=
    exists_direction_of_value (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup hx2mem
      omegaC_add_conj omegaC_mul_conj
  obtain ⟨d2c, b2c, hd2c, hp2c, hb2c, hbl2c⟩ :=
    exists_direction_of_value (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup hx2mem
      homega1c homega2c
  have hss : (starRingEnd ℂ) ((starRingEnd ℂ) omegaC) = omegaC := by
    rw [starRingEnd_apply, starRingEnd_apply, star_star]
  have hQ1 : b1w * b1c = (F0.eval x1 - α) ^ 2 - 3 * γ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul]
    rw [hb1w, hb1c, hss]
    rw [← hF0, ← hu]
    rw [omegaC_prod (F0.eval x1) u]
  have hQ2 : b2w * b2c = (F0.eval x2 - α) ^ 2 - 3 * γ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul]
    rw [hb2w, hb2c, hss]
    rw [← hF0, ← hu]
    rw [omegaC_prod (F0.eval x2) u]
  have mk : ∀ (d : Fin 6 → ℝ) (b : ℝ), qform (Gram q) d = 0 →
      p3vec q (Lcomb q d) = 3 → bilin (Gram q) P₀ d = b →
      p3vec q (Lcomb q (stereo (Gram q) P₀ d)) = -24 * b ^ 3 := by
    intro d b hd hp hb
    rw [p3vec_Lcomb_stereo_of_qform_zero q hd, hb, hp]
    ring
  have hsome : b1w * b1c < 0 ∨ b2w * b2c < 0 := by
    rcases sign_neg_aux hSbound hgamma hQ1 hQ2 with h | h | ⟨hS0, hα0, hγ0⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hu0 : u = 0 := by
        apply Complex.ext
        · change u.re = 0; rw [← hα]; exact hα0
        · change u.im = 0; rw [← hγ]; exact hγ0
      have hFr : ∀ r ∈ R, F0.eval r = 0 := by
        intro r hr
        have hnn : ∀ s ∈ R.map (fun r => (F0.eval r) ^ 2), (0 : ℝ) ≤ s := by
          intro s hs
          obtain ⟨r', _, rfl⟩ := Multiset.mem_map.mp hs
          exact sq_nonneg _
        have hsum0 : (R.map (fun r => (F0.eval r) ^ 2)).sum = 0 := by
          rw [← hS]; exact hS0
        exact sq_eq_zero_iff.mp
          (Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hnn hsum0 _
            (Multiset.mem_map_of_mem _ hr))
      have hF00 : F0 = 0 := by
        refine eq_zero_of_vanishes_on_roots hnat hsep hF0deg ?_
        intro w hw
        rw [hroots] at hw
        rcases Multiset.mem_cons.mp hw with hw | hw
        · subst hw; rw [← hu]; exact hu0
        · rcases Multiset.mem_cons.mp hw with hw | hw
          · subst hw; rw [eval_map_conj F0 z, ← hu, hu0, map_zero]
          · obtain ⟨r, hr, hrw⟩ := Multiset.mem_map.mp hw
            rw [← hrw, eval_map_ofReal, hFr r hr]; simp
      exact hF0ne hF00
  have key1 : ∀ b : ℝ, b < 0 → (0 : ℝ) < -24 * b ^ 3 := by
    intro b hb; nlinarith [hb, sq_pos_of_ne_zero (ne_of_lt hb)]
  have key2 : ∀ b : ℝ, 0 < b → -24 * b ^ 3 < 0 := by
    intro b hb; nlinarith [hb, sq_pos_of_ne_zero (ne_of_gt hb)]
  rcases hsome with hneg | hneg
  · rcases mul_neg_iff.mp hneg with ⟨hbw, hbc⟩ | ⟨hbw, hbc⟩
    · refine ⟨d1c, d1w, ?_, ?_⟩
      · rw [mk d1c b1c hd1c hp1c hbl1c]; exact key1 b1c hbc
      · rw [mk d1w b1w hd1w hp1w hbl1w]; exact key2 b1w hbw
    · refine ⟨d1w, d1c, ?_, ?_⟩
      · rw [mk d1w b1w hd1w hp1w hbl1w]; exact key1 b1w hbw
      · rw [mk d1c b1c hd1c hp1c hbl1c]; exact key2 b1c hbc
  · rcases mul_neg_iff.mp hneg with ⟨hbw, hbc⟩ | ⟨hbw, hbc⟩
    · refine ⟨d2c, d2w, ?_, ?_⟩
      · rw [mk d2c b2c hd2c hp2c hbl2c]; exact key1 b2c hbc
      · rw [mk d2w b2w hd2w hp2w hbl2w]; exact key2 b2w hbw
    · refine ⟨d2w, d2c, ?_, ?_⟩
      · rw [mk d2w b2w hd2w hp2w hbl2w]; exact key1 b2w hbw
      · rw [mk d2c b2c hd2c hp2c hbl2c]; exact key2 b2c hbc

end

end Pconstructible
