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

import Pptc.Octic.Roots

/-! # Pptc.Octic.Cone

The light cone of the trace form on the `7`-dimensional space `{Tr φ = 0}`, the
degree-8 analogue of the corresponding block of `Pptc.DegreeSeven`
(`Pptc/Octic/PLAN.md` §2.5).

The quadratic form `Q = qform (Gram8 q)` is the restriction of the trace form
`φ ↦ Tr (φ(C_q)²)` to the seven-dimensional hyperplane `{p1 = 0}`. If `q` has `s`
conjugate pairs (and hence `8 - 2s` real roots, counting the pair `z, z̄` as a
`2`-plane of signature `(1, 1)`), then `Q` has signature `(7 - s, s)`:
each real root contributes `+1` and each conjugate pair contributes a
`(1, 1)`-plane. So for `s ≥ 2` there is a negative `2`-plane, while for `s = 1`
the form is `(6, 1)` and no isotropic plane exists.

This file provides

* the stereographic parametrisation `stereoN` of the cone `{Q = 0}` through a cone
  point `P₀`, in the dimension-free form needed downstream at `n = 7`;
* `neg_dir_of_pair8` / `pos_dir_of_pair8`: from two distinct conjugate pairs, a
  definite `2`-plane in `{p1 = 0}` — read off from the trace identities for the
  coefficient vectors `coeff7 (vecOf8 f)`;
* the construction of a P-constructible nonzero cone point `P₀`
  (`exists_cone_point8`), and of a P-constructible isotropic vector orthogonal to a
  given cone point and independent of it (`exists_isotropic_orth_Pconstructible8`),
  which is exactly what the `s ≥ 2` route needs.

The stereographic formulas, the projection lemma and the continuity statements never
use the dimension, so they are stated once here for `Fin n`.
-/

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### The stereographic parametrisation, in arbitrary dimension

For a cone point `P₀` (`Q P₀ = 0`) and a direction `x`, the second intersection of the
line `P₀ + t x` with the cone `{Q = 0}` is `v x / Q x`, where
`v x = Q x • P₀ - 2 B P₀ x • x`.  No square root is needed because the `t = 0` root is
already known. -/

/-- The second intersection of the cone through `P₀` with the line `P₀ + t x`, scaled by
`Q x`: `Q x • P₀ - 2 B P₀ x • x`. -/
def stereoN {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P₀ x : Fin n → ℝ) : Fin n → ℝ :=
  qform A x • P₀ - (2 * bilin A P₀ x) • x

-- Theorem (S1): `stereoN` always lands on the cone.
theorem qform_stereoN_eq_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A)
    {P₀ : Fin n → ℝ} (hP₀ : qform A P₀ = 0) (x : Fin n → ℝ) :
    qform A (stereoN A P₀ x) = 0 := by
  rw [show stereoN A P₀ x = qform A x • P₀ + (-(2 * bilin A P₀ x)) • x by
    rw [stereoN, sub_eq_add_neg, ← neg_smul]]
  rw [qform_smul_add A hA (qform A x) (-(2 * bilin A P₀ x)) P₀ x]
  simp only [hP₀, mul_zero, zero_add]
  ring

-- Theorem (S2): `stereoN` vanishes to order two along the ray of `P₀`: shifting `δ` by
-- any multiple of `P₀` only rescales `stereoN`.
theorem stereoN_smul_add_smul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A)
    {P₀ : Fin n → ℝ} (hP₀ : qform A P₀ = 0) (c ε : ℝ) (δ : Fin n → ℝ) :
    stereoN A P₀ (c • P₀ + ε • δ) = ε ^ 2 • stereoN A P₀ δ := by
  have hBsym : bilin A P₀ P₀ = 0 := by
    rw [show bilin A P₀ P₀ = qform A P₀ from rfl, hP₀]
  have hQx : qform A (c • P₀ + ε • δ) =
      2 * c * ε * bilin A P₀ δ + ε ^ 2 * qform A δ := by
    rw [qform_smul_add A hA c ε P₀ δ, hP₀]
    ring
  have hBx : bilin A P₀ (c • P₀ + ε • δ) = ε * bilin A P₀ δ := by
    rw [bilin_add_right, bilin_smul_right, bilin_smul_right, hBsym]
    ring
  rw [show stereoN A P₀ (c • P₀ + ε • δ)
      = qform A (c • P₀ + ε • δ) • P₀
        + (-(2 * bilin A P₀ (c • P₀ + ε • δ))) • (c • P₀ + ε • δ) by
    rw [stereoN, sub_eq_add_neg, ← neg_smul]]
  rw [hQx, hBx]
  rw [show stereoN A P₀ δ
      = qform A δ • P₀ + (-(2 * bilin A P₀ δ)) • δ by
    rw [stereoN, sub_eq_add_neg, ← neg_smul]]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

-- Theorem: there is a P-constructible affine projection onto the hyperplane
-- `bilin A P₀ · = 0`, of the form `y ↦ c • y - bilin A P₀ y • u` with `c ≠ 0`.
theorem exists_orth_projectionN {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, PConstructible (A i j)) {P₀ : Fin n → ℝ}
    (hP₀ : ∀ i, PConstructible (P₀ i)) :
    ∃ (c : ℝ) (u : Fin n → ℝ), c ≠ 0 ∧ PConstructible c ∧
      (∀ i, PConstructible (u i)) ∧
      ∀ y, bilin A P₀ (c • y - bilin A P₀ y • u) = 0 := by
  classical
  have hsingle : ∀ i j : Fin n,
      PConstructible ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) := by
    intro i j
    by_cases hji : j = i
    · subst hji; rw [Pi.single_eq_same]; exact PConstructible.base_one
    · rw [Pi.single_eq_of_ne hji]; exact zero_Pconstructible
  by_cases h : ∃ i : Fin n, bilin A P₀ (Pi.single i (1 : ℝ)) ≠ 0
  · obtain ⟨i, hi⟩ := h
    refine ⟨bilin A P₀ (Pi.single i (1 : ℝ)), Pi.single i (1 : ℝ), hi,
      bilin_Pconstructible hA hP₀ (hsingle i), hsingle i, ?_⟩
    intro y
    rw [sub_eq_add_neg, bilin_add_right, bilin_smul_right,
      show -(bilin A P₀ y • Pi.single i (1 : ℝ))
          = (-(bilin A P₀ y)) • Pi.single i (1 : ℝ) by rw [neg_smul],
      bilin_smul_right]
    ring
  · push Not at h
    refine ⟨1, 0, one_ne_zero, PConstructible.base_one, fun i => zero_Pconstructible, ?_⟩
    intro y
    have hy : y = ∑ i : Fin n, y i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      ext j
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, mul_one]
      · intro k _ hkj
        rw [Pi.single_eq_of_ne (Ne.symm hkj), mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have hzero : bilin A P₀ y = 0 := by
      rw [hy, bilin_sum_right]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [bilin_smul_right, h i, mul_zero]
    simp [hzero]

-- Theorem: if `Q = qform A` is negative definite on the real plane spanned by `v₁, v₂`,
-- then there is a P-constructible `e` with `bilin A P₀ e = 0` and `Q e < 0`.
theorem exists_orth_neg_PconstructibleN {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, PConstructible (A i j)) {P₀ : Fin n → ℝ}
    (hP₀ : ∀ i, PConstructible (P₀ i)) {v₁ v₂ : Fin n → ℝ}
    (hdef : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → qform A (a • v₁ + b • v₂) < 0) :
    ∃ e : Fin n → ℝ, (∀ i, PConstructible (e i)) ∧ bilin A P₀ e = 0 ∧
      qform A e < 0 := by
  classical
  obtain ⟨c, u, hcne, hcP, huP, hproj⟩ := exists_orth_projectionN hA hP₀
  have hreal : ∃ e₀ : Fin n → ℝ, bilin A P₀ e₀ = 0 ∧ qform A e₀ < 0 := by
    by_cases hb : bilin A P₀ v₁ = 0 ∧ bilin A P₀ v₂ = 0
    · exact ⟨v₁, hb.1, by simpa using hdef 1 0 (Or.inl one_ne_zero)⟩
    · refine ⟨bilin A P₀ v₂ • v₁ - bilin A P₀ v₁ • v₂, ?_, ?_⟩
      · rw [sub_eq_add_neg, bilin_add_right, bilin_smul_right,
          show -(bilin A P₀ v₁ • v₂) = (-(bilin A P₀ v₁)) • v₂ by rw [neg_smul],
          bilin_smul_right]
        ring
      · have hab : bilin A P₀ v₂ ≠ 0 ∨ (-(bilin A P₀ v₁)) ≠ 0 := by
          by_contra hc
          push Not at hc
          exact hb ⟨neg_eq_zero.mp hc.2, hc.1⟩
        have hq := hdef (bilin A P₀ v₂) (-(bilin A P₀ v₁)) hab
        have heq : bilin A P₀ v₂ • v₁ - bilin A P₀ v₁ • v₂
            = bilin A P₀ v₂ • v₁ + (-(bilin A P₀ v₁)) • v₂ := by
          rw [sub_eq_add_neg, neg_smul]
        rwa [heq]
  obtain ⟨e₀, hBe₀, he₀Q⟩ := hreal
  set π : (Fin n → ℝ) → (Fin n → ℝ) := fun y => c • y - (bilin A P₀ y) • u with hπ
  have hcont : Continuous (fun y : Fin n → ℝ => -qform A (π y)) := by
    have h2 : Continuous (fun y : Fin n → ℝ => c • y - (bilin A P₀ y) • u) := by
      have h1 : Continuous (fun y : Fin n → ℝ => bilin A P₀ y) := continuous_bilin A P₀
      have hc : Continuous (fun y : Fin n → ℝ => c • y) := continuous_id.const_smul c
      have hu : Continuous (fun y : Fin n → ℝ => (bilin A P₀ y) • u) :=
        h1.smul (continuous_const : Continuous (fun _ : Fin n → ℝ => u))
      exact hc.sub hu
    exact ((continuous_qform A).neg).comp h2
  have hπe₀ : π e₀ = c • e₀ := by
    change c • e₀ - (bilin A P₀ e₀) • u = c • e₀
    rw [hBe₀, zero_smul, sub_zero]
  have hx : 0 < -qform A (π e₀) := by
    rw [hπe₀, qform_smul]
    nlinarith [he₀Q, sq_pos_of_ne_zero hcne]
  obtain ⟨r, hr⟩ := exists_rat_vec_pos n hcont (x := e₀) hx
  set er : Fin n → ℝ := fun i => (r i : ℝ) with her
  have herP : ∀ i, PConstructible (er i) := fun i => rat_Pconstructible (r i)
  have hQer : qform A (π er) < 0 := neg_pos.mp hr
  refine ⟨π er, ?_, ?_, hQer⟩
  · intro i
    have hbil : PConstructible (bilin A P₀ er) := bilin_Pconstructible hA hP₀ herP
    rw [hπ]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.sub (PConstructible.mul hcP (herP i))
      (PConstructible.mul hbil (huP i))
  · simpa only [hπ] using hproj er

-- Theorem: `stereoN` is continuous in the direction.
theorem continuous_stereoN {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P₀ : Fin n → ℝ) :
    Continuous (fun d : Fin n → ℝ => stereoN A P₀ d) := by
  apply continuous_pi
  intro i
  have hq : Continuous (fun d : Fin n → ℝ => qform A d) := continuous_qform _
  have hb : Continuous (fun d : Fin n → ℝ => bilin A P₀ d) := continuous_bilin _ _
  have hfun : (fun d : Fin n → ℝ => stereoN A P₀ d i)
      = fun d => qform A d * P₀ i - (2 * bilin A P₀ d) * d i := by
    funext d
    simp only [stereoN, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact (hq.mul continuous_const).sub ((continuous_const.mul hb).mul (continuous_apply i))

/-! ### Negative and positive two-planes in `{p1 = 0}`

`exists_neg_pair8` / `exists_pos_pair8` produce polynomials supported on two distinct
conjugate pairs.  Their coefficient vectors land in `{p1vec8 = 0}` (after subtracting the
mean in the positive case), which lets us read them as coordinates in the `b`-basis; the
trace identities then say the restricted form `Gram8` is negative definite (resp. positive
definite) on the spanned plane. -/

-- Theorem: from two distinct conjugate pairs there is a P-constructible plane on which the
-- trace form is negative definite.
theorem neg_dir_of_pair8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z w : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ v1 v2 : Fin 7 → ℝ,
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → qform (Gram8 q) (a • v1 + b • v2) < 0 := by
  obtain ⟨f, g, hfdeg, hgdeg, htrf, htrg, hsqf, hsqg, hcross⟩ :=
    exists_neg_pair8 q hmon hnat hsep hz hzim hw hwim hzw hzw'
  refine ⟨coeff7 (vecOf8 f), coeff7 (vecOf8 g), ?_⟩
  have hpf : p1vec8 q (vecOf8 f) = 0 := by rw [p1vec8_vecOf8 q f hfdeg, htrf]
  have hpg : p1vec8 q (vecOf8 g) = 0 := by rw [p1vec8_vecOf8 q g hgdeg, htrg]
  intro a b hab
  rw [← qform_Gram8_Lcomb8, Lcomb8_smul_add, Lcomb8_coeff7 q hpf, Lcomb8_coeff7 q hpg]
  rw [qform_Hmat8_smul_add_vecOf8 q a b f g hfdeg hgdeg, aeval_C_mul_smul8,
    trace_sq_smul_add8, hsqf, hcross, hsqg]
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb]
  nlinarith

-- Theorem: from two distinct conjugate pairs there is a P-constructible plane on which the
-- trace form is positive definite (after subtracting the mean `2/8`).
theorem pos_dir_of_pair8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z w : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ v1 v2 : Fin 7 → ℝ,
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < qform (Gram8 q) (a • v1 + b • v2) := by
  obtain ⟨f, g, hfdeg, hgdeg, htrf, htrg, hsqf, hsqg, hcross⟩ :=
    exists_pos_pair8 q hmon hnat hsep hz hzim hw hwim hzw hzw'
  refine ⟨coeff7 (vecOf8 (f - C (2 / 8))), coeff7 (vecOf8 (g - C (2 / 8))), ?_⟩
  have hf'deg : (f - C (2 / 8)).natDegree ≤ 7 := by
    refine le_trans (Polynomial.natDegree_sub_le f (C (2 / 8))) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hfdeg
  have hg'deg : (g - C (2 / 8)).natDegree ≤ 7 := by
    refine le_trans (Polynomial.natDegree_sub_le g (C (2 / 8))) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hgdeg
  have hpf : p1vec8 q (vecOf8 (f - C (2 / 8))) = 0 := by
    rw [p1vec8_vecOf8 q (f - C (2 / 8)) hf'deg, aeval_sub_C8, Matrix.trace_sub,
      Matrix.trace_smul, htrf, Matrix.trace_one]
    norm_num
  have hpg : p1vec8 q (vecOf8 (g - C (2 / 8))) = 0 := by
    rw [p1vec8_vecOf8 q (g - C (2 / 8)) hg'deg, aeval_sub_C8, Matrix.trace_sub,
      Matrix.trace_smul, htrg, Matrix.trace_one]
    norm_num
  intro a b hab
  rw [← qform_Gram8_Lcomb8, Lcomb8_smul_add, Lcomb8_coeff7 q hpf, Lcomb8_coeff7 q hpg]
  rw [qform_Hmat8_smul_add_vecOf8 q a b (f - C (2 / 8)) (g - C (2 / 8)) hf'deg hg'deg,
    aeval_sub_C_smul_add8, trace_sq_sub_scalar8]
  have htrA : Matrix.trace
      (a • aeval (companionN (n := 8) q) f + b • aeval (companionN (n := 8) q) g)
      = 2 * a + 2 * b := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htrf, htrg]
    simp only [smul_eq_mul]
    ring
  have hsqA : Matrix.trace
      ((a • aeval (companionN (n := 8) q) f + b • aeval (companionN (n := 8) q) g) ^ 2)
      = 2 * a ^ 2 + 2 * b ^ 2 := by
    rw [trace_sq_smul_add8, hsqf, hcross, hsqg]
    ring
  rw [htrA, hsqA]
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), hpos]

/-! ### A P-constructible cone point

Given P-constructible directions `e` (negative) and `f` (positive) for the trace form,
the light cone meets the segment between them at a P-constructible point `P₀`. -/

-- Theorem: if `e` is P-constructible with `Q e < 0` and `f` is P-constructible with
-- `Q f > 0`, then the line `e + t f` meets the cone at a positive P-constructible parameter.
theorem exists_pos_isotropic_param8 (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {e f : Fin 7 → ℝ} (he : ∀ i, PConstructible (e i)) (hf : ∀ i, PConstructible (f i))
    (heQ : qform (Gram8 q) e < 0) (hfQ : 0 < qform (Gram8 q) f) :
    ∃ t : ℝ, PConstructible t ∧ 0 < t ∧ qform (Gram8 q) (e + t • f) = 0 := by
  have hG : ∀ i j, PConstructible (Gram8 q i j) := Gram8_Pconstructible q hq
  have hQe : PConstructible (qform (Gram8 q) e) := bilin_Pconstructible hG he he
  have hQf : PConstructible (qform (Gram8 q) f) := bilin_Pconstructible hG hf hf
  have hB : PConstructible (bilin (Gram8 q) e f) := bilin_Pconstructible hG he hf
  obtain ⟨t, htP, htpos, htroot⟩ := exists_pos_quadratic_root hQf hB hQe hfQ heQ
  refine ⟨t, htP, htpos, ?_⟩
  have hqform : qform (Gram8 q) (e + t • f) =
      qform (Gram8 q) e + 2 * t * bilin (Gram8 q) e f + t ^ 2 * qform (Gram8 q) f := by
    rw [show e + t • f = (1 : ℝ) • e + t • f by rw [one_smul]]
    rw [qform_smul_add (Gram8 q) (Gram8_symm q) 1 t e f]
    ring
  rw [hqform]
  linear_combination htroot

-- Theorem: if `e` is P-constructible with `Q e < 0` and `f` is P-constructible with
-- `Q f > 0`, then the cone `{Q = 0}` contains a P-constructible nonzero point.
theorem exists_isotropic_Pconstructible8 (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {e f : Fin 7 → ℝ} (he : ∀ i, PConstructible (e i)) (hf : ∀ i, PConstructible (f i))
    (heQ : qform (Gram8 q) e < 0) (hfQ : 0 < qform (Gram8 q) f) :
    ∃ P₀ : Fin 7 → ℝ,
      (∀ i, PConstructible (P₀ i)) ∧ qform (Gram8 q) P₀ = 0 ∧ P₀ ≠ 0 := by
  obtain ⟨t, htP, htpos, htroot⟩ := exists_pos_isotropic_param8 q hq he hf heQ hfQ
  refine ⟨e + t • f, fun i => PConstructible.add (he i) (PConstructible.mul htP (hf i)),
    htroot, ?_⟩
  intro h0
  have heq : e = -(t • f) := eq_neg_of_add_eq_zero_left h0
  have hQe' : qform (Gram8 q) (-(t • f)) < 0 := by rw [← heq]; exact heQ
  have hneg : qform (Gram8 q) (-(t • f)) = qform (Gram8 q) (t • f) := by
    rw [show -(t • f) = (-1 : ℝ) • (t • f) by rw [neg_one_smul], qform_smul]
    norm_num
  rw [hneg, qform_smul] at hQe'
  nlinarith [hfQ, sq_pos_of_pos htpos]

-- Theorem: a monic separable octic with a non-real root has a P-constructible nonzero
-- cone point for the trace form on `{p1 = 0}`.
theorem exists_cone_point8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k)) {z : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0) :
    ∃ P₀ : Fin 7 → ℝ, (∀ i, PConstructible (P₀ i)) ∧ qform (Gram8 q) P₀ = 0 ∧
      P₀ ≠ 0 := by
  obtain ⟨fneg, hfnegdeg, hfneg1, hfneg2⟩ := exists_neg_trace8 q hmon hnat hsep hz hzim
  obtain ⟨fpos, hfposdeg, hfpos1, hfpos2⟩ := exists_pos_trace8 q hmon hnat hsep hz hzim
  have hvecneg_p1 : p1vec8 q (vecOf8 fneg) = 0 := by
    rw [p1vec8_vecOf8 q fneg hfnegdeg, hfneg1]
  have hLneg : Lcomb8 q (coeff7 (vecOf8 fneg)) = vecOf8 fneg :=
    Lcomb8_coeff7 q hvecneg_p1
  have hQneg : qform (Gram8 q) (coeff7 (vecOf8 fneg)) = -2 := by
    rw [qform_Gram8_eq_trace_sq, hLneg, polyOfVec8_vecOf8 hfnegdeg, hfneg2]
  set gpos : ℝ[X] := fpos - C (2 / 8) with hgpos
  have hgposdeg : gpos.natDegree ≤ 7 := by
    rw [hgpos]
    refine le_trans (Polynomial.natDegree_sub_le fpos (C (2 / 8))) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hfposdeg
  have hvecpos_p1 : p1vec8 q (vecOf8 gpos) = 0 := by
    rw [p1vec8_vecOf8 q gpos hgposdeg, hgpos, aeval_sub_C8, Matrix.trace_sub,
      Matrix.trace_smul, hfpos1, Matrix.trace_one]
    norm_num
  have hLpos : Lcomb8 q (coeff7 (vecOf8 gpos)) = vecOf8 gpos := Lcomb8_coeff7 q hvecpos_p1
  have hQpos : qform (Gram8 q) (coeff7 (vecOf8 gpos)) = 3 / 2 := by
    rw [qform_Gram8_eq_trace_sq, hLpos, polyOfVec8_vecOf8 hgposdeg, hgpos, aeval_sub_C8,
      trace_sq_sub_scalar8, hfpos1, hfpos2]
    norm_num
  obtain ⟨rneg, hrneg⟩ := exists_rat_vec_pos 7 (continuous_qform (Gram8 q)).neg
    (x := coeff7 (vecOf8 fneg)) (by linarith : 0 < -qform (Gram8 q) (coeff7 (vecOf8 fneg)))
  obtain ⟨rpos, hrpos⟩ := exists_rat_vec_pos 7 (continuous_qform (Gram8 q))
    (x := coeff7 (vecOf8 gpos)) (by linarith : 0 < qform (Gram8 q) (coeff7 (vecOf8 gpos)))
  set e : Fin 7 → ℝ := fun i => (rneg i : ℝ) with he
  set f : Fin 7 → ℝ := fun i => (rpos i : ℝ) with hf
  have heP : ∀ i, PConstructible (e i) := fun i => rat_Pconstructible (rneg i)
  have hfP : ∀ i, PConstructible (f i) := fun i => rat_Pconstructible (rpos i)
  have heQ : qform (Gram8 q) e < 0 := by simpa using hrneg
  have hfQ : 0 < qform (Gram8 q) f := hrpos
  exact exists_isotropic_Pconstructible8 q hq heP hfP heQ hfQ

-- Theorem: from a cone point `P₀` and P-constructible `e, f ⟂ P₀` with `Q e < 0 < Q f`,
-- there is a P-constructible isotropic `x ⟂ P₀` independent of `P₀`.
theorem exists_isotropic_orth_Pconstructible8 (q : ℝ[X])
    (hq : ∀ k, PConstructible (q.coeff k))
    {P₀ e f : Fin 7 → ℝ} (hQ₀ : qform (Gram8 q) P₀ = 0)
    (he : ∀ i, PConstructible (e i)) (hf : ∀ i, PConstructible (f i))
    (hBe : bilin (Gram8 q) P₀ e = 0) (hBf : bilin (Gram8 q) P₀ f = 0)
    (heQ : qform (Gram8 q) e < 0) (hfQ : 0 < qform (Gram8 q) f) :
    ∃ x : Fin 7 → ℝ, (∀ i, PConstructible (x i)) ∧ qform (Gram8 q) x = 0 ∧
      bilin (Gram8 q) P₀ x = 0 ∧ ¬ ∃ k : ℝ, x = k • P₀ := by
  obtain ⟨t, htP, htpos, htroot⟩ := exists_pos_isotropic_param8 q hq he hf heQ hfQ
  refine ⟨e + t • f, fun i => PConstructible.add (he i) (PConstructible.mul htP (hf i)),
    htroot, ?_, ?_⟩
  · rw [bilin_add_right, bilin_smul_right, hBe, hBf, mul_zero, add_zero]
  · rintro ⟨k, hk⟩
    have heq : e = k • P₀ - t • f := eq_sub_iff_add_eq.mpr hk
    have hQe : qform (Gram8 q) e = t ^ 2 * qform (Gram8 q) f := by
      rw [heq, show k • P₀ - t • f = k • P₀ + (-t) • f by rw [sub_eq_add_neg, neg_smul],
        qform_smul_add (Gram8 q) (Gram8_symm q) k (-t) P₀ f, hQ₀, hBf]
      ring
    nlinarith [heQ, hfQ, sq_pos_of_pos htpos]

end

end Pconstructible
