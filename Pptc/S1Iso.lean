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
import Pptc.S1Roots

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### F5. There is no totally isotropic plane when `s = 1`

With a single conjugate pair `{z, z̄}`, the trace form `Q = qform (Gram q)` has no totally
isotropic plane: `Q x = Q y = B x y = 0` with `y ≠ 0` forces `x ∥ y`.

For `a b : ℝ` put `H = a F + b G`, where `F, G` are the degree-`≤ 6` polynomials of `x, y`.
The second power sum identity `companion7_trace_pow_aeval` and the root decomposition
`roots_eq_pair_add_real` give, over `ℂ`, that the sum of the squares of `H` over the roots
of `q` vanishes.  The conjugate pair contributes `2 Re (H(z)²)` and the other five roots are
real, so
`∑_r H(r)² + 2 Re (H(z)²) = 0`
for every `a, b`.  If `F(z), G(z)` are `ℝ`-dependent there is a nonzero `(a, b)` with
`H(z) = 0`, so the sum of squares vanishes termwise and `H`, of degree `≤ 6`, vanishes at the
seven distinct roots of `q`; hence `H = 0`.  Otherwise some `H` realises `H(z) = 1`, forcing the
sum of squares to be `-2 < 0`, a contradiction. -/

/-- `vecOf` is a left inverse of `polyOfVec`. -/
private lemma vecOf_polyOfVec (v : Fin 7 → ℝ) : vecOf (polyOfVec v) = v := by
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
private lemma eval_map_ofReal (f : ℝ[X]) (r : ℝ) :
    (f.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = ((f.eval r : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (f := algebraMap ℝ ℂ) (r := r) (p := f)

/-- Coercing the sum of the squared evaluations equals the complex multiset sum. -/
private lemma ofReal_sum_sq (R : Multiset ℝ) (H : ℝ[X]) :
    ((R.map (fun r => ((H.eval r) ^ 2 : ℂ))).sum)
      = (((R.map (fun r => (H.eval r) ^ 2)).sum : ℝ) : ℂ) := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih]
      push_cast
      ring

/-- The evaluation at `z` of `(C a * F + C b * G).map` is `a * F(z) + b * G(z)`. -/
private lemma eval_C_mul_add (F G : ℝ[X]) (z : ℂ) (a b : ℝ) :
    (((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval z)
      = (a : ℂ) * ((F.map (algebraMap ℝ ℂ)).eval z)
        + (b : ℂ) * ((G.map (algebraMap ℝ ℂ)).eval z) := by
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_C]
  simp

/-- The real sum of squares identity attached to the trace power sum. -/
private theorem sum_sq_add_pair_re {q H : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)))
    (htrace : Matrix.trace ((aeval (companion7 q) H) ^ 2) = 0) :
    (R.map (fun r => (H.eval r) ^ 2)).sum
      + 2 * ((((H.map (algebraMap ℝ ℂ)).eval z) ^ 2).re) = 0 := by
  have htr := companion7_trace_pow_aeval q H hmon hnat hsep 2
  rw [htrace, map_zero] at htr
  have hsum : ((q.map (algebraMap ℝ ℂ)).roots.map
      (fun w => ((H.map (algebraMap ℝ ℂ)).eval w) ^ 2)).sum = 0 := htr.symm
  rw [hroots] at hsum
  simp only [Multiset.map_cons, Multiset.sum_cons] at hsum
  set w : ℂ := (H.map (algebraMap ℝ ℂ)).eval z with hw
  set S : ℝ := (R.map (fun r => (H.eval r) ^ 2)).sum with hS
  have hzbar : ((H.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)) ^ 2
      = starRingEnd ℂ (w ^ 2) := by
    rw [hw, eval_map_conj, map_pow]
  have hRmap : ((R.map (algebraMap ℝ ℂ)).map
      (fun w => ((H.map (algebraMap ℝ ℂ)).eval w) ^ 2)).sum = ((S : ℝ) : ℂ) := by
    rw [Multiset.map_map]
    have hcongr : R.map ((fun w => ((H.map (algebraMap ℝ ℂ)).eval w) ^ 2)
        ∘ algebraMap ℝ ℂ) = R.map (fun r => ((H.eval r) ^ 2 : ℂ)) := by
      apply Multiset.map_congr rfl
      intro r _
      simp only [Function.comp_apply]
      rw [eval_map_ofReal]
    rw [hcongr]
    rw [ofReal_sum_sq, hS]
  rw [hzbar, hRmap] at hsum
  have hmain : (2 * (w ^ 2).re + S : ℝ) = 0 := by
    apply Complex.ofReal_eq_zero.mp
    push_cast
    rw [← add_assoc, Complex.add_conj] at hsum
    push_cast at hsum
    exact hsum
  rw [hS]
  linarith

/-- If `H` of degree `≤ 6` vanishes at all complex roots of a separable septic `q`, then
`H = 0`. -/
private lemma eq_zero_of_eval_zero_on_roots {q H : ℝ[X]} (_hmon : q.Monic)
    (hnat : q.natDegree = 7) (hsep : q.Separable) (hHdeg : H.natDegree ≤ 6)
    (h : ∀ w : ℂ, w ∈ (q.map (algebraMap ℝ ℂ)).roots →
      (H.map (algebraMap ℝ ℂ)).eval w = 0) : H = 0 := by
  have hnodup : (q.map (algebraMap ℝ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots (hsep.map)
  have hcardC : (q.map (algebraMap ℝ ℂ)).roots.card = 7 := by
    rw [show (q.map (algebraMap ℝ ℂ)).roots.card = (q.map (algebraMap ℝ ℂ)).natDegree from
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

-- Theorem: with a single conjugate pair the trace form on `{p1 = 0}` has no totally isotropic
-- plane: `Q x = Q y = B x y = 0` and `y ≠ 0` force `x` to be a scalar multiple of `y`.
theorem isotropic_plane_trivial {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z) :
    ∀ x y : Fin 6 → ℝ, qform (Gram q) x = 0 → qform (Gram q) y = 0 →
      bilin (Gram q) x y = 0 → y ≠ 0 → ∃ c : ℝ, x = c • y := by
  intro x y hQx hQy hBxy hyne
  set F : ℝ[X] := polyOfVec (Lcomb q x) with hF
  set G : ℝ[X] := polyOfVec (Lcomb q y) with hG
  have hFdeg : F.natDegree ≤ 6 := by rw [hF]; exact polyOfVec_natDegree_le _
  have hGdeg : G.natDegree ≤ 6 := by rw [hG]; exact polyOfVec_natDegree_le _
  have hvecF : vecOf F = Lcomb q x := by rw [hF]; exact vecOf_polyOfVec _
  have hvecG : vecOf G = Lcomb q y := by rw [hG]; exact vecOf_polyOfVec _
  obtain ⟨R, _hRnodup, _hRcard, hroots⟩ :=
    roots_eq_pair_add_real hmon hnat hsep hz hzim hone
  have hpoly : ∀ a b : ℝ,
      C a * F + C b * G = polyOfVec (Lcomb q (a • x + b • y)) := by
    intro a b
    rw [← polyOfVec_smul_add hFdeg hGdeg, hvecF, hvecG, Lcomb_smul_add]
  have hHdeg : ∀ a b : ℝ, (C a * F + C b * G).natDegree ≤ 6 := by
    intro a b
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_C_mul_le a F) hFdeg
    · exact le_trans (Polynomial.natDegree_C_mul_le b G) hGdeg
  have key : ∀ a b : ℝ,
      (R.map (fun r => ((C a * F + C b * G).eval r) ^ 2)).sum
        + 2 * (((((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval z) ^ 2).re) = 0 := by
    intro a b
    have hQab : qform (Gram q) (a • x + b • y) = 0 := by
      rw [qform_smul_add (Gram q) (Gram_symm q) a b x y, hQx, hQy, hBxy]
      ring
    have htrace : Matrix.trace ((aeval (companion7 q) (C a * F + C b * G)) ^ 2) = 0 := by
      calc Matrix.trace ((aeval (companion7 q) (C a * F + C b * G)) ^ 2)
          = Matrix.trace ((aeval (companion7 q)
              (polyOfVec (Lcomb q (a • x + b • y)))) ^ 2) := by rw [hpoly a b]
        _ = hermiteForm q (Lcomb q (a • x + b • y)) :=
              (hermiteForm_eq_trace_sq q _).symm
        _ = qform (Hmat q) (Lcomb q (a • x + b • y)) :=
              (qform_Hmat_eq_hermiteForm q _).symm
        _ = qform (Gram q) (a • x + b • y) := qform_Hmat_Lcomb q _
        _ = 0 := hQab
    exact sum_sq_add_pair_re hmon hnat hsep hroots htrace
  set u : ℂ := (F.map (algebraMap ℝ ℂ)).eval z with hu
  set v : ℂ := (G.map (algebraMap ℝ ℂ)).eval z with hv
  set D : ℝ := u.re * v.im - u.im * v.re with hD
  by_cases hD0 : D = 0
  · -- dependent case: a nonzero `(a, b)` with `a u + b v = 0`
    have hex : ∃ a b : ℝ, (a, b) ≠ (0, 0) ∧ (a : ℂ) * u + (b : ℂ) * v = 0 := by
      by_cases hu0 : u = 0
      · exact ⟨1, 0, by simp, by simp [hu0]⟩
      · refine ⟨u.re * v.re + u.im * v.im, -(u.re ^ 2 + u.im ^ 2), ?_, ?_⟩
        · intro h
          have hB : -(u.re ^ 2 + u.im ^ 2) = 0 := by
            have := congrArg Prod.snd h
            simpa using this
          have hsum0 : u.re ^ 2 + u.im ^ 2 = 0 := by linarith
          have hre : u.re = 0 := by nlinarith [sq_nonneg u.re, sq_nonneg u.im]
          have him : u.im = 0 := by nlinarith [sq_nonneg u.re, sq_nonneg u.im]
          exact hu0 (Complex.ext hre him)
        · have hd : u.re * v.im = u.im * v.re := by
            have := hD0; rw [hD] at this; linarith
          apply Complex.ext
          · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              Complex.zero_re]
            ring_nf
            linear_combination (u.im) * hd
          · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.zero_im]
            ring_nf
            linear_combination (-u.re) * hd
    obtain ⟨a, b, habne, huv0⟩ := hex
    have hHz : (((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval z) = 0 := by
      rw [eval_C_mul_add, ← hu, ← hv]
      exact huv0
    have hkey := key a b
    rw [hHz] at hkey
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), Complex.zero_re, mul_zero, add_zero]
      at hkey
    have hpoint : ∀ r ∈ R, (C a * F + C b * G).eval r = 0 := by
      have hnn : ∀ s ∈ R.map (fun r => ((C a * F + C b * G).eval r) ^ 2), (0 : ℝ) ≤ s := by
        intro s hs
        obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hs
        exact sq_nonneg _
      have hall := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hnn hkey
      intro r hr
      exact sq_eq_zero_iff.mp (hall _ (Multiset.mem_map_of_mem _ hr))
    have hrootzero : ∀ w : ℂ, w ∈ (q.map (algebraMap ℝ ℂ)).roots →
        ((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval w = 0 := by
      intro w hw
      rw [hroots] at hw
      rcases Multiset.mem_cons.mp hw with hwz | hw
      · subst hwz; exact hHz
      · rcases Multiset.mem_cons.mp hw with hwz | hw
        · subst hwz
          rw [eval_map_conj, hHz, map_zero]
        · obtain ⟨r, hr, hrw⟩ := Multiset.mem_map.mp hw
          rw [← hrw, eval_map_ofReal, hpoint r hr]
          simp
    have hH0 : C a * F + C b * G = 0 :=
      eq_zero_of_eval_zero_on_roots hmon hnat hsep (hHdeg a b) hrootzero
    have hL0 : Lcomb q (a • x + b • y) = 0 := by
      rw [hpoly a b] at hH0
      by_contra hne
      exact polyOfVec_ne_zero hne hH0
    have hab0 : a • x + b • y = 0 := Lcomb_injective q hL0
    have ha0 : a ≠ 0 := by
      intro ha
      rw [ha, zero_smul, zero_add] at hab0
      rcases smul_eq_zero.mp hab0 with hb | hy
      · exact habne (Prod.ext ha hb)
      · exact hyne hy
    refine ⟨-(b / a), ?_⟩
    have h1 : a • x = -(b • y) := eq_neg_of_add_eq_zero_left hab0
    calc x = a⁻¹ • (a • x) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
      _ = a⁻¹ • (-(b • y)) := by rw [h1]
      _ = (-(b / a)) • y := by
          rw [smul_neg, smul_smul, div_eq_mul_inv, neg_smul, mul_comm b a⁻¹]
  · -- independent case: some `(a, b)` realises `H(z) = 1`
    have hvnd : ((v.im / D : ℝ) : ℂ) * u + ((-u.im / D : ℝ) : ℂ) * v = 1 := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.one_re]
        field_simp [hD0]
        rw [hD]; ring
      · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.one_im]
        field_simp [hD0]; ring
    have hHz : (((C (v.im / D) * F + C (-u.im / D) * G).map
        (algebraMap ℝ ℂ)).eval z) = 1 := by
      rw [eval_C_mul_add, ← hu, ← hv]
      exact hvnd
    have hkey := key (v.im / D) (-u.im / D)
    rw [hHz] at hkey
    simp only [one_pow, Complex.one_re, mul_one] at hkey
    have hnn : 0 ≤ (R.map (fun r => ((C (v.im / D) * F + C (-u.im / D) * G).eval r) ^ 2)).sum :=
      Multiset.sum_nonneg (fun s hs => by
        obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hs
        exact sq_nonneg _)
    linarith

end

end Pconstructible
