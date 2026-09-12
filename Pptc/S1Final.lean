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

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
import Pptc.S1Sign
import Pptc.S1Sextic
import Mathlib.Topology.Order.IntermediateValue

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### Continuity of the stereographic cubic

The sign certificate `exists_sign_change` produces *some* real directions on which the cubic
has a prescribed sign; to obtain P-constructible (rational) directions we use density, which
needs continuity of the composite `d ↦ p3vec q (Lcomb q (stereo (Gram q) P₀ d))`.  Everything
in sight is polynomial, so continuity is proved coordinatewise. -/

-- Theorem: `qform` is continuous in its vector argument.
theorem continuous_qform {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun x : Fin n → ℝ => qform A x) := by
  rw [show (fun x : Fin n → ℝ => qform A x)
      = fun x => ∑ j, ∑ k, x j * A j k * x k by
    funext x; rw [qform_eq_sum]]
  fun_prop

-- Theorem: `bilin A y ·` is continuous in its second argument.
theorem continuous_bilin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    Continuous (fun x : Fin n → ℝ => bilin A y x) := by
  rw [show (fun x : Fin n → ℝ => bilin A y x)
      = fun x => ∑ j, ∑ k, y j * A j k * x k by
    funext x; rw [bilin_eq_sum]]
  fun_prop

-- Theorem: `stereo` is continuous in the direction.
theorem continuous_stereo (q : ℝ[X]) (P₀ : Fin 6 → ℝ) :
    Continuous (fun d : Fin 6 → ℝ => stereo (Gram q) P₀ d) := by
  apply continuous_pi
  intro i
  have hq : Continuous (fun d : Fin 6 → ℝ => qform (Gram q) d) := continuous_qform _
  have hb : Continuous (fun d : Fin 6 → ℝ => bilin (Gram q) P₀ d) := continuous_bilin _ _
  have hfun : (fun d : Fin 6 → ℝ => stereo (Gram q) P₀ d i)
      = fun d => qform (Gram q) d * P₀ i - (2 * bilin (Gram q) P₀ d) * d i := by
    funext d
    simp only [stereo, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact (hq.mul continuous_const).sub ((continuous_const.mul hb).mul (continuous_apply i))

-- Theorem: `Lcomb q` is continuous.
theorem continuous_Lcomb (q : ℝ[X]) :
    Continuous (fun v : Fin 6 → ℝ => Lcomb q v) := by
  apply continuous_pi
  intro i
  have hfun : (fun v : Fin 6 → ℝ => Lcomb q v i)
      = fun v => ∑ j : Fin 6, v j * bvec q j i := by
    funext v
    rw [Lcomb, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  fun_prop

-- Theorem: the stereographic cubic is continuous in the direction.
theorem continuous_Phi (q : ℝ[X]) (P₀ : Fin 6 → ℝ) :
    Continuous (fun d : Fin 6 → ℝ => p3vec q (Lcomb q (stereo (Gram q) P₀ d))) :=
  (continuous_p3vec q).comp ((continuous_Lcomb q).comp (continuous_stereo q P₀))

-- Theorem: `stereo` of P-constructible data has P-constructible coordinates.
theorem stereo_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {P₀ d : Fin 6 → ℝ} (hP₀ : ∀ i, PConstructible (P₀ i))
    (hd : ∀ i, PConstructible (d i)) :
    ∀ i, PConstructible (stereo (Gram q) P₀ d i) := by
  intro i
  have hG : ∀ i j, PConstructible (Gram q i j) := Gram_Pconstructible q hq
  have hqform : PConstructible (qform (Gram q) d) := bilin_Pconstructible hG hd hd
  have hbilin : PConstructible (bilin (Gram q) P₀ d) := bilin_Pconstructible hG hP₀ hd
  simp only [stereo, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact PConstructible.sub (PConstructible.mul hqform (hP₀ i))
    (PConstructible.mul (PConstructible.mul (by pconstructible) hbilin) (hd i))

/-! ### The one-conjugate-pair case

With all the pieces in place the proof follows `PLAN-degree7-s1.md` Steps 1-7: build a
P-constructible cone point `P₀`, certify a sign change of the stereographic cubic, round the
witnesses to rational directions, solve the resulting sextic, and feed the recovered
Tschirnhaus polynomial to the tail `root_Pconstructible_of_tschirnhaus`. -/

set_option maxHeartbeats 1000000 in
-- the assembly involves large `ring`/`nlinarith` goals in the non-degeneracy argument
-- Theorem: a real root `β` of a monic separable septic `q` with exactly one non-real
-- conjugate pair `{z, z̄}` is P-constructible.
theorem root_Pconstructible_of_one_conjugate_pair {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 7) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β := by
  classical
  -- Step 1: P-constructible directions with `Q e < 0 < Q f`.
  obtain ⟨fneg, hfnegdeg, hfneg1, hfneg2⟩ := exists_neg_trace q hmon hnat hsep hz hzim
  obtain ⟨fpos, hfposdeg, hfpos1, hfpos2⟩ := exists_pos_trace q hmon hnat hsep hz hzim
  have hvecneg_p1 : p1vec q (vecOf fneg) = 0 := by
    rw [p1vec_vecOf q fneg hfnegdeg, hfneg1]
  have hLneg : Lcomb q (coeff6 (vecOf fneg)) = vecOf fneg := Lcomb_coeff6 q hvecneg_p1
  have hQneg : qform (Gram q) (coeff6 (vecOf fneg)) = -2 := by
    rw [← qform_Hmat_Lcomb q (coeff6 (vecOf fneg)), hLneg, qform_Hmat_eq_hermiteForm,
      hermiteForm_eq_trace_sq, polyOfVec_vecOf hfnegdeg, hfneg2]
  set gpos : ℝ[X] := fpos - C (2 / 7) with hgpos
  have hgposdeg : gpos.natDegree ≤ 6 := by
    rw [hgpos]
    refine le_trans (Polynomial.natDegree_sub_le fpos (C (2 / 7))) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hfposdeg
  have hvecpos_p1 : p1vec q (vecOf gpos) = 0 := by
    rw [p1vec_vecOf q gpos hgposdeg, hgpos, aeval_sub_C, Matrix.trace_sub,
      Matrix.trace_smul, hfpos1, Matrix.trace_one]
    norm_num
  have hLpos : Lcomb q (coeff6 (vecOf gpos)) = vecOf gpos := Lcomb_coeff6 q hvecpos_p1
  have hQpos : qform (Gram q) (coeff6 (vecOf gpos)) = 10 / 7 := by
    rw [← qform_Hmat_Lcomb q (coeff6 (vecOf gpos)), hLpos, qform_Hmat_eq_hermiteForm,
      hermiteForm_eq_trace_sq, polyOfVec_vecOf hgposdeg, hgpos, aeval_sub_C,
      trace_sq_sub_scalar, hfpos1, hfpos2]
    norm_num
  obtain ⟨rneg, hrneg⟩ := exists_rat_vec_pos 6 (continuous_qform (Gram q)).neg
    (x := coeff6 (vecOf fneg)) (by linarith : 0 < -qform (Gram q) (coeff6 (vecOf fneg)))
  obtain ⟨rpos, hrpos⟩ := exists_rat_vec_pos 6 (continuous_qform (Gram q))
    (x := coeff6 (vecOf gpos)) (by linarith : 0 < qform (Gram q) (coeff6 (vecOf gpos)))
  set e : Fin 6 → ℝ := fun i => (rneg i : ℝ) with he
  set f : Fin 6 → ℝ := fun i => (rpos i : ℝ) with hf
  have heP : ∀ i, PConstructible (e i) := fun i => rat_Pconstructible (rneg i)
  have hfP : ∀ i, PConstructible (f i) := fun i => rat_Pconstructible (rpos i)
  have heQ : qform (Gram q) e < 0 := by simpa using hrneg
  have hfQ : 0 < qform (Gram q) f := hrpos
  -- Step 2: a P-constructible point `P₀` on the cone.
  obtain ⟨P₀, hP₀P, hQ₀, hP₀ne⟩ := exists_isotropic_Pconstructible q hq heP hfP heQ hfQ
  -- Step 3: a sign change of the stereographic cubic on the cone.
  obtain ⟨dplus, dminus, hdplus, hdminus⟩ :=
    exists_sign_change hmon hnat hsep hz hzim hone hQ₀ hP₀ne
  -- Step 4: rationalise the two witnesses.
  obtain ⟨rdplus, hrdplus⟩ := exists_rat_vec_pos 6 (continuous_Phi q P₀) (x := dplus) hdplus
  obtain ⟨rdminus, hrdminus⟩ := exists_rat_vec_pos 6 (continuous_Phi q P₀).neg
    (x := dminus) (by linarith : 0 < -p3vec q (Lcomb q (stereo (Gram q) P₀ dminus)))
  set dp : Fin 6 → ℝ := fun i => (rdplus i : ℝ) with hdp
  set dm : Fin 6 → ℝ := fun i => (rdminus i : ℝ) with hdm
  have hdpP : ∀ i, PConstructible (dp i) := fun i => rat_Pconstructible (rdplus i)
  have hdmP : ∀ i, PConstructible (dm i) := fun i => rat_Pconstructible (rdminus i)
  have hPhidp : 0 < p3vec q (Lcomb q (stereo (Gram q) P₀ dp)) := hrdplus
  have hPhidm : p3vec q (Lcomb q (stereo (Gram q) P₀ dm)) < 0 := by simpa using hrdminus
  -- Step 5: the sextic along the line `dp + m • (dm - dp)`.
  set δ : Fin 6 → ℝ := dm - dp with hδ
  have hδP : ∀ i, PConstructible (δ i) := by
    intro i; rw [hδ]; exact PConstructible.sub (hdmP i) (hdpP i)
  obtain ⟨Ψ, hΨc, hΨdeg, hΨeval⟩ := exists_sextic_along_line q hq hP₀P hdpP hδP
  have hΨ0 : 0 < Ψ.eval 0 := by
    rw [hΨeval 0]
    simpa using hPhidp
  have hdm_eq : dp + (1 : ℝ) • δ = dm := by
    rw [hδ]; simp only [one_smul]; abel
  have hΨ1 : Ψ.eval 1 < 0 := by
    rw [hΨeval 1, hdm_eq]
    exact hPhidm
  have hΨne : Ψ ≠ 0 := by
    intro h0; rw [h0, Polynomial.eval_zero] at hΨ0; exact lt_irrefl _ hΨ0
  have hcontOn : ContinuousOn (fun m : ℝ => Ψ.eval m) (Set.Icc (0 : ℝ) 1) :=
    (Polynomial.continuous Ψ).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc (Ψ.eval 1) (Ψ.eval 0) :=
    ⟨le_of_lt hΨ1, le_of_lt hΨ0⟩
  obtain ⟨mstar, hmstar_mem, hmstar_root⟩ :=
    (intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcontOn) hmem
  have hmstar_ne0 : mstar ≠ 0 := by
    intro h0; rw [h0] at hmstar_root; linarith [hΨ0]
  have hmstar_ne1 : mstar ≠ 1 := by
    intro h1; rw [h1] at hmstar_root; linarith [hΨ1]
  have hmstar_pos : 0 < mstar := lt_of_le_of_ne hmstar_mem.1 hmstar_ne0.symm
  have hmstar_lt1 : mstar < 1 := lt_of_le_of_ne hmstar_mem.2 hmstar_ne1
  have hmstarP : PConstructible mstar :=
    root_Pconstructible_le_six_coeffs hΨne hΨdeg hΨc hmstar_root
  set xstar : Fin 6 → ℝ := dp + mstar • δ with hxstar
  have hxstarP : ∀ i, PConstructible (xstar i) := by
    intro i
    simp only [hxstar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.add (hdpP i) (PConstructible.mul hmstarP (hδP i))
  set vstar : Fin 6 → ℝ := stereo (Gram q) P₀ xstar with hvstar
  have hvstarP : ∀ i, PConstructible (vstar i) := stereo_Pconstructible q hq hP₀P hxstarP
  have hQvstar : qform (Gram q) vstar = 0 := qform_stereo_eq_zero (Gram_symm q) hQ₀ xstar
  have hphistar0 : p3vec q (Lcomb q vstar) = 0 := by
    have h := hΨeval mstar
    rw [← hxstar, ← hvstar] at h
    exact h.symm.trans hmstar_root
  -- Step 6: non-degeneracy of `vstar`.
  have hnotpar : ¬ ∃ c : ℝ, xstar = c • P₀ := by
    rintro ⟨c, hc⟩
    set Phiδ : ℝ := p3vec q (Lcomb q (stereo (Gram q) P₀ δ)) with hPhiδ
    have hxstar_eq : dp + mstar • δ = c • P₀ := by rw [← hc, hxstar]
    have hdp_eq : dp = c • P₀ - mstar • δ := by rw [← hxstar_eq, add_sub_cancel_right]
    have hPsi_eq : ∀ m : ℝ, Ψ.eval m = (m - mstar) ^ 6 * Phiδ := by
      intro m
      rw [hΨeval m]
      have hx : dp + m • δ = c • P₀ + (m - mstar) • δ := by rw [hdp_eq]; module
      rw [hx, stereo_smul_add_smul (A := Gram q) (Gram_symm q) hQ₀ c (m - mstar) δ,
        Lcomb_smul, p3vec_smul, ← hPhiδ]
      ring
    have h0 : Ψ.eval 0 = mstar ^ 6 * Phiδ := by rw [hPsi_eq 0]; ring
    have h1 : Ψ.eval 1 = (1 - mstar) ^ 6 * Phiδ := hPsi_eq 1
    have hA : 0 < mstar ^ 6 := pow_pos hmstar_pos 6
    have hB : 0 < (1 - mstar) ^ 6 := pow_pos (by linarith) 6
    nlinarith [hΨ0, hΨ1, h0, h1, hA, hB]
  have hvstar_ne : vstar ≠ 0 := by
    intro hv
    have hsub : qform (Gram q) xstar • P₀
        - (2 * bilin (Gram q) P₀ xstar) • xstar = 0 := by
      rw [← hv, hvstar]; rfl
    by_cases hb : bilin (Gram q) P₀ xstar = 0
    · have hQx : qform (Gram q) xstar = 0 := by
        rw [hb] at hsub
        simp only [mul_zero, zero_smul, sub_zero] at hsub
        exact (smul_eq_zero.mp hsub).resolve_right hP₀ne
      have hb' : bilin (Gram q) xstar P₀ = 0 := by
        rw [← bilin_comm (Gram_symm q) P₀ xstar]; exact hb
      exact hnotpar
        (isotropic_plane_trivial hmon hnat hsep hz hzim hone xstar P₀ hQx hQ₀ hb' hP₀ne)
    · by_cases hQx : qform (Gram q) xstar = 0
      · have hx0 : xstar = 0 := by
          rw [hQx, zero_smul, zero_sub] at hsub
          rw [neg_eq_zero] at hsub
          exact (smul_eq_zero.mp hsub).resolve_left (mul_ne_zero two_ne_zero hb)
        exact hnotpar ⟨0, by rw [hx0, zero_smul]⟩
      · have hx : xstar
            = ((2 * bilin (Gram q) P₀ xstar)⁻¹ * qform (Gram q) xstar) • P₀ := by
          have hrel : qform (Gram q) xstar • P₀
              = (2 * bilin (Gram q) P₀ xstar) • xstar := sub_eq_zero.mp hsub
          have h2b : (2 * bilin (Gram q) P₀ xstar) ≠ 0 := mul_ne_zero two_ne_zero hb
          have h := congrArg (fun v : Fin 6 → ℝ =>
            ((2 * bilin (Gram q) P₀ xstar))⁻¹ • v) hrel
          rw [smul_smul, smul_smul, inv_mul_cancel₀ h2b, one_smul] at h
          exact h.symm
        exact hnotpar ⟨_, hx⟩
  -- Step 7: the Tschirnhaus polynomial and the tail.
  set φ : ℝ[X] := polyOfVec (Lcomb q vstar) with hφ
  have hLne : Lcomb q vstar ≠ 0 := fun h => hvstar_ne (Lcomb_injective q h)
  refine root_Pconstructible_of_tschirnhaus (φ := φ) hmon hnat hsep hq ?_ ?_ ?_ ?_ ?_ ?_ hβ
  · exact polyOfVec_coeff_Pconstructible _ (Lcomb_Pconstructible q hq hvstarP)
  · exact polyOfVec_natDegree_le _
  · rw [hφ]; exact polyOfVec_ne_zero hLne
  · rw [hφ, ← p1vec_eq_trace q (Lcomb q vstar)]; exact p1vec_Lcomb q vstar
  · rw [hφ, ← hermiteForm_eq_trace_sq q (Lcomb q vstar),
      ← qform_Hmat_eq_hermiteForm, qform_Hmat_Lcomb q vstar]
    exact hQvstar
  · rw [hφ]
    change p3vec q (Lcomb q vstar) = 0
    exact hphistar0

/-! ### The literal issue statement

Finally, drop the separability hypothesis by normalising to a monic septic and splitting on
whether a second conjugate pair exists (`root_Pconstructible_of_two_conjugate_pairs`), with
the non-separable branch handled by `root_Pconstructible_of_nonSeparable`. -/

-- Theorem: a real root `β` of any degree-7 polynomial `q` with P-constructible coefficients
-- and a non-real root `z` is P-constructible (the literal statement of issue #6).
theorem root_Pconstructible_of_nonreal_root {q : ℝ[X]} (hnat : q.natDegree = 7)
    (hq : ∀ k, PConstructible (q.coeff k)) {z : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    {β : ℝ} (hβ : q.eval β = 0) : PConstructible β := by
  classical
  have hne : q ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  set q₀ : ℝ[X] := C q.leadingCoeff⁻¹ * q with hq₀
  have hmon : q₀.Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hnat₀ : q₀.natDegree = 7 := by
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
  · by_cases hsecond : ∃ w : ℂ, (q₀.map (algebraMap ℝ ℂ)).eval w = 0 ∧ w.im ≠ 0 ∧
        w ≠ z ∧ w ≠ starRingEnd ℂ z
    · obtain ⟨w, hw, hwim, hwz, hwz'⟩ := hsecond
      have hzw' : z ≠ starRingEnd ℂ w := by
        intro h
        exact hwz' (by
          have := congrArg (starRingEnd ℂ) h
          simpa using this.symm)
      exact root_Pconstructible_of_two_conjugate_pairs_monic hmon hnat₀ hq₀c hz₀ hzim
        hw hwim hwz.symm hzw' hβ₀
    · have hone : ∀ w : ℂ, (q₀.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
          w = z ∨ w = starRingEnd ℂ z := by
        intro w hw hwim
        by_contra hc
        rcases not_or.mp hc with ⟨hwz, hwz'⟩
        exact hsecond ⟨w, hw, hwim, hwz, hwz'⟩
      exact root_Pconstructible_of_one_conjugate_pair hmon hnat₀ hsep hq₀c hz₀ hzim hone hβ₀
  · exact root_Pconstructible_of_nonSeparable hmon hq₀c (le_of_eq hnat₀) hsep hβ₀

end

end Pconstructible
