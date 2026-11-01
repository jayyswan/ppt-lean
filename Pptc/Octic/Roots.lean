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

import Pptc.Octic.TraceForm

/-! # Pptc.Octic.Roots

Lagrange interpolation and the root decomposition for octics, the degree-8 analogue of the
corresponding block of `Pptc.DegreeSeven` (`Pptc/Octic/PLAN.md` §2.4).

For a monic separable real octic `q` with a non-real root `z`, prescribing a complex value
`c` at `z`, its conjugate at `z̄` and `0` at every other root is done by dividing out the
conjugate quadratic `conjQuad z` (degree two) and multiplying by a linear factor: the
quotient `q /ₘ conjQuad z` has degree `6`, so the interpolating polynomial has degree `≤ 7`
(and not `≤ 6` as in the septic case, where the same construction lands in degree `≤ 6`).

The trace consequences follow by summing a function over the roots of `q` over `ℂ`: a real
polynomial that takes the value `c` at `z` and vanishes at all other roots has companion
trace `c + c̄`, hence trace `2 Re c` and trace of the square `2 Re c²`.

Finally, if the only non-real roots of `q` are `z` and `z̄`, the eight complex roots
decompose as the conjugate pair plus the images of six distinct real roots, giving
`roots = z ::ₘ z̄ ::ₘ R.map (algebraMap ℝ ℂ)` with `R.Nodup` and `R.card = 6`.
-/

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### The trace of `aeval` as a sum over the roots -/

-- Theorem: the trace of `aeval (companionN q) F`, mapped to `ℂ`, is the sum of the values of
-- `F` at the complex roots of `q`.
theorem companionN_trace_aeval8 (q F : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companionN (n := 8) q) F))
      = ((q.map (algebraMap ℝ ℂ)).roots.map
          (fun z => (F.map (algebraMap ℝ ℂ)).eval z)).sum := by
  have h := companionN_trace_pow_aeval8 q F hmon hnat hsep 1
  simpa using h

/-! ### The Lagrange direction

For a monic separable real octic with a non-real root `z`, any complex value `c` can be
prescribed at `z`, with conjugate value forced at `z̄` and vanishing at every other root.
The construction factors `q = (conjQuad z) * G` over `ℝ`; over `ℂ` this is
`qC = (X - z)(X - z̄) * GC`, so `GC` is supported on the remaining roots.  Multiplying
`G` by a linear real polynomial `h` chosen so that `G(z) * h(z) = c` does the rest. -/

-- Theorem: for a monic separable real octic with a non-real complex root `z`, every complex
-- value is attained at `z` by a real polynomial of degree at most seven that vanishes at all
-- other complex roots and takes the conjugate value at `z̄`.
theorem exists_poly_value_at_root8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (c : ℂ) :
    ∃ f : ℝ[X], f.natDegree ≤ 7 ∧
      (f.map (algebraMap ℝ ℂ)).eval z = c ∧
      (f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = starRingEnd ℂ c ∧
      ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
        x ≠ starRingEnd ℂ z →
        (f.map (algebraMap ℝ ℂ)).eval x = 0 := by
  classical
  have hqne : q ≠ 0 := hmon.ne_zero
  have hpmon : (conjQuad z).Monic := conjQuad_monic z
  have hpdeg : (conjQuad z).natDegree = 2 := conjQuad_natDegree z
  have hpvd : conjQuad z ∣ q := conjQuad_dvd_of_root hz hzim
  set G : ℝ[X] := q /ₘ conjQuad z with hG
  have hdiv : conjQuad z * G = q := by
    have hmod0 : q %ₘ conjQuad z = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hpmon).mpr hpvd
    have h := Polynomial.modByMonic_add_div q (conjQuad z)
    rw [hmod0, zero_add] at h
    rw [hG]
    exact h
  have hGne : G ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdiv
    exact hqne hdiv.symm
  have hGdeg : G.natDegree = 6 := by
    have h := Polynomial.natDegree_mul hpmon.ne_zero hGne
    rw [hdiv, hpdeg, hnat] at h
    omega
  have h2im : (2 * z.im : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hzim
  have h2imC : (algebraMap ℝ ℂ (2 * z.im)) ≠ 0 := fun h =>
    h2im ((algebraMap ℝ ℂ).injective (by simpa using h))
  have h2im_ne : (algebraMap ℝ ℂ (2 * z.im)) * Complex.I ≠ 0 :=
    mul_ne_zero h2imC Complex.I_ne_zero
  have hmap : q.map (algebraMap ℝ ℂ)
      = ((conjQuad z).map (algebraMap ℝ ℂ)) * (G.map (algebraMap ℝ ℂ)) := by
    rw [← hdiv, Polynomial.map_mul]
  have hpCder : (((conjQuad z).map (algebraMap ℝ ℂ)).derivative).eval z
      = (algebraMap ℝ ℂ (2 * z.im)) * Complex.I := by
    rw [conjQuad_map_eq_prod]
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C, Polynomial.derivative_X_sub_C]
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, one_mul, mul_one, sub_self, add_zero,
      Complex.sub_conj]
    rfl
  have hderiv : (q.map (algebraMap ℝ ℂ)).derivative.eval z
      = (((conjQuad z).map (algebraMap ℝ ℂ)).derivative.eval z)
          * (G.map (algebraMap ℝ ℂ)).eval z
        + (((conjQuad z).map (algebraMap ℝ ℂ)).eval z)
          * (G.map (algebraMap ℝ ℂ)).derivative.eval z := by
    rw [hmap, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul]
  have hGCeq : (G.map (algebraMap ℝ ℂ)).eval z
      = (q.map (algebraMap ℝ ℂ)).derivative.eval z
          / ((algebraMap ℝ ℂ (2 * z.im)) * Complex.I) := by
    have h := hderiv
    rw [conjQuad_eval_map z, zero_mul, add_zero, hpCder] at h
    rw [h, eq_div_iff h2im_ne]
    ring
  have hqCsep : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  have hqCder_ne : (q.map (algebraMap ℝ ℂ)).derivative.eval z ≠ 0 := by
    have h := hqCsep.aeval_derivative_ne_zero (x := z) (by
      simp only [Polynomial.coe_aeval_eq_eval]
      exact hz)
    simpa only [Polynomial.coe_aeval_eq_eval] using h
  obtain ⟨h, hhdeg, hhval⟩ := exists_linear_eval z
    (c * ((algebraMap ℝ ℂ (2 * z.im)) * Complex.I)
      / (q.map (algebraMap ℝ ℂ)).derivative.eval z) hzim
  have hfz : ((G * h).map (algebraMap ℝ ℂ)).eval z = c := by
    rw [Polynomial.map_mul, Polynomial.eval_mul, hGCeq, hhval]
    field_simp [h2im_ne, hqCder_ne]
  have hfbar : ((G * h).map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)
      = starRingEnd ℂ c := by
    rw [eval_map_conj, hfz]
  have hfother : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((G * h).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    have hpCx : ((conjQuad z).map (algebraMap ℝ ℂ)).eval x ≠ 0 := by
      rw [conjQuad_map_eq_prod]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact mul_ne_zero (sub_ne_zero.mpr hxz) (sub_ne_zero.mpr hxz')
    have hxprod : (((conjQuad z).map (algebraMap ℝ ℂ)).eval x)
        * ((G.map (algebraMap ℝ ℂ)).eval x) = 0 := by
      rw [← Polynomial.eval_mul, ← Polynomial.map_mul, hdiv]
      exact hx
    have hGCx : (G.map (algebraMap ℝ ℂ)).eval x = 0 :=
      (mul_eq_zero.mp hxprod).resolve_left hpCx
    rw [Polynomial.map_mul, Polynomial.eval_mul, hGCx, zero_mul]
  have hfdeg : (G * h).natDegree ≤ 7 := by
    have := Polynomial.natDegree_mul_le_of_le (p := G) (q := h) (m := 6) (n := 1)
      (by omega) hhdeg
    simpa using this
  exact ⟨G * h, hfdeg, hfz, hfbar, hfother⟩

/-! ### Trace consequences -/

-- Theorem: a real polynomial taking the value `c` at a non-real root `z` and vanishing at
-- every other root has companion-matrix trace `c + c̄`.
theorem algebraMap_trace_eq_of_value8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (F : ℝ[X]) (c : ℂ)
    (hFz : (F.map (algebraMap ℝ ℂ)).eval z = c)
    (hFother : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → (F.map (algebraMap ℝ ℂ)).eval x = 0) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companionN (n := 8) q) F))
      = c + starRingEnd ℂ c := by
  have hqCne : (q.map (algebraMap ℝ ℂ)) ≠ 0 := (hmon.map (algebraMap ℝ ℂ)).ne_zero
  have hqCsep : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  have hnodup : (q.map (algebraMap ℝ ℂ)).roots.Nodup := Polynomial.nodup_roots hqCsep
  have hzmem : z ∈ (q.map (algebraMap ℝ ℂ)).roots :=
    (Polynomial.mem_roots hqCne).mpr hz
  have hzbarmem : starRingEnd ℂ z ∈ (q.map (algebraMap ℝ ℂ)).roots :=
    (Polynomial.mem_roots hqCne).mpr (by
      change Polynomial.eval (starRingEnd ℂ z) (Polynomial.map (algebraMap ℝ ℂ) q) = 0
      rw [eval_map_conj q z, hz, map_zero])
  have hzzber : z ≠ starRingEnd ℂ z := by
    intro h
    have him : z.im = -z.im := by
      have := congrArg Complex.im h
      rwa [Complex.conj_im] at this
    exact hzim (by linarith)
  rw [companionN_trace_aeval8 q F hmon hnat hsep]
  have hsum := multiset_sum_eq_two_of_vanish hnodup hzmem hzbarmem hzzber
    (g := fun x => (F.map (algebraMap ℝ ℂ)).eval x)
    (fun x hx hxz hxz' => hFother x ((Polynomial.mem_roots hqCne).mp hx) hxz hxz')
  rw [hsum]
  change (F.map (algebraMap ℝ ℂ)).eval z
      + (F.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = c + starRingEnd ℂ c
  rw [hFz, eval_map_conj F z, hFz]

-- Theorem: a real polynomial whose complex evaluation vanishes at every root of `qC` has
-- companion-matrix trace zero.
theorem trace_aeval_eq_zero_of_vanishes8 (q : ℝ[X]) (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (F : ℝ[X])
    (hF : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 →
      (F.map (algebraMap ℝ ℂ)).eval x = 0) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companionN (n := 8) q) F)) = 0 := by
  have hqCne : (q.map (algebraMap ℝ ℂ)) ≠ 0 := (hmon.map (algebraMap ℝ ℂ)).ne_zero
  rw [companionN_trace_aeval8 q F hmon hnat hsep]
  refine Multiset.sum_eq_zero fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  exact hF x ((Polynomial.mem_roots hqCne).mp hx)

-- Theorem: if a real polynomial `f` takes the value `c` at a non-real root `z` and vanishes
-- at every other root, then `trace N_f = 2 Re c` and `trace N_f² = 2 Re c²`.
theorem trace_eq_of_value8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) {f : ℝ[X]} {c : ℂ}
    (hfz : (f.map (algebraMap ℝ ℂ)).eval z = c)
    (hfother : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → (f.map (algebraMap ℝ ℂ)).eval x = 0) :
    Matrix.trace (aeval (companionN (n := 8) q) f) = 2 * c.re ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = 2 * (c ^ 2).re := by
  have hfsq : ((f ^ 2).map (algebraMap ℝ ℂ)).eval z = c ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfz]
  have hfothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((f ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfother x hx hxz hxz']
    simp
  have ht := algebraMap_trace_eq_of_value8 q hmon hnat hsep hz hzim f c hfz hfother
  have htsq :=
    algebraMap_trace_eq_of_value8 q hmon hnat hsep hz hzim (f ^ 2) (c ^ 2) hfsq hfothersq
  refine ⟨?_, ?_⟩
  · apply (algebraMap ℝ ℂ).injective
    rw [ht, Complex.add_conj]
    rfl
  · apply (algebraMap ℝ ℂ).injective
    have h2 : (aeval (companionN (n := 8) q) f) ^ 2
        = aeval (companionN (n := 8) q) (f ^ 2) :=
      (map_pow (aeval (companionN (n := 8) q)) f 2).symm
    rw [h2, htsq, Complex.add_conj]
    rfl

-- Theorem: for any complex value `c`, some real polynomial of degree at most seven realises
-- `trace N_f = 2 Re c` and `trace N_f² = 2 Re c²`.
theorem exists_value_trace8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (c : ℂ) :
    ∃ f : ℝ[X], f.natDegree ≤ 7 ∧
      Matrix.trace (aeval (companionN (n := 8) q) f) = 2 * c.re ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = 2 * (c ^ 2).re := by
  obtain ⟨f, hfdeg, hfz, _hfbar, hfother⟩ :=
    exists_poly_value_at_root8 q hmon hnat hsep hz hzim c
  exact ⟨f, hfdeg, trace_eq_of_value8 q hmon hnat hsep hz hzim hfz hfother⟩

-- Theorem: for a non-real root `z`, some real polynomial of degree at most seven has trace
-- `0` and trace of square `-2` in the companion matrix.
theorem exists_neg_trace8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) :
    ∃ f : ℝ[X], f.natDegree ≤ 7 ∧ Matrix.trace (aeval (companionN (n := 8) q) f) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = -2 := by
  obtain ⟨f, hfdeg, htr, htrsq⟩ :=
    exists_value_trace8 q hmon hnat hsep hz hzim Complex.I
  exact ⟨f, hfdeg, by simpa [Complex.I_re] using htr, by simpa [Complex.I_sq] using htrsq⟩

-- Theorem: for a non-real root `z`, some real polynomial of degree at most seven has trace
-- `2` and trace of square `2` in the companion matrix.
theorem exists_pos_trace8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) :
    ∃ f : ℝ[X], f.natDegree ≤ 7 ∧ Matrix.trace (aeval (companionN (n := 8) q) f) = 2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = 2 := by
  obtain ⟨f, hfdeg, htr, htrsq⟩ := exists_value_trace8 q hmon hnat hsep hz hzim 1
  exact ⟨f, hfdeg, by simpa using htr, by simpa using htrsq⟩

/-! ### Two conjugate pairs

Two non-real roots `z`, `w` from distinct conjugate pairs give polynomials supported on
disjoint sets of roots, so their traces and cross trace can be computed independently. -/

-- Theorem: for any complex value `c`, two non-real roots from distinct conjugate pairs yield
-- real polynomials of degree at most seven realising `trace = 2 Re c`, `trace sq = 2 Re c²`
-- and vanishing cross trace.
theorem exists_value_pair8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) (c : ℂ) :
    ∃ f g : ℝ[X], f.natDegree ≤ 7 ∧ g.natDegree ≤ 7 ∧
      Matrix.trace (aeval (companionN (n := 8) q) f) = 2 * c.re ∧
      Matrix.trace (aeval (companionN (n := 8) q) g) = 2 * c.re ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = 2 * (c ^ 2).re ∧
      Matrix.trace ((aeval (companionN (n := 8) q) g) ^ 2) = 2 * (c ^ 2).re ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f)
        * (aeval (companionN (n := 8) q) g)) = 0 := by
  obtain ⟨f, hfdeg, hfz, _hfbar, hfother⟩ :=
    exists_poly_value_at_root8 q hmon hnat hsep hz hzim c
  obtain ⟨g, hgdeg, hgw, _hgbar, hgother⟩ :=
    exists_poly_value_at_root8 q hmon hnat hsep hw hwim c
  have hzbar : (q.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = 0 := by
    rw [eval_map_conj, hz, map_zero]
  have hz'w : starRingEnd ℂ z ≠ w := by
    intro h
    apply hzw'
    have := congrArg (starRingEnd ℂ) h
    rw [starRingEnd_apply, starRingEnd_apply, star_star] at this
    exact this
  have hz'w' : starRingEnd ℂ z ≠ starRingEnd ℂ w := by
    intro h
    exact hzw ((starRingEnd ℂ).injective h)
  have hcross := trace_aeval_eq_zero_of_vanishes8 q hmon hnat hsep (f * g) (by
    intro x hx
    rw [Polynomial.map_mul, Polynomial.eval_mul]
    by_cases hxz : x = z
    · rw [hxz]
      have hgz : (g.map (algebraMap ℝ ℂ)).eval z = 0 := hgother z hz hzw hzw'
      rw [hgz, mul_zero]
    · by_cases hxz' : x = starRingEnd ℂ z
      · rw [hxz']
        have hgz : (g.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = 0 :=
          hgother _ hzbar hz'w hz'w'
        rw [hgz, mul_zero]
      · rw [hfother x hx hxz hxz', zero_mul])
  have htrace : Matrix.trace ((aeval (companionN (n := 8) q) f)
      * (aeval (companionN (n := 8) q) g)) = 0 := by
    have h1 : (aeval (companionN (n := 8) q) f) * (aeval (companionN (n := 8) q) g)
        = aeval (companionN (n := 8) q) (f * g) := by rw [map_mul]
    rw [h1]
    exact (algebraMap ℝ ℂ).injective (by simpa using hcross)
  obtain ⟨htf, htf_sq⟩ := trace_eq_of_value8 q hmon hnat hsep hz hzim hfz hfother
  obtain ⟨htg, htg_sq⟩ := trace_eq_of_value8 q hmon hnat hsep hw hwim hgw hgother
  exact ⟨f, g, hfdeg, hgdeg, htf, htg, htf_sq, htg_sq, htrace⟩

-- Theorem: two non-real roots from distinct conjugate pairs yield real polynomials of
-- degree at most seven with vanishing traces, square traces `-2`, and vanishing cross trace.
theorem exists_neg_pair8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ f g : ℝ[X], f.natDegree ≤ 7 ∧ g.natDegree ≤ 7 ∧
      Matrix.trace (aeval (companionN (n := 8) q) f) = 0 ∧
      Matrix.trace (aeval (companionN (n := 8) q) g) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = -2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) g) ^ 2) = -2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f)
        * (aeval (companionN (n := 8) q) g)) = 0 := by
  obtain ⟨f, g, hfdeg, hgdeg, htf, htg, htfsq, htgsq, hcross⟩ :=
    exists_value_pair8 q hmon hnat hsep hz hzim hw hwim hzw hzw' Complex.I
  exact ⟨f, g, hfdeg, hgdeg, by simpa [Complex.I_re] using htf,
    by simpa [Complex.I_re] using htg, by simpa [Complex.I_sq] using htfsq,
    by simpa [Complex.I_sq] using htgsq, hcross⟩

-- Theorem: two non-real roots from distinct conjugate pairs yield real polynomials of
-- degree at most seven with traces `2`, square traces `2`, and vanishing cross trace.
theorem exists_pos_pair8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ f g : ℝ[X], f.natDegree ≤ 7 ∧ g.natDegree ≤ 7 ∧
      Matrix.trace (aeval (companionN (n := 8) q) f) = 2 ∧
      Matrix.trace (aeval (companionN (n := 8) q) g) = 2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = 2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) g) ^ 2) = 2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f)
        * (aeval (companionN (n := 8) q) g)) = 0 := by
  obtain ⟨f, g, hfdeg, hgdeg, htf, htg, htfsq, htgsq, hcross⟩ :=
    exists_value_pair8 q hmon hnat hsep hz hzim hw hwim hzw hzw' 1
  exact ⟨f, g, hfdeg, hgdeg, by simpa using htf, by simpa using htg,
    by simpa using htfsq, by simpa using htgsq, hcross⟩

/-! ### The root decomposition of an octic with one conjugate pair

For a monic separable real octic `q` whose only non-real roots are `z` and `z̄`, the
complex roots split as `z`, `z̄`, and the images of six distinct real roots.  The real
roots are collected as a `Multiset ℝ` by filtering the complex roots on `im = 0` and
reading off `.re`. -/

-- Theorem: under `hsep` and `hone`, the roots of `q` over `ℂ` are `z`, `z̄` and the six
-- real roots, which form a nodup `Multiset ℝ` of cardinality six.
theorem roots_eq_pair_add_real8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z) :
    ∃ R : Multiset ℝ, R.Nodup ∧ R.card = 6 ∧
      (q.map (algebraMap ℝ ℂ)).roots
        = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)) := by
  classical
  set qC : ℂ[X] := q.map (algebraMap ℝ ℂ) with hqC
  have hqCne : qC ≠ 0 := by rw [hqC]; exact (hmon.map _).ne_zero
  have hnodup : qC.roots.Nodup := by
    rw [hqC]; exact Polynomial.nodup_roots (hsep.map)
  have hcard : qC.roots.card = 8 := by
    rw [show qC.roots.card = qC.natDegree from
      (IsAlgClosed.splits qC).natDegree_eq_card_roots.symm]
    rw [hqC, Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, hnat]
  have hzmem : z ∈ qC.roots := by
    rw [hqC] at hz ⊢; exact (Polynomial.mem_roots hqCne).mpr hz
  have hzbar : starRingEnd ℂ z ∈ qC.roots := by
    refine (Polynomial.mem_roots hqCne).mpr ?_
    rw [Polynomial.IsRoot, hqC]
    rw [eval_map_conj q z, hz, map_zero]
  have hzbarim : (starRingEnd ℂ z).im ≠ 0 := by
    change -z.im ≠ 0
    exact neg_ne_zero.mpr hzim
  have hznez : z ≠ starRingEnd ℂ z := by
    intro h
    exact hzim (Complex.conj_eq_iff_im.mp h.symm)
  set nonR : Multiset ℂ := qC.roots.filter (fun w => w.im ≠ 0) with hnonR
  set realC : Multiset ℂ := qC.roots.filter (fun w => w.im = 0) with hrealC
  have hsplit : realC + nonR = qC.roots := by
    have h := Multiset.filter_add_not (p := fun w : ℂ => w.im = 0) qC.roots
    rw [hrealC, hnonR]
    simpa using h
  have hnonR_eq : nonR = z ::ₘ starRingEnd ℂ z ::ₘ (0 : Multiset ℂ) := by
    have hnonRnodup : nonR.Nodup := by
      rw [hnonR]; exact hnodup.filter _
    have hpairnodup : (z ::ₘ starRingEnd ℂ z ::ₘ (0 : Multiset ℂ)).Nodup := by
      simp [Multiset.nodup_cons, hznez]
    refine (Multiset.Nodup.ext hnonRnodup hpairnodup).mpr ?_
    intro w
    rw [hnonR]
    simp only [Multiset.mem_filter, Multiset.mem_cons, Multiset.notMem_zero, or_false]
    constructor
    · rintro ⟨hwr, hwim⟩
      have hroot : qC.eval w = 0 := (Polynomial.mem_roots hqCne).mp hwr
      exact hone w hroot hwim
    · rintro (h | h)
      · subst h; exact ⟨hzmem, hzim⟩
      · subst h; exact ⟨hzbar, hzbarim⟩
  set R : Multiset ℝ := realC.map (fun w => w.re) with hR
  have hRmap : R.map (algebraMap ℝ ℂ) = realC := by
    rw [hR, Multiset.map_map]
    nth_rewrite 2 [← Multiset.map_id realC]
    apply Multiset.map_congr rfl
    intro w hw
    have him : w.im = 0 := (Multiset.mem_filter.mp hw).2
    exact Complex.ext (by simp) (by simp [him])
  have hcardR : R.card = 6 := by
    have hnc : nonR.card = 2 := by rw [hnonR_eq]; simp
    have hsum : realC.card + nonR.card = qC.roots.card := by
      rw [← hsplit, Multiset.card_add]
    rw [hR, Multiset.card_map]
    omega
  have hRnodup : R.Nodup := by
    rw [hR]
    refine Multiset.Nodup.map_on ?_ (Multiset.Nodup.filter _ hnodup)
    intro a ha b hb hab
    have hai : a.im = 0 := (Multiset.mem_filter.mp ha).2
    have hbi : b.im = 0 := (Multiset.mem_filter.mp hb).2
    exact Complex.ext hab (by rw [hai, hbi])
  refine ⟨R, hRnodup, hcardR, ?_⟩
  rw [← hsplit, hnonR_eq, hRmap]
  rw [Multiset.add_cons, Multiset.add_cons, Multiset.add_zero]

end

end Pconstructible
