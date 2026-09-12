import Pptc.ScratchG

open Polynomial Matrix Module

namespace Pconstructible

noncomputable section

/-! ### The conjugate quadratic over `ℂ`

`conjQuad z` is the real quadratic with complex roots `z` and `z̄`.  Over `ℂ` it factors
as `(X - z) * (X - z̄)`, so it can be used to separate the conjugate pair `{z, z̄}` from
the other roots of a real polynomial. -/

-- Theorem: mapping the conjugate quadratic to `ℂ` factors it as `(X - z) * (X - z̄)`.
theorem conjQuad_map_eq_prod (z : ℂ) :
    (conjQuad z).map (algebraMap ℝ ℂ) = (X - C z) * (X - C (starRingEnd ℂ z)) := by
  have h1 : (algebraMap ℝ ℂ) (2 * z.re) = z + starRingEnd ℂ z :=
    (Complex.add_conj z).symm
  have h2 : (algebraMap ℝ ℂ) (z.re ^ 2 + z.im ^ 2) = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_apply, Complex.coe_algebraMap, Complex.ofReal_inj]
    ring
  rw [conjQuad]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  rw [h1, h2]
  simp only [Polynomial.C_add, Polynomial.C_mul]
  ring

-- Theorem: evaluation of a mapped real polynomial commutes with complex conjugation.
theorem eval_map_conj (f : ℝ[X]) (z : ℂ) :
    (f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)
      = starRingEnd ℂ ((f.map (algebraMap ℝ ℂ)).eval z) := by
  induction f using Polynomial.induction_on' with
  | add p r hp hr =>
      simp only [Polynomial.map_add, Polynomial.eval_add, map_add, hp, hr]
  | monomial n a =>
      simp only [Polynomial.map_monomial, Polynomial.eval_monomial, map_mul, map_pow]
      congr 1
      exact (Complex.conj_ofReal a).symm

/-! ### The Bring–Jerrard direction

For a monic separable real septic with a non-real root `z`, any complex value `c` can be
prescribed at `z`, with conjugate value forced at `z̄` and vanishing at every other root.
The construction factors `q = (conjQuad z) * G` over `ℝ`; over `ℂ` this is
`qC = (X - z)(X - z̄) * GC`, so `GC` is supported on the remaining roots.  Multiplying
`G` by a linear real polynomial `h` chosen so that `G(z) * h(z) = c` does the rest. -/

-- Theorem: for a monic separable real septic with a non-real complex root `z`, every
-- complex value is attained at `z` by a real polynomial of degree at most six that
-- vanishes at all other complex roots and takes the conjugate value at `z̄`.
theorem exists_poly_value_at_root (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (c : ℂ) :
    ∃ f : ℝ[X], f.natDegree ≤ 6 ∧
      (f.map (algebraMap ℝ ℂ)).eval z = c ∧
      (f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = starRingEnd ℂ c ∧
      ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z → x ≠ starRingEnd ℂ z →
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
  have hGdeg : G.natDegree = 5 := by
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
  have hfdeg : (G * h).natDegree ≤ 6 := by
    have := Polynomial.natDegree_mul_le_of_le (p := G) (q := h) (m := 5) (n := 1)
      (by omega) hhdeg
    simpa using this
  exact ⟨G * h, hfdeg, hfz, hfbar, hfother⟩

/-! ### Summing a function over a nodup multiset supported on two points -/

-- Theorem: for a nodup multiset of complex numbers, if `g` vanishes off `z` and `z'`, its
-- sum is `g z + g z'`.
theorem multiset_sum_eq_two_of_vanish {g : ℂ → ℂ} {s : Multiset ℂ} (hs : s.Nodup)
    {z z' : ℂ} (hz : z ∈ s) (hz' : z' ∈ s) (hzz' : z ≠ z')
    (hv : ∀ x : ℂ, x ∈ s → x ≠ z → x ≠ z' → g x = 0) :
    (s.map g).sum = g z + g z' := by
  have hval : s.toFinset.val = s := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hs]
  have h1 : (s.map g).sum = ∑ x ∈ s.toFinset, g x := by
    show (s.map g).sum = (s.toFinset.val.map g).sum
    rw [hval]
  have hsub : ({z, z'} : Finset ℂ) ⊆ s.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Multiset.mem_toFinset.mpr hz
    · exact Multiset.mem_toFinset.mpr hz'
  have hv' : ∀ x ∈ s.toFinset, x ∉ ({z, z'} : Finset ℂ) → g x = 0 := by
    intro x hx hxnot
    exact hv x (Multiset.mem_toFinset.mp hx)
      (fun hxz => hxnot (by rw [hxz]; simp))
      (fun hxz' => hxnot (by rw [hxz']; simp))
  rw [h1, ← Finset.sum_subset hsub hv']
  simp [hzz']

/-! ### Trace consequences -/

-- Theorem: a real polynomial taking the value `c` at a non-real root `z` and vanishing at
-- every other root has companion-matrix trace `c + c̄`.
theorem algebraMap_trace_eq_of_value (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (F : ℝ[X]) (c : ℂ)
    (hFz : (F.map (algebraMap ℝ ℂ)).eval z = c)
    (hFother : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → (F.map (algebraMap ℝ ℂ)).eval x = 0) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companion7 q) F)) = c + starRingEnd ℂ c := by
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
  rw [companion7_trace_aeval q F hmon hnat hsep]
  have hsum := multiset_sum_eq_two_of_vanish hnodup hzmem hzbarmem hzzber
    (g := fun x => (F.map (algebraMap ℝ ℂ)).eval x)
    (fun x hx hxz hxz' => hFother x ((Polynomial.mem_roots hqCne).mp hx) hxz hxz')
  rw [hsum]
  show (F.map (algebraMap ℝ ℂ)).eval z
      + (F.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = c + starRingEnd ℂ c
  rw [hFz, eval_map_conj F z, hFz]

-- Theorem: a real polynomial whose complex evaluation vanishes at every root of `qC` has
-- companion-matrix trace zero.
theorem trace_aeval_eq_zero_of_vanishes (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) (F : ℝ[X])
    (hF : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 →
      (F.map (algebraMap ℝ ℂ)).eval x = 0) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companion7 q) F)) = 0 := by
  have hqCne : (q.map (algebraMap ℝ ℂ)) ≠ 0 := (hmon.map (algebraMap ℝ ℂ)).ne_zero
  rw [companion7_trace_aeval q F hmon hnat hsep]
  apply Multiset.sum_eq_zero
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  exact hF x ((Polynomial.mem_roots hqCne).mp hx)

-- Theorem: for a non-real root `z`, some real polynomial of degree at most six has trace
-- `0` and trace of square `-2` in the companion matrix.
theorem exists_neg_trace (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) :
    ∃ f : ℝ[X], f.natDegree ≤ 6 ∧ Matrix.trace (aeval (companion7 q) f) = 0 ∧
      Matrix.trace ((aeval (companion7 q) f) ^ 2) = -2 := by
  obtain ⟨f, hfdeg, hfz, _hfbar, hfother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hz hzim Complex.I
  have hfsq : ((f ^ 2).map (algebraMap ℝ ℂ)).eval z = Complex.I ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfz]
  have hfothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((f ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfother x hx hxz hxz']
    simp
  have ht := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim f Complex.I hfz hfother
  have htsq := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim (f ^ 2) (Complex.I ^ 2)
    hfsq hfothersq
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hIc : starRingEnd ℂ ((Complex.I : ℂ) ^ 2) = -1 := by rw [hI, map_neg, map_one]
  refine ⟨f, hfdeg, ?_, ?_⟩
  · rw [Complex.conj_I, add_neg_cancel] at ht
    exact (algebraMap ℝ ℂ).injective (by simpa using ht)
  · have h2 : (Complex.I : ℂ) ^ 2 + starRingEnd ℂ ((Complex.I : ℂ) ^ 2) = -2 := by
      rw [hIc, hI]; norm_num
    rw [h2, map_pow] at htsq
    exact (algebraMap ℝ ℂ).injective (by simpa using htsq)

-- Theorem: for a non-real root `z`, some real polynomial of degree at most six has trace
-- `2` and trace of square `2` in the companion matrix.
theorem exists_pos_trace (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) :
    ∃ f : ℝ[X], f.natDegree ≤ 6 ∧ Matrix.trace (aeval (companion7 q) f) = 2 ∧
      Matrix.trace ((aeval (companion7 q) f) ^ 2) = 2 := by
  obtain ⟨f, hfdeg, hfz, _hfbar, hfother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hz hzim 1
  have hfsq : ((f ^ 2).map (algebraMap ℝ ℂ)).eval z = (1 : ℂ) ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfz]
  have hfothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((f ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfother x hx hxz hxz']
    simp
  have ht := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim f 1 hfz hfother
  have htsq := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim (f ^ 2) ((1 : ℂ) ^ 2)
    hfsq hfothersq
  refine ⟨f, hfdeg, ?_, ?_⟩
  · have h2 : (1 : ℂ) + starRingEnd ℂ (1 : ℂ) = 2 := by rw [map_one]; norm_num
    rw [h2] at ht
    exact (algebraMap ℝ ℂ).injective (by simpa using ht)
  · have h2 : ((1 : ℂ) ^ 2) + starRingEnd ℂ ((1 : ℂ) ^ 2) = 2 := by
      rw [one_pow, map_one]; norm_num
    rw [h2, map_pow] at htsq
    exact (algebraMap ℝ ℂ).injective (by simpa using htsq)

/-! ### Two conjugate pairs

Two non-real roots `z`, `w` from distinct conjugate pairs give polynomials supported on
disjoint sets of roots, so their traces and cross trace can be computed independently. -/

-- Theorem: two non-real roots from distinct conjugate pairs yield real polynomials of
-- degree at most six with vanishing traces, square traces `-2`, and vanishing cross trace.
theorem exists_neg_pair (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ f g : ℝ[X], f.natDegree ≤ 6 ∧ g.natDegree ≤ 6 ∧
      Matrix.trace (aeval (companion7 q) f) = 0 ∧ Matrix.trace (aeval (companion7 q) g) = 0 ∧
      Matrix.trace ((aeval (companion7 q) f) ^ 2) = -2 ∧
      Matrix.trace ((aeval (companion7 q) g) ^ 2) = -2 ∧
      Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)) = 0 := by
  obtain ⟨f, hfdeg, hfz, _hfbar, hfother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hz hzim Complex.I
  obtain ⟨g, hgdeg, hgw, _hgbar, hgother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hw hwim Complex.I
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
  have hfsq : ((f ^ 2).map (algebraMap ℝ ℂ)).eval z = Complex.I ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfz]
  have hfothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((f ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfother x hx hxz hxz']
    simp
  have hgsq : ((g ^ 2).map (algebraMap ℝ ℂ)).eval w = Complex.I ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hgw]
  have hgothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ w →
      x ≠ starRingEnd ℂ w → ((g ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxw hxw'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hgother x hx hxw hxw']
    simp
  have htf := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim f Complex.I hfz hfother
  have htf_sq := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim (f ^ 2) (Complex.I ^ 2)
    hfsq hfothersq
  have htg := algebraMap_trace_eq_of_value q hmon hnat hsep hw hwim g Complex.I hgw hgother
  have htg_sq := algebraMap_trace_eq_of_value q hmon hnat hsep hw hwim (g ^ 2) (Complex.I ^ 2)
    hgsq hgothersq
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hIc : starRingEnd ℂ ((Complex.I : ℂ) ^ 2) = -1 := by rw [hI, map_neg, map_one]
  have hcross := trace_aeval_eq_zero_of_vanishes q hmon hnat hsep (f * g) (by
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
  have htrace : Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)) = 0 := by
    have h1 : (aeval (companion7 q) f) * (aeval (companion7 q) g)
        = aeval (companion7 q) (f * g) := by rw [map_mul]
    rw [h1]
    exact (algebraMap ℝ ℂ).injective (by simpa using hcross)
  refine ⟨f, g, hfdeg, hgdeg, ?_, ?_, ?_, ?_, htrace⟩
  · rw [Complex.conj_I, add_neg_cancel] at htf
    exact (algebraMap ℝ ℂ).injective (by simpa using htf)
  · rw [Complex.conj_I, add_neg_cancel] at htg
    exact (algebraMap ℝ ℂ).injective (by simpa using htg)
  · have h2 : (Complex.I : ℂ) ^ 2 + starRingEnd ℂ ((Complex.I : ℂ) ^ 2) = -2 := by
      rw [hIc, hI]; norm_num
    rw [h2, map_pow] at htf_sq
    exact (algebraMap ℝ ℂ).injective (by simpa using htf_sq)
  · have h2 : (Complex.I : ℂ) ^ 2 + starRingEnd ℂ ((Complex.I : ℂ) ^ 2) = -2 := by
      rw [hIc, hI]; norm_num
    rw [h2, map_pow] at htg_sq
    exact (algebraMap ℝ ℂ).injective (by simpa using htg_sq)

-- Theorem: two non-real roots from distinct conjugate pairs yield real polynomials of
-- degree at most six with traces `2`, square traces `2`, and vanishing cross trace.
theorem exists_pos_pair (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ f g : ℝ[X], f.natDegree ≤ 6 ∧ g.natDegree ≤ 6 ∧
      Matrix.trace (aeval (companion7 q) f) = 2 ∧ Matrix.trace (aeval (companion7 q) g) = 2 ∧
      Matrix.trace ((aeval (companion7 q) f) ^ 2) = 2 ∧
      Matrix.trace ((aeval (companion7 q) g) ^ 2) = 2 ∧
      Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)) = 0 := by
  obtain ⟨f, hfdeg, hfz, _hfbar, hfother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hz hzim 1
  obtain ⟨g, hgdeg, hgw, _hgbar, hgother⟩ :=
    exists_poly_value_at_root q hmon hnat hsep hw hwim 1
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
  have hfsq : ((f ^ 2).map (algebraMap ℝ ℂ)).eval z = (1 : ℂ) ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfz]
  have hfothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → ((f ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxz hxz'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hfother x hx hxz hxz']
    simp
  have hgsq : ((g ^ 2).map (algebraMap ℝ ℂ)).eval w = (1 : ℂ) ^ 2 := by
    rw [Polynomial.map_pow, Polynomial.eval_pow, hgw]
  have hgothersq : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ w →
      x ≠ starRingEnd ℂ w → ((g ^ 2).map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx hxw hxw'
    rw [Polynomial.map_pow, Polynomial.eval_pow, hgother x hx hxw hxw']
    simp
  have htf := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim f 1 hfz hfother
  have htf_sq := algebraMap_trace_eq_of_value q hmon hnat hsep hz hzim (f ^ 2) ((1 : ℂ) ^ 2)
    hfsq hfothersq
  have htg := algebraMap_trace_eq_of_value q hmon hnat hsep hw hwim g 1 hgw hgother
  have htg_sq := algebraMap_trace_eq_of_value q hmon hnat hsep hw hwim (g ^ 2) ((1 : ℂ) ^ 2)
    hgsq hgothersq
  have hcross := trace_aeval_eq_zero_of_vanishes q hmon hnat hsep (f * g) (by
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
  have htrace : Matrix.trace ((aeval (companion7 q) f) * (aeval (companion7 q) g)) = 0 := by
    have h1 : (aeval (companion7 q) f) * (aeval (companion7 q) g)
        = aeval (companion7 q) (f * g) := by rw [map_mul]
    rw [h1]
    exact (algebraMap ℝ ℂ).injective (by simpa using hcross)
  refine ⟨f, g, hfdeg, hgdeg, ?_, ?_, ?_, ?_, htrace⟩
  · have h2 : (1 : ℂ) + starRingEnd ℂ (1 : ℂ) = 2 := by rw [map_one]; norm_num
    rw [h2] at htf
    exact (algebraMap ℝ ℂ).injective (by simpa using htf)
  · have h2 : (1 : ℂ) + starRingEnd ℂ (1 : ℂ) = 2 := by rw [map_one]; norm_num
    rw [h2] at htg
    exact (algebraMap ℝ ℂ).injective (by simpa using htg)
  · have h2 : ((1 : ℂ) ^ 2) + starRingEnd ℂ ((1 : ℂ) ^ 2) = 2 := by
      rw [one_pow, map_one]; norm_num
    rw [h2, map_pow] at htf_sq
    exact (algebraMap ℝ ℂ).injective (by simpa using htf_sq)
  · have h2 : ((1 : ℂ) ^ 2) + starRingEnd ℂ ((1 : ℂ) ^ 2) = 2 := by
      rw [one_pow, map_one]; norm_num
    rw [h2, map_pow] at htg_sq
    exact (algebraMap ℝ ℂ).injective (by simpa using htg_sq)

end

end Pconstructible
