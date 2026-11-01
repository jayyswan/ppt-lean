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

import Pptc.Octic.Sextic
import Pptc.Octic.Resolvent

/-! # Pptc.Octic.OnePair

The octic with exactly one conjugate pair of non-real roots (`s = 1`).

A real octic with one conjugate pair `{z, z̄}` has six real roots, so the companion matrix has
signature `(7 - s, s) = (6, 1)` on the seven-dimensional trace-zero space.  With `s = 1` the
trace form `Q = qform (Gram8 q)` has no totally isotropic plane: `Q x = Q y = B x y = 0` with
`y ≠ 0` forces `x ∥ y` (`isotropic_plane_trivial8`).  This is exactly where the octic differs
from the `s ≥ 2` case, where two independent isotropic directions exist.

The certificate is a Lagrange polynomial of degree at most seven, normalised to `1` at one real
root and `0` at the others and corrected at `z` to take a prescribed value `c`.  Its first three
trace power sums at `companionN (n := 8) q` are `0`, `0`, `3`.

The vanishing argument needs eight distinct roots: a polynomial of degree `< 8` that vanishes at
all eight roots of a separable octic is zero. -/

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### The cubic certificate for the one-conjugate-pair octic

Given a monic separable real octic `q` with a single non-real conjugate pair `{z, z̄}` and a
prescribed complex value `c` with `c + c̄ = -1`, `c c̄ = 1`, we build a real polynomial `X` of
degree at most seven whose values at `z`, `z̄` are `c`, `c̄`, which equals `1` at the chosen real
root `x` and vanishes at every other real root of `q`.  Because the non-real values contribute
`c ^ k + c̄ ^ k` and the real ones contribute `1` for the root `x` and `0` elsewhere, the first
three trace power sums of `X(companionN q)` are `0`, `0`, `3`.

The construction is the Lagrange base `L = (q'(x))⁻¹ · (q /ₘ (X - C x))`, normalised to `1` at
`x` and `0` at the other roots, corrected at `z` by `exists_poly_value_at_root8`. -/

-- Theorem: for a monic separable octic `q` with one non-real conjugate pair `{z, z̄}` and a
-- complex `c` with `c + c̄ = -1`, `c c̄ = 1`, there is a real polynomial `X` of degree at most
-- seven attaining `c`, `c̄` at `z`, `z̄`, equal to `1` at the real root `x`, vanishing at the
-- other real roots, and whose first three trace power sums at `companionN (n := 8) q` are
-- `0`, `0`, `3`.
theorem exists_lagrange_value8 {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {x : ℝ} (hx : q.eval x = 0) (hxz : (x : ℂ) ≠ z) (hxz' : (x : ℂ) ≠ starRingEnd ℂ z)
    {c : ℂ} (hc1 : c + starRingEnd ℂ c = -1) (hc2 : c * starRingEnd ℂ c = 1) :
    ∃ X : ℝ[X], X.natDegree ≤ 7 ∧
      (X.map (algebraMap ℝ ℂ)).eval z = c ∧
      (X.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = starRingEnd ℂ c ∧
      X.eval x = 1 ∧
      (∀ r : ℝ, q.eval r = 0 → r ≠ x → X.eval r = 0) ∧
      Matrix.trace (aeval (companionN (n := 8) q) X) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) X) ^ 2) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) X) ^ 3) = 3 := by
  classical
  have hqCne : (q.map (algebraMap ℝ ℂ)) ≠ 0 := (hmon.map (algebraMap ℝ ℂ)).ne_zero
  have hxrootC : (q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hx, map_zero]
  have hxzC : (algebraMap ℝ ℂ x) ≠ z := by simpa using hxz
  have hxzC' : (algebraMap ℝ ℂ x) ≠ starRingEnd ℂ z := by simpa using hxz'
  -- Lagrange base at the real root `x`
  set m : ℝ[X] := Polynomial.X - C x with hm
  have hmmon : m.Monic := by rw [hm]; exact Polynomial.monic_X_sub_C x
  have hmdvd : m ∣ q := by
    rw [hm]
    exact (Polynomial.dvd_iff_isRoot).mpr hx
  have hmod : q %ₘ m = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hmmon).mpr hmdvd
  have hdiv : m * (q /ₘ m) = q := by
    have h := Polynomial.modByMonic_add_div q m
    rw [hmod, zero_add] at h
    exact h
  have hd : (q /ₘ m).eval x = q.derivative.eval x := by
    have h := congrArg (fun p : ℝ[X] => p.derivative.eval x) hdiv
    rw [Polynomial.derivative_mul, hm] at h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.derivative_X_sub_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_self, zero_mul, add_zero, one_mul] at h
    exact h
  have hdne : q.derivative.eval x ≠ 0 := by
    have h := hsep.aeval_derivative_ne_zero (x := x) (by simpa using hx)
    simpa using h
  set L : ℝ[X] := C ((q.derivative.eval x)⁻¹) * (q /ₘ m) with hL
  have hLdeg : L.natDegree ≤ 7 := by
    rw [hL]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_divByMonic q (Polynomial.monic_X_sub_C x),
      Polynomial.natDegree_X_sub_C, hnat]
  have hLx : L.eval x = 1 := by
    rw [hL, Polynomial.eval_mul, Polynomial.eval_C, hd, inv_mul_cancel₀ hdne]
  have hLother : ∀ r : ℝ, q.eval r = 0 → r ≠ x → L.eval r = 0 := by
    intro r hr hrx
    have hmr : m.eval r ≠ 0 := by
      rw [hm]
      simpa using sub_ne_zero.mpr hrx
    have hq0 : m.eval r * (q /ₘ m).eval r = 0 := by
      rw [← Polynomial.eval_mul, hdiv]
      exact hr
    have hdiv0 : (q /ₘ m).eval r = 0 := (mul_eq_zero.mp hq0).resolve_left hmr
    rw [hL, Polynomial.eval_mul, Polynomial.eval_C, hdiv0, mul_zero]
  -- correction at `z` via the Bring–Jerrard direction
  obtain ⟨A, hAdeg, hAz, hAzbar, hAother⟩ :=
    exists_poly_value_at_root8 q hmon hnat hsep hz hzim (c - (L.map (algebraMap ℝ ℂ)).eval z)
  set P : ℝ[X] := L + A with hP
  have hPdeg : P.natDegree ≤ 7 := by
    rw [hP]
    exact (Polynomial.natDegree_add_le L A).trans (max_le hLdeg hAdeg)
  have hPz : (P.map (algebraMap ℝ ℂ)).eval z = c := by
    rw [hP, Polynomial.map_add, Polynomial.eval_add, hAz]
    ring
  have hPzbar : (P.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = starRingEnd ℂ c := by
    rw [hP, Polynomial.map_add, Polynomial.eval_add, eval_map_conj L z, hAzbar, map_sub]
    ring
  have hPx : P.eval x = 1 := by
    have hAx : A.eval x = 0 := by
      have h := hAother (algebraMap ℝ ℂ x) hxrootC hxzC hxzC'
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply] at h
      exact (algebraMap ℝ ℂ).injective (by simpa using h)
    rw [hP, Polynomial.eval_add, hLx, hAx, add_zero]
  have hPother : ∀ r : ℝ, q.eval r = 0 → r ≠ x → P.eval r = 0 := by
    intro r hr hrx
    have hAr : A.eval r = 0 := by
      have hrC : (q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = 0 := by
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]
      have hrz : (algebraMap ℝ ℂ r) ≠ z := fun h => hzim (by rw [← h]; simp)
      have hrz' : (algebraMap ℝ ℂ r) ≠ starRingEnd ℂ z := fun h => by
        have hc := congrArg Complex.im h
        simp at hc
        exact hzim (by linarith)
      have h := hAother (algebraMap ℝ ℂ r) hrC hrz hrz'
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply] at h
      exact (algebraMap ℝ ℂ).injective (by simpa using h)
    rw [hP, Polynomial.eval_add, hLother r hr hrx, hAr, add_zero]
  -- the root multiset decomposes into the conjugate pair and the real roots
  obtain ⟨R, hRnodup, _hRcard, hroots⟩ :=
    roots_eq_pair_add_real8 q hmon hnat hsep hz hzim hone
  have hxmemC : (algebraMap ℝ ℂ x) ∈ (q.map (algebraMap ℝ ℂ)).roots :=
    (Polynomial.mem_roots hqCne).mpr hxrootC
  have hxmemC' : (algebraMap ℝ ℂ x) ∈ R.map (algebraMap ℝ ℂ) := by
    have h := hxmemC
    rw [hroots] at h
    simp only [Multiset.mem_cons] at h
    rcases h with h | h | h
    · exact absurd h hxzC
    · exact absurd h hxzC'
    · exact h
  have hxmem : x ∈ R := by
    rwa [Multiset.mem_map_of_injective (algebraMap ℝ ℂ).injective] at hxmemC'
  have hRroot : ∀ r ∈ R, q.eval r = 0 := by
    intro r hr
    have hmemR : (algebraMap ℝ ℂ r) ∈ R.map (algebraMap ℝ ℂ) :=
      (Multiset.mem_map_of_injective (algebraMap ℝ ℂ).injective).mpr hr
    have hmem : (algebraMap ℝ ℂ r) ∈ (q.map (algebraMap ℝ ℂ)).roots := by
      rw [hroots]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hmemR)
    have hroot := (Polynomial.mem_roots hqCne).mp hmem
    change (q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = 0 at hroot
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply] at hroot
    exact (algebraMap ℝ ℂ).injective (by simpa using hroot)
  set S : Multiset ℝ := R.erase x with hS
  have hR_eq : R = x ::ₘ S := by
    rw [hS]
    exact (Multiset.cons_erase hxmem).symm
  have hS_mem : ∀ r ∈ S, r ∈ R.erase x := fun r hr => by rwa [hS] at hr
  have hS_root : ∀ r ∈ S, q.eval r = 0 := fun r hr =>
    hRroot r (hRnodup.mem_erase_iff.mp (hS_mem r hr)).2
  have hS_ne : ∀ r ∈ S, r ≠ x := fun r hr =>
    (hRnodup.mem_erase_iff.mp (hS_mem r hr)).1
  have hPeval : ∀ r ∈ S, P.eval r = 0 := fun r hr =>
    hPother r (hS_root r hr) (hS_ne r hr)
  -- power sum of `P` over the complex roots
  have hsum (k : ℕ) (hk : k ≠ 0) :
      ((q.map (algebraMap ℝ ℂ)).roots.map
        (fun w => ((P.map (algebraMap ℝ ℂ)).eval w) ^ k)).sum
        = c ^ k + (starRingEnd ℂ c) ^ k + 1 := by
    have hrest : ((R.map (algebraMap ℝ ℂ)).map
          (fun w => ((P.map (algebraMap ℝ ℂ)).eval w) ^ k)).sum = 1 := by
      rw [hR_eq, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons]
      have hhead : ((P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x)) ^ k = 1 := by
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hPx]
        simp
      have htail : ((S.map (algebraMap ℝ ℂ)).map
            (fun w => ((P.map (algebraMap ℝ ℂ)).eval w) ^ k)).sum = 0 := by
        have hmap0 : (S.map (algebraMap ℝ ℂ)).map
              (fun w => ((P.map (algebraMap ℝ ℂ)).eval w) ^ k)
            = S.map (fun _ => (0 : ℂ)) := by
          rw [Multiset.map_map]
          exact Multiset.map_congr rfl (fun r hr => by
            change ((P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r)) ^ k = (0 : ℂ)
            rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hPeval r hr]
            simp [zero_pow hk])
        rw [hmap0, Multiset.sum_map_zero]
      simp only [hhead, htail, add_zero]
    rw [hroots, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
    simp only [hPz, hPzbar, hrest]
    ring
  have ht1 : Matrix.trace (aeval (companionN (n := 8) q) P) = 0 := by
    have h := companionN_trace_pow_aeval8 q P hmon hnat hsep 1
    rw [hsum 1 (by norm_num)] at h
    rw [pow_one] at h
    refine (algebraMap ℝ ℂ).injective ?_
    rw [h, map_zero]
    linear_combination hc1
  have ht2 : Matrix.trace ((aeval (companionN (n := 8) q) P) ^ 2) = 0 := by
    have h := companionN_trace_pow_aeval8 q P hmon hnat hsep 2
    rw [hsum 2 (by norm_num)] at h
    refine (algebraMap ℝ ℂ).injective ?_
    rw [h, map_zero]
    linear_combination (c + starRingEnd ℂ c - 1) * hc1 - 2 * hc2
  have ht3 : Matrix.trace ((aeval (companionN (n := 8) q) P) ^ 3) = 3 := by
    have h := companionN_trace_pow_aeval8 q P hmon hnat hsep 3
    rw [hsum 3 (by norm_num)] at h
    have h3 : (algebraMap ℝ ℂ (3 : ℝ)) = (3 : ℂ) := by norm_num
    refine (algebraMap ℝ ℂ).injective ?_
    rw [h, h3]
    linear_combination ((c + starRingEnd ℂ c + 1) ^ 2
        - 3 * (c + starRingEnd ℂ c + 1) - 3 * (c * starRingEnd ℂ c - 1)) * hc1
      + 3 * hc2
  exact ⟨P, hPdeg, hPz, hPzbar, hPx, hPother, ht1, ht2, ht3⟩

/-! ### F5. There is no totally isotropic plane when `s = 1`

With a single conjugate pair `{z, z̄}`, the trace form `Q = qform (Gram8 q)` has no totally
isotropic plane: `Q x = Q y = B x y = 0` with `y ≠ 0` forces `x ∥ y`.

For `a b : ℝ` put `H = a F + b G`, where `F, G` are the degree-`≤ 7` polynomials of `x, y`.
The second power sum identity `companionN_trace_pow_aeval8` and the root decomposition
`roots_eq_pair_add_real8` give, over `ℂ`, that the sum of the squares of `H` over the roots
of `q` vanishes.  The conjugate pair contributes `2 Re (H(z)²)` and the other six roots are
real, so
`∑_r H(r)² + 2 Re (H(z)²) = 0`
for every `a, b`.  If `F(z), G(z)` are `ℝ`-dependent there is a nonzero `(a, b)` with
`H(z) = 0`, so the sum of squares vanishes termwise and `H`, of degree `≤ 7`, vanishes at the
eight distinct roots of `q`; hence `H = 0`.  Otherwise some `H` realises `H(z) = 1`, forcing
the sum of squares to be `-2 < 0`, a contradiction. -/

-- Theorem: `vecOf8` is a left inverse of `polyOfVec8`.
private lemma vecOf8_polyOfVec8 (v : Fin 8 → ℝ) : vecOf8 (polyOfVec8 v) = v := by
  funext i
  have hc : (polyOfVec8 v).coeff i.val = v i := by
    rw [polyOfVec8, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Polynomial.coeff_monomial]
      split_ifs with h
      · exact absurd (Fin.ext h) hji
      · rfl
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simpa [vecOf8] using hc

-- Theorem: evaluation of a mapped real polynomial at a real point.
private lemma eval_map_ofReal (f : ℝ[X]) (r : ℝ) :
    (f.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = ((f.eval r : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (f := algebraMap ℝ ℂ) (r := r) (p := f)

-- `ofReal_multiset_sum` is dimension-free and already provided by `Pptc.DegreeSeven`
-- (namespace `Pconstructible`), so it is reused here rather than restated.

-- Theorem: the evaluation at `z` of `(C a * F + C b * G).map` is `a * F(z) + b * G(z)`.
private lemma eval_C_mul_add (F G : ℝ[X]) (z : ℂ) (a b : ℝ) :
    (((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval z)
      = (a : ℂ) * ((F.map (algebraMap ℝ ℂ)).eval z)
        + (b : ℂ) * ((G.map (algebraMap ℝ ℂ)).eval z) := by
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_C]
  simp

-- Theorem: the real sum of squares identity attached to the trace power sum.
private theorem sum_sq_add_pair_re8 {q H : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)))
    (htrace : Matrix.trace ((aeval (companionN (n := 8) q) H) ^ 2) = 0) :
    (R.map (fun r => (H.eval r) ^ 2)).sum
      + 2 * ((((H.map (algebraMap ℝ ℂ)).eval z) ^ 2).re) = 0 := by
  have htr := companionN_trace_pow_aeval8 q H hmon hnat hsep 2
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
    have hfun : (fun r => ((H.eval r) ^ 2 : ℂ))
        = (fun r => (((H.eval r) ^ 2 : ℝ) : ℂ)) := by
      funext r
      push_cast
      ring
    rw [hfun, ofReal_multiset_sum, hS]
  rw [hzbar, hRmap] at hsum
  have hmain : (2 * (w ^ 2).re + S : ℝ) = 0 := by
    rw [← add_assoc, Complex.add_conj] at hsum
    exact_mod_cast hsum
  rw [hS]
  linarith

-- Theorem: a degree-`≤ 7` real polynomial vanishing at all complex roots of a separable
-- octic `q` is zero.
lemma eq_zero_of_vanishes_on_roots8 {q H : ℝ[X]} (hnat : q.natDegree = 8) (hsep : q.Separable)
    (hHdeg : H.natDegree ≤ 7)
    (h : ∀ w : ℂ, w ∈ (q.map (algebraMap ℝ ℂ)).roots →
      (H.map (algebraMap ℝ ℂ)).eval w = 0) : H = 0 := by
  have hnodup : (q.map (algebraMap ℝ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots (hsep.map)
  have hcardC : (q.map (algebraMap ℝ ℂ)).roots.card = 8 := by
    rw [show (q.map (algebraMap ℝ ℂ)).roots.card
        = (q.map (algebraMap ℝ ℂ)).natDegree from
      (IsAlgClosed.splits (q.map (algebraMap ℝ ℂ))).natDegree_eq_card_roots.symm]
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, hnat]
  have hcardfin : Fintype.card ((q.map (algebraMap ℝ ℂ)).roots.toFinset) = 8 := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcardC]
  have hdegC : (H.map (algebraMap ℝ ℂ)).natDegree < 8 := by
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
theorem isotropic_plane_trivial8 {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z) :
    ∀ x y : Fin 7 → ℝ, qform (Gram8 q) x = 0 → qform (Gram8 q) y = 0 →
      bilin (Gram8 q) x y = 0 → y ≠ 0 → ∃ c : ℝ, x = c • y := by
  intro x y hQx hQy hBxy hyne
  set F : ℝ[X] := polyOfVec8 (Lcomb8 q x) with hF
  set G : ℝ[X] := polyOfVec8 (Lcomb8 q y) with hG
  have hFdeg : F.natDegree ≤ 7 := by rw [hF]; exact polyOfVec8_natDegree_le _
  have hGdeg : G.natDegree ≤ 7 := by rw [hG]; exact polyOfVec8_natDegree_le _
  have hvecF : vecOf8 F = Lcomb8 q x := by rw [hF]; exact vecOf8_polyOfVec8 _
  have hvecG : vecOf8 G = Lcomb8 q y := by rw [hG]; exact vecOf8_polyOfVec8 _
  obtain ⟨R, _hRnodup, _hRcard, hroots⟩ :=
    roots_eq_pair_add_real8 q hmon hnat hsep hz hzim hone
  have hpoly : ∀ a b : ℝ,
      C a * F + C b * G = polyOfVec8 (Lcomb8 q (a • x + b • y)) := by
    intro a b
    rw [← polyOfVec8_smul_add hFdeg hGdeg, hvecF, hvecG, Lcomb8_smul_add]
  have hHdeg : ∀ a b : ℝ, (C a * F + C b * G).natDegree ≤ 7 := by
    intro a b
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_C_mul_le a F) hFdeg
    · exact le_trans (Polynomial.natDegree_C_mul_le b G) hGdeg
  have key : ∀ a b : ℝ,
      (R.map (fun r => ((C a * F + C b * G).eval r) ^ 2)).sum
        + 2 * (((((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval z) ^ 2).re) = 0 := by
    intro a b
    have hQab : qform (Gram8 q) (a • x + b • y) = 0 := by
      rw [qform_smul_add (Gram8 q) (Gram8_symm q) a b x y, hQx, hQy, hBxy]
      ring
    have htrace : Matrix.trace
        ((aeval (companionN (n := 8) q) (C a * F + C b * G)) ^ 2) = 0 := by
      rw [hpoly a b, ← qform_Gram8_eq_trace_sq]
      exact hQab
    exact sum_sq_add_pair_re8 hmon hnat hsep hroots htrace
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
      eq_zero_of_vanishes_on_roots8 hnat hsep (hHdeg a b) hrootzero
    have hL0 : Lcomb8 q (a • x + b • y) = 0 := by
      rw [hpoly a b] at hH0
      by_contra hne
      exact polyOfVec8_ne_zero hne hH0
    have hab0 : a • x + b • y = 0 := Lcomb8_injective q hL0
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

/-! ### Part B: the sign certificate and the assembly

On the light cone `{Q = 0}` through a nonzero `P₀`, the reduced cubic `p3vec8 q ∘ Lcomb8 q ∘
stereoN` takes both signs.  The lynchpin is the Lagrange polynomial `X` of part A, with
`X(x_j) = 1` at one real root, `0` at the other real roots and `ω = -1/2 + (√3/2) i` at `z`;
its conjugate takes `ω̄` at `z`.  Writing `b = bilin (Gram8 q) P₀ (coeff7 (vecOf8 X))`, the
trace split identity gives `b = y_j + u ω + ū ω̄`, where `y_j` is the value of
`F₀ = polyOfVec8 (Lcomb8 q P₀)` at `x_j` and `u = F₀(z)`, so the two `b`'s multiply to
`(y_j - Re u)² - 3 (Im u)²`.  Since `Q P₀ = 0` forces `(Im u)² = (Re u)² + S/2` with
`S = Σ_r F₀(r)²`, one of the two products is negative, and
`p3vec_Lcomb_stereo_of_qform_zero8` turns that into a strict sign change.

The final assembly rationalises the two witnesses, solves the sextic along the line joining
them (degree `≤ 6`, because `stereoN` is quadratic and `p3vec8` is cubic), and reads off the
Tschirnhaus polynomial `φ = polyOfVec8 (Lcomb8 q vstar)`. -/

namespace Pconstructible

noncomputable section

open Polynomial Matrix

-- Theorem: on the cone, `stereoN` is a scalar multiple of `x`, and the reduced cubic scales
-- by the cube of that multiple: `p3vec8 q (stereoN x) = -8 (B P₀ x)^3 p3vec8 q (Lcomb8 q x)`.
theorem p3vec_Lcomb_stereo_of_qform_zero8 (q : ℝ[X]) {P₀ x : Fin 7 → ℝ}
    (hx : qform (Gram8 q) x = 0) :
    p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ x))
      = -8 * (bilin (Gram8 q) P₀ x) ^ 3 * p3vec8 q (Lcomb8 q x) := by
  have hvec : stereoN (Gram8 q) P₀ x = (-2 * bilin (Gram8 q) P₀ x) • x := by
    rw [stereoN, hx]
    module
  rw [hvec, Lcomb8_smul, p3vec8_smul]
  ring

-- Theorem: every element of the real multiset `R` is a real root of `q`.
lemma root_of_mem_R8 {q : ℝ[X]} (hmon : q.Monic) {z : ℂ} {R : Multiset ℝ}
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

-- Theorem: `bilin (Hmat8 q) (vecOf8 f) (vecOf8 g) = trace (N_f N_g)`.
lemma bilin_Hmat8_vecOf8 (q : ℝ[X]) (f g : ℝ[X]) (hf : f.natDegree ≤ 7)
    (hg : g.natDegree ≤ 7) :
    bilin (Hmat8 q) (vecOf8 f) (vecOf8 g)
      = Matrix.trace ((aeval (companionN (n := 8) q) f)
        * (aeval (companionN (n := 8) q) g)) := by
  have hfg : (f + g).natDegree ≤ 7 :=
    le_trans (Polynomial.natDegree_add_le f g) (max_le hf hg)
  have h1 := qform_add (Hmat8 q) (Hmat8_symm q) (vecOf8 f) (vecOf8 g)
  have hv : vecOf8 f + vecOf8 g = vecOf8 (f + g) := by
    ext i
    simp [vecOf8, Polynomial.coeff_add]
  rw [hv] at h1
  have hqf : qform (Hmat8 q) (vecOf8 f)
      = Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) := by
    rw [qform_Hmat8_eq_hermiteForm8, hermiteForm8_eq_trace_sq, polyOfVec8_vecOf8 hf]
  have hqg : qform (Hmat8 q) (vecOf8 g)
      = Matrix.trace ((aeval (companionN (n := 8) q) g) ^ 2) := by
    rw [qform_Hmat8_eq_hermiteForm8, hermiteForm8_eq_trace_sq, polyOfVec8_vecOf8 hg]
  have hqfg : qform (Hmat8 q) (vecOf8 (f + g))
      = Matrix.trace ((aeval (companionN (n := 8) q) (f + g)) ^ 2) := by
    rw [qform_Hmat8_eq_hermiteForm8, hermiteForm8_eq_trace_sq, polyOfVec8_vecOf8 hfg]
  rw [hqfg, hqf, hqg] at h1
  have htr := trace_sq_smul_add8 (aeval (companionN (n := 8) q) f)
    (aeval (companionN (n := 8) q) g) 1 1
  have hmap : aeval (companionN (n := 8) q) (f + g)
      = (1 : ℝ) • aeval (companionN (n := 8) q) f
        + (1 : ℝ) • aeval (companionN (n := 8) q) g := by
    rw [map_add]; simp
  rw [hmap] at h1
  rw [h1] at htr
  simp only [one_pow, one_mul] at htr
  linarith

-- Theorem: `trace (N_f N_g)` splits as the sum over the six real roots plus the two
-- non-real terms `f(z) g(z)` and `f(z̄) g(z̄)`.
theorem ofReal_trace_mul_eq_sum8 (q f g : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ))) :
    algebraMap ℝ ℂ (Matrix.trace ((aeval (companionN (n := 8) q) f)
        * (aeval (companionN (n := 8) q) g)))
      = ((R.map (fun r => f.eval r * g.eval r)).sum : ℂ)
        + ((f.map (algebraMap ℝ ℂ)).eval z) * ((g.map (algebraMap ℝ ℂ)).eval z)
        + ((f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z))
            * ((g.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)) := by
  have h := companionN_trace_aeval8 q (f * g) hmon hnat hsep
  rw [map_mul] at h
  rw [hroots, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons] at h
  simp only [Polynomial.map_mul, Polynomial.eval_mul] at h
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

-- Theorem: for a prescribed value `c` at `z` with `c + c̄ = -1`, `c c̄ = 1`, the Lagrange
-- polynomial of part A yields a cone direction `d` with `p3vec8 = 3` and the stated bilinear
-- value against `P₀`.
theorem exists_direction_of_value8 {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)))
    (hRroot : ∀ r ∈ R, q.eval r = 0) (hRnodup : R.Nodup)
    {P₀ : Fin 7 → ℝ} {xj : ℝ} (hxjmem : xj ∈ R)
    {c : ℂ} (hc1 : c + starRingEnd ℂ c = -1) (hc2 : c * starRingEnd ℂ c = 1) :
    ∃ (d : Fin 7 → ℝ) (b : ℝ),
      qform (Gram8 q) d = 0 ∧
      p3vec8 q (Lcomb8 q d) = 3 ∧
      (b : ℂ) = (((polyOfVec8 (Lcomb8 q P₀)).eval xj : ℝ) : ℂ)
        + ((polyOfVec8 (Lcomb8 q P₀)).map (algebraMap ℝ ℂ)).eval z * c
        + starRingEnd ℂ (((polyOfVec8 (Lcomb8 q P₀)).map (algebraMap ℝ ℂ)).eval z)
          * starRingEnd ℂ c ∧
      bilin (Gram8 q) P₀ d = b := by
  classical
  set F0 : ℝ[X] := polyOfVec8 (Lcomb8 q P₀) with hF0
  have hF0deg : F0.natDegree ≤ 7 := by rw [hF0]; exact polyOfVec8_natDegree_le _
  have hvecF0 : vecOf8 F0 = Lcomb8 q P₀ := by rw [hF0, vecOf8_polyOfVec8]
  have hxjroot : q.eval xj = 0 := hRroot xj hxjmem
  have hxjz : (algebraMap ℝ ℂ xj) ≠ z := fun h => hzim (by rw [← h]; simp)
  have hxjz' : (algebraMap ℝ ℂ xj) ≠ starRingEnd ℂ z := fun h => by
    have hc := congrArg Complex.im h
    simp at hc
    exact hzim (by linarith)
  obtain ⟨X, hXdeg, hXz, hXzbar, hXxj, hXother, ht1, ht2, ht3⟩ :=
    exists_lagrange_value8 hmon hnat hsep hz hzim hone hxjroot hxjz hxjz' hc1 hc2
  have hp1X : p1vec8 q (vecOf8 X) = 0 := by
    rw [p1vec8_vecOf8 q X hXdeg, ht1]
  have hLcombX : Lcomb8 q (coeff7 (vecOf8 X)) = vecOf8 X := Lcomb8_coeff7 q hp1X
  have hqform_d : qform (Gram8 q) (coeff7 (vecOf8 X)) = 0 := by
    rw [← qform_Gram8_Lcomb8 q (coeff7 (vecOf8 X)), hLcombX, qform_Hmat8_eq_hermiteForm8,
      hermiteForm8_eq_trace_sq, polyOfVec8_vecOf8 hXdeg, ht2]
  have hp3_d : p3vec8 q (Lcomb8 q (coeff7 (vecOf8 X))) = 3 := by
    rw [hLcombX, p3vec8, polyOfVec8_vecOf8 hXdeg, ht3]
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
  have htrace_eq : Matrix.trace ((aeval (companionN (n := 8) q) F0)
      * (aeval (companionN (n := 8) q) X))
      = bilin (Gram8 q) P₀ (coeff7 (vecOf8 X)) := by
    rw [← bilin_Hmat8_vecOf8 q F0 X hF0deg hXdeg]
    conv_lhs => rw [hvecF0, ← hLcombX]
    rw [bilin_Hmat8_Lcomb8]
  have hsplit := ofReal_trace_mul_eq_sum8 q F0 X hmon hnat hsep hroots
  rw [hRval, hXz, hXzbar, eval_map_conj F0 z] at hsplit
  refine ⟨coeff7 (vecOf8 X), bilin (Gram8 q) P₀ (coeff7 (vecOf8 X)), hqform_d, hp3_d, ?_,
    rfl⟩
  rw [← htrace_eq]
  exact hsplit

-- Theorem: the real arithmetic behind the sign certificate.  If `y₁² + y₂² ≤ S` and
-- `γ² = α² + S/2`, then either one of the products `b_j = (y_j - α)² - 3γ²` is negative,
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

-- Theorem: on the light cone through a nonzero `P₀` the reduced cubic `p3vec8` takes both
-- signs (the sign certificate of `PLAN.md` §2.8).
theorem exists_sign_change8 {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable)
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {P₀ : Fin 7 → ℝ} (hQ₀ : qform (Gram8 q) P₀ = 0) (hP₀ne : P₀ ≠ 0) :
    ∃ dplus dminus : Fin 7 → ℝ,
      0 < p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ dplus)) ∧
      p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ dminus)) < 0 := by
  classical
  obtain ⟨R, hRnodup, hRcard, hroots⟩ :=
    roots_eq_pair_add_real8 q hmon hnat hsep hz hzim hone
  have hRroot : ∀ r ∈ R, q.eval r = 0 := root_of_mem_R8 hmon hroots
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
  set F0 : ℝ[X] := polyOfVec8 (Lcomb8 q P₀) with hF0
  have hF0deg : F0.natDegree ≤ 7 := by rw [hF0]; exact polyOfVec8_natDegree_le _
  have hF0ne : F0 ≠ 0 := by
    rw [hF0]
    exact polyOfVec8_ne_zero (fun h => hP₀ne (Lcomb8_injective q h))
  have hvecF0 : vecOf8 F0 = Lcomb8 q P₀ := by rw [hF0, vecOf8_polyOfVec8]
  set S : ℝ := (R.map (fun r => (F0.eval r) ^ 2)).sum with hS
  set u : ℂ := (F0.map (algebraMap ℝ ℂ)).eval z with hu
  set α : ℝ := u.re with hα
  set γ : ℝ := u.im with hγ
  have htrF0sq : Matrix.trace ((aeval (companionN (n := 8) q) F0) ^ 2) = 0 := by
    have h1 : qform (Hmat8 q) (vecOf8 F0) = 0 := by
      rw [hvecF0, qform_Gram8_Lcomb8 q P₀, hQ₀]
    rw [qform_Hmat8_eq_hermiteForm8, hermiteForm8_eq_trace_sq,
      polyOfVec8_vecOf8 hF0deg] at h1
    exact h1
  have hsplit2 := ofReal_trace_mul_eq_sum8 q F0 F0 hmon hnat hsep hroots
  have hzero : algebraMap ℝ ℂ
      (Matrix.trace ((aeval (companionN (n := 8) q) F0)
        * (aeval (companionN (n := 8) q) F0))) = 0 := by
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
    exists_direction_of_value8 (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup
      hx1mem omegaC_add_conj omegaC_mul_conj
  obtain ⟨d1c, b1c, hd1c, hp1c, hb1c, hbl1c⟩ :=
    exists_direction_of_value8 (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup
      hx1mem homega1c homega2c
  obtain ⟨d2w, b2w, hd2w, hp2w, hb2w, hbl2w⟩ :=
    exists_direction_of_value8 (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup
      hx2mem omegaC_add_conj omegaC_mul_conj
  obtain ⟨d2c, b2c, hd2c, hp2c, hb2c, hbl2c⟩ :=
    exists_direction_of_value8 (P₀ := P₀) hmon hnat hsep hz hzim hone hroots hRroot hRnodup
      hx2mem homega1c homega2c
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
  have mk : ∀ (d : Fin 7 → ℝ) (b : ℝ), qform (Gram8 q) d = 0 →
      p3vec8 q (Lcomb8 q d) = 3 → bilin (Gram8 q) P₀ d = b →
      p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ d)) = -24 * b ^ 3 := by
    intro d b hd hp hb
    rw [p3vec_Lcomb_stereo_of_qform_zero8 q hd, hb, hp]
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
        refine eq_zero_of_vanishes_on_roots8 hnat hsep hF0deg ?_
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

-- Theorem: a real root `β` of a monic separable octic `q` with P-constructible coefficients
-- and exactly one non-real conjugate pair `{z, z̄}` is P-constructible.
set_option maxHeartbeats 1000000 in
-- the final `ring`/`nlinarith` steps expand `stereoN` and `p3vec8` over eight coordinates, so
-- the default heartbeat budget is not enough for this proof.
theorem root_Pconstructible_of_one_conjugate_pair8 {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β := by
  classical
  -- Steps 1-2: a P-constructible point `P₀` on the cone.
  obtain ⟨P₀, hP₀P, hQ₀, hP₀ne⟩ :=
    exists_cone_point8 q hmon hnat hsep hq hz hzim
  -- Step 3: a sign change of the stereographic cubic on the cone.
  obtain ⟨dplus, dminus, hdplus, hdminus⟩ :=
    exists_sign_change8 hmon hnat hsep hz hzim hone hQ₀ hP₀ne
  -- Step 4: rationalise the two witnesses.
  obtain ⟨rdplus, hrdplus⟩ :=
    exists_rat_vec_pos 7 (continuous_Phi8 q P₀) (x := dplus) hdplus
  obtain ⟨rdminus, hrdminus⟩ := exists_rat_vec_pos 7 (continuous_Phi8 q P₀).neg
    (x := dminus) (by linarith : 0 < -p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ dminus)))
  set dp : Fin 7 → ℝ := fun i => (rdplus i : ℝ) with hdp
  set dm : Fin 7 → ℝ := fun i => (rdminus i : ℝ) with hdm
  have hdpP : ∀ i, PConstructible (dp i) := fun i => rat_Pconstructible (rdplus i)
  have hdmP : ∀ i, PConstructible (dm i) := fun i => rat_Pconstructible (rdminus i)
  have hPhidp : 0 < p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ dp)) := hrdplus
  have hPhidm : p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ dm)) < 0 := by simpa using hrdminus
  -- Step 5: the sextic along the line `dp + m • (dm - dp)`.
  set δ : Fin 7 → ℝ := dm - dp with hδ
  have hδP : ∀ i, PConstructible (δ i) := by
    intro i; rw [hδ]; exact PConstructible.sub (hdmP i) (hdpP i)
  obtain ⟨Ψ, hΨc, hΨdeg, hΨeval⟩ := exists_sextic_along_line8 q hq hP₀P hdpP hδP
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
  set xstar : Fin 7 → ℝ := dp + mstar • δ with hxstar
  have hxstarP : ∀ i, PConstructible (xstar i) := by
    intro i
    simp only [hxstar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.add (hdpP i) (PConstructible.mul hmstarP (hδP i))
  set vstar : Fin 7 → ℝ := stereoN (Gram8 q) P₀ xstar with hvstar
  have hvstarP : ∀ i, PConstructible (vstar i) := stereoN_Pconstructible q hq hP₀P hxstarP
  have hQvstar : qform (Gram8 q) vstar = 0 := qform_stereoN_eq_zero (Gram8_symm q) hQ₀ xstar
  have hphistar0 : p3vec8 q (Lcomb8 q vstar) = 0 := by
    have h := hΨeval mstar
    rw [← hxstar, ← hvstar] at h
    exact h.symm.trans hmstar_root
  -- Step 6: non-degeneracy of `vstar`.
  have hnotpar : ¬ ∃ c : ℝ, xstar = c • P₀ := by
    rintro ⟨c, hc⟩
    set Phiδ : ℝ := p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ δ)) with hPhiδ
    have hxstar_eq : dp + mstar • δ = c • P₀ := by rw [← hc, hxstar]
    have hdp_eq : dp = c • P₀ - mstar • δ := by rw [← hxstar_eq, add_sub_cancel_right]
    have hPsi_eq : ∀ m : ℝ, Ψ.eval m = (m - mstar) ^ 6 * Phiδ := by
      intro m
      rw [hΨeval m]
      have hx : dp + m • δ = c • P₀ + (m - mstar) • δ := by rw [hdp_eq]; module
      rw [hx, stereoN_smul_add_smul (A := Gram8 q) (Gram8_symm q) hQ₀ c (m - mstar) δ,
        Lcomb8_smul, p3vec8_smul, ← hPhiδ]
      ring
    have h0 : Ψ.eval 0 = mstar ^ 6 * Phiδ := by rw [hPsi_eq 0]; ring
    have h1 : Ψ.eval 1 = (1 - mstar) ^ 6 * Phiδ := hPsi_eq 1
    have hA : 0 < mstar ^ 6 := pow_pos hmstar_pos 6
    have hB : 0 < (1 - mstar) ^ 6 := pow_pos (by linarith) 6
    nlinarith [hΨ0, hΨ1, h0, h1, hA, hB]
  have hvstar_ne : vstar ≠ 0 := by
    intro hv
    have hsub : qform (Gram8 q) xstar • P₀
        - (2 * bilin (Gram8 q) P₀ xstar) • xstar = 0 := by
      rw [← hv, hvstar]; rfl
    by_cases hb : bilin (Gram8 q) P₀ xstar = 0
    · have hQx : qform (Gram8 q) xstar = 0 := by
        rw [hb] at hsub
        simp only [mul_zero, zero_smul, sub_zero] at hsub
        exact (smul_eq_zero.mp hsub).resolve_right hP₀ne
      have hb' : bilin (Gram8 q) xstar P₀ = 0 := by
        rw [← bilin_comm (Gram8_symm q) P₀ xstar]; exact hb
      exact hnotpar
        (isotropic_plane_trivial8 hmon hnat hsep hz hzim hone xstar P₀ hQx hQ₀ hb' hP₀ne)
    · by_cases hQx : qform (Gram8 q) xstar = 0
      · have hx0 : xstar = 0 := by
          rw [hQx, zero_smul, zero_sub] at hsub
          rw [neg_eq_zero] at hsub
          exact (smul_eq_zero.mp hsub).resolve_left (mul_ne_zero two_ne_zero hb)
        exact hnotpar ⟨0, by rw [hx0, zero_smul]⟩
      · have hx : xstar
            = ((2 * bilin (Gram8 q) P₀ xstar)⁻¹ * qform (Gram8 q) xstar) • P₀ := by
          have hrel : qform (Gram8 q) xstar • P₀
              = (2 * bilin (Gram8 q) P₀ xstar) • xstar := sub_eq_zero.mp hsub
          have h2b : (2 * bilin (Gram8 q) P₀ xstar) ≠ 0 := mul_ne_zero two_ne_zero hb
          have h := congrArg (fun v : Fin 7 → ℝ =>
            ((2 * bilin (Gram8 q) P₀ xstar))⁻¹ • v) hrel
          rw [smul_smul, smul_smul, inv_mul_cancel₀ h2b, one_smul] at h
          exact h.symm
        exact hnotpar ⟨_, hx⟩
  -- Step 7: the Tschirnhaus polynomial and the tail.
  set φ : ℝ[X] := polyOfVec8 (Lcomb8 q vstar) with hφ
  have hLne : Lcomb8 q vstar ≠ 0 := fun h => hvstar_ne (Lcomb8_injective q h)
  refine root_Pconstructible_of_tschirnhaus8 (φ := φ) hmon hnat hsep hq ?_ ?_ ?_ ?_ ?_ ?_
    hβ
  · exact polyOfVec8_coeff_Pconstructible _ (Lcomb8_Pconstructible q hq hvstarP)
  · exact polyOfVec8_natDegree_le _
  · rw [hφ]; exact polyOfVec8_ne_zero hLne
  · rw [hφ, ← p1vec8_eq_trace q (Lcomb8 q vstar)]; exact p1vec8_Lcomb8 q vstar
  · rw [hφ, ← hermiteForm8_eq_trace_sq q (Lcomb8 q vstar),
      ← qform_Hmat8_eq_hermiteForm8, qform_Gram8_Lcomb8 q vstar]
    exact hQvstar
  · rw [hφ]
    change p3vec8 q (Lcomb8 q vstar) = 0
    exact hphistar0

end

end Pconstructible
