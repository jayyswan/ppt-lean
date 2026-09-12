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
import Pptc.S1Roots

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### The cubic certificate for the one-conjugate-pair septic

Given a monic separable real septic `q` with a single non-real conjugate pair `{z, z̄}` and a
prescribed complex value `c` with `c + c̄ = -1`, `c c̄ = 1`, we build a real polynomial `P` of
degree at most six whose values at `z`, `z̄` are `c`, `c̄`, which equals `1` at the chosen real
root `x` and vanishes at every other real root of `q`.  Because the non-real values sum to
`c^k + c̄^k` and the real ones contribute `1` for the root `x` and `0` elsewhere, the first
three trace power sums of `P(companion7 q)` are `0`, `0`, `3`.

The construction is the Lagrange base `L = (q'(x))⁻¹ · (q /ₘ (X - C x))`, normalised to `1`
at `x` and `0` at the other roots, corrected at `z` by `exists_poly_value_at_root`. -/

-- Theorem: for a monic separable septic `q` with one non-real conjugate pair `{z, z̄}` and a
-- complex `c` with `c + c̄ = -1`, `c c̄ = 1`, there is a real polynomial `P` of degree at most
-- six attaining `c`, `c̄` at `z`, `z̄`, equal to `1` at the real root `x`, vanishing at the
-- other real roots, and whose first three trace power sums at `companion7 q` are `0`, `0`, `3`.
theorem exists_lagrange_value {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {x : ℝ} (hx : q.eval x = 0) (hxz : (x : ℂ) ≠ z) (hxz' : (x : ℂ) ≠ starRingEnd ℂ z)
    {c : ℂ} (hc1 : c + starRingEnd ℂ c = -1) (hc2 : c * starRingEnd ℂ c = 1) :
    ∃ X : ℝ[X], X.natDegree ≤ 6 ∧
      (X.map (algebraMap ℝ ℂ)).eval z = c ∧
      (X.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = starRingEnd ℂ c ∧
      X.eval x = 1 ∧
      (∀ r : ℝ, q.eval r = 0 → r ≠ x → X.eval r = 0) ∧
      Matrix.trace (aeval (companion7 q) X) = 0 ∧
      Matrix.trace ((aeval (companion7 q) X) ^ 2) = 0 ∧
      Matrix.trace ((aeval (companion7 q) X) ^ 3) = 3 := by
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
  have hLdeg : L.natDegree ≤ 6 := by
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
    exists_poly_value_at_root q hmon hnat hsep hz hzim (c - (L.map (algebraMap ℝ ℂ)).eval z)
  set P : ℝ[X] := L + A with hP
  have hPdeg : P.natDegree ≤ 6 := by
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
    roots_eq_pair_add_real hmon hnat hsep hz hzim hone
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
  have ht1 : Matrix.trace (aeval (companion7 q) P) = 0 := by
    have h := companion7_trace_pow_aeval q P hmon hnat hsep 1
    rw [hsum 1 (by norm_num)] at h
    rw [pow_one] at h
    refine (algebraMap ℝ ℂ).injective ?_
    rw [h, map_zero]
    linear_combination hc1
  have ht2 : Matrix.trace ((aeval (companion7 q) P) ^ 2) = 0 := by
    have h := companion7_trace_pow_aeval q P hmon hnat hsep 2
    rw [hsum 2 (by norm_num)] at h
    refine (algebraMap ℝ ℂ).injective ?_
    rw [h, map_zero]
    linear_combination (c + starRingEnd ℂ c - 1) * hc1 - 2 * hc2
  have ht3 : Matrix.trace ((aeval (companion7 q) P) ^ 3) = 3 := by
    have h := companion7_trace_pow_aeval q P hmon hnat hsep 3
    rw [hsum 3 (by norm_num)] at h
    have h3 : (algebraMap ℝ ℂ (3 : ℝ)) = (3 : ℂ) := by norm_num
    refine (algebraMap ℝ ℂ).injective ?_
    rw [h, h3]
    linear_combination ((c + starRingEnd ℂ c + 1) ^ 2
        - 3 * (c + starRingEnd ℂ c + 1) - 3 * (c * starRingEnd ℂ c - 1)) * hc1
      + 3 * hc2
  exact ⟨P, hPdeg, hPz, hPzbar, hPx, hPother, ht1, ht2, ht3⟩

end

end Pconstructible
