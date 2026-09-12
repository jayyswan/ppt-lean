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
import Pptc.DegreeSevenOnePair
import Mathlib.Data.Multiset.Filter

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### F1. The root decomposition of a septic with one conjugate pair

For a monic separable real septic `q` whose only non-real roots are `z` and `z̄`, the
complex roots split as `z`, `z̄`, and the images of five distinct real roots.  The real
roots are collected as a `Multiset ℝ` by filtering the complex roots on `im = 0` and
reading off `.re`. -/

-- Theorem: under `hsep` and `hone`, the roots of `q` over `ℂ` are `z`, `z̄` and the five
-- real roots, which form a nodup `Multiset ℝ` of cardinality five.
theorem roots_eq_pair_add_real {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z) :
    ∃ R : Multiset ℝ, R.Nodup ∧ R.card = 5 ∧
      (q.map (algebraMap ℝ ℂ)).roots
        = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)) := by
  classical
  set qC : ℂ[X] := q.map (algebraMap ℝ ℂ) with hqC
  have hqCne : qC ≠ 0 := by rw [hqC]; exact (hmon.map _).ne_zero
  have hnodup : qC.roots.Nodup := by
    rw [hqC]; exact Polynomial.nodup_roots (hsep.map)
  have hcard : qC.roots.card = 7 := by
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
  have hcardR : R.card = 5 := by
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
