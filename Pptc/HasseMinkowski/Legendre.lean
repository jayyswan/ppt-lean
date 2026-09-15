import Pptc.HasseMinkowski.HilbertSymbol.Norm
import Pptc.HasseMinkowski.HilbertSymbol.Padic
import Mathlib.Tactic

/-!
# WP1 1.1 — norm transfer for the Hilbert symbol

The Hilbert symbol `(a, b)_k` depends on `b` only through its class in `kˣ / kˣ²`, but in the
form used later (the descent in the proof of quadratic reciprocity) the input is not a square
multiple of `b` but a *norm* from `k(√a)`: we are handed `t` with `t ^ 2 - a = b * b'`.

Geometrically, `t + √a` has norm `t ^ 2 - a = b * b'` in `k(√a)`, so if `b` is a norm then so is
`b'` (divide the norm identity by `b`), and conversely. Since a nonzero nonsquare `a` satisfies
`(b, a)_k = 1` exactly when `b` is a norm from `k(√a)`, the two symbols agree.
-/

set_option linter.style.openClassical false

namespace Pptc.HasseMinkowski

open Classical

/-- If `t ^ 2 - a = b * b'` with `b` and `b'` nonzero, then `(a, b)_k = (a, b')_k`: the two
second arguments differ by the norm of `t + √a` in `k(√a)`, and being a norm from `k(√a)` is
invariant under multiplication by a square class, in particular under `b ↦ (t² - a) / b`. -/
-- Theorem: if `t ^ 2 - a = b * b'` with `b`, `b'` nonzero, then `(a,b)_k = (a,b')_k`.
theorem hilbertSym_eq_of_sq_sub_eq_mul {k : Type*} [Field k] [Invertible (2 : k)]
    {a b b' t : k} (hb : b ≠ 0) (hb' : b' ≠ 0) (h : t ^ 2 - a = b * b') :
    hilbertSym a b = hilbertSym a b' := by
  -- If `b` is a norm from `k(√a)` then so is `b'`, and vice versa.
  have aux : ∀ c c' : k, c ≠ 0 → c' ≠ 0 → t ^ 2 - a = c * c' →
      (∃ u : QuadraticAlgebra k a 0, c = u.norm) →
      ∃ u : QuadraticAlgebra k a 0, c' = u.norm := by
    intro c c' hc hc' hcc' ⟨u, hu⟩
    refine ⟨algebraMap k (QuadraticAlgebra k a 0) c⁻¹ * (⟨t, 1⟩ * star u), ?_⟩
    have hw : (⟨t, 1⟩ : QuadraticAlgebra k a 0).norm = c * c' := by
      simp [QuadraticAlgebra.norm_def]
      linear_combination hcc'
    simp only [map_mul, QuadraticAlgebra.norm_algebraMap, QuadraticAlgebra.norm_star, hw, ← hu]
    field_simp
  by_cases ha : a = 0
  · rw [ha]
    simp [hilbertSym_zero_left]
  · by_cases hsq : IsSquare a
    · -- `a` is a nonzero square, so both symbols are `1`.
      rcases hsq with ⟨s, hs⟩
      have h1 : hilbertSym a b = 1 := by
        refine hilbertSym_eq_one_of_sol ha hb ⟨s, 1, 0, by simp, ?_⟩
        rw [hs]
        ring
      have h2 : hilbertSym a b' = 1 := by
        refine hilbertSym_eq_one_of_sol ha hb' ⟨s, 1, 0, by simp, ?_⟩
        rw [hs]
        ring
      rw [h1, h2]
    · -- Main case: `a` is a nonzero nonsquare; use the norm characterization.
      rw [hilbertSym_comm a b, hilbertSym_comm a b']
      have hiff1 := hilbertSym_eq_one_iff_isNorm (a := b) (b := a) hb ha hsq
      have hiff2 := hilbertSym_eq_one_iff_isNorm (a := b') (b := a) hb' ha hsq
      have key : (∃ u : QuadraticAlgebra k a 0, b = u.norm) ↔
          (∃ u : QuadraticAlgebra k a 0, b' = u.norm) :=
        ⟨aux b b' hb hb' h, aux b' b hb' hb (h.trans (mul_comm b b'))⟩
      have hiff : (hilbertSym b a = 1) ↔ (hilbertSym b' a = 1) := by
        rw [hiff1, hiff2]
        exact key
      have hb0 : hilbertSym b a ≠ 0 := by
        intro hc
        rw [hilbertSym_eq_zero_iff] at hc
        exact hc.elim hb ha
      have hb'0 : hilbertSym b' a ≠ 0 := by
        intro hc
        rw [hilbertSym_eq_zero_iff] at hc
        exact hc.elim hb' ha
      rcases hilbertSym_eq_one_or b a with h1 | h0 | hm1
      · rcases hilbertSym_eq_one_or b' a with h2 | h02 | hm2
        · rw [h1, h2]
        · exact absurd h02 hb'0
        · exact absurd (hiff.mp h1) (by rw [hm2]; norm_num)
      · exact absurd h0 hb0
      · rcases hilbertSym_eq_one_or b' a with h2 | h02 | hm2
        · exact absurd (hiff.mpr h2) (by rw [hm1]; norm_num)
        · exact absurd h02 hb'0
        · rw [hm1, hm2]

end Pptc.HasseMinkowski
