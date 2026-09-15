import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

set_option linter.style.openClassical false

namespace Pptc.HasseMinkowski

open Classical

/-- The Hilbert symbol `(a,b)_k`, valued in `{0, ±1}`. -/
noncomputable def hilbertSym {k : Type*} [Field k] (a b : k) : ℤ :=
  if a = 0 ∨ b = 0 then 0
  else if ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    then 1 else -1

-- Theorem: the Hilbert symbol vanishes if either argument is zero.
theorem hilbertSym_zero_left {k : Type*} [Field k] (a : k) : hilbertSym 0 a = 0 := by
  simp [hilbertSym]

-- Theorem: the Hilbert symbol vanishes if either argument is zero.
theorem hilbertSym_zero_right {k : Type*} [Field k] (a : k) : hilbertSym a 0 = 0 := by
  simp [hilbertSym]

-- Theorem: `hilbertSym a b = 0` exactly when one of the arguments is zero.
theorem hilbertSym_eq_zero_iff {k : Type*} [Field k] (a b : k) :
    hilbertSym a b = 0 ↔ a = 0 ∨ b = 0 := by
  by_cases h : a = 0 ∨ b = 0
  · unfold hilbertSym
    rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · unfold hilbertSym
    rw [if_neg h]
    refine ⟨fun hz => ?_, fun hz => absurd hz h⟩
    by_cases hs : ∃ z x y : k,
        (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    · rw [if_pos hs] at hz
      norm_num at hz
    · rw [if_neg hs] at hz
      norm_num at hz

-- Theorem: the Hilbert symbol only takes values among `1`, `0`, `-1`.
theorem hilbertSym_eq_one_or {k : Type*} [Field k] (a b : k) :
    hilbertSym a b = 1 ∨ hilbertSym a b = 0 ∨ hilbertSym a b = -1 := by
  by_cases h : a = 0 ∨ b = 0
  · right; left
    unfold hilbertSym
    rw [if_pos h]
  · by_cases hs : ∃ z x y : k,
        (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    · left
      unfold hilbertSym
      rw [if_neg h, if_pos hs]
    · right; right
      unfold hilbertSym
      rw [if_neg h, if_neg hs]

-- Theorem: the Hilbert symbol only takes values among `-1`, `0`, `1`.
theorem hilbertSym_eq_neg_one_or {k : Type*} [Field k] (a b : k) :
    hilbertSym a b = -1 ∨ hilbertSym a b = 0 ∨ hilbertSym a b = 1 := by
  rcases hilbertSym_eq_one_or a b with h1 | h0 | hm1
  · exact Or.inr (Or.inr h1)
  · exact Or.inr (Or.inl h0)
  · exact Or.inl hm1

-- Theorem: the Hilbert symbol is symmetric in its two arguments.
theorem hilbertSym_comm {k : Type*} [Field k] (a b : k) :
    hilbertSym a b = hilbertSym b a := by
  by_cases h : a = 0 ∨ b = 0
  · rcases h with ha | hb
    · rw [ha, hilbertSym_zero_left, hilbertSym_zero_right]
    · rw [hb, hilbertSym_zero_right, hilbertSym_zero_left]
  · have h' : ¬ (b = 0 ∨ a = 0) := by tauto
    unfold hilbertSym
    rw [if_neg h, if_neg h']
    by_cases hs : ∃ z x y : k,
        (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    · have hs' : ∃ z x y : k,
          (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - b * x ^ 2 - a * y ^ 2 = 0 := by
        obtain ⟨z, x, y, hne, heq⟩ := hs
        refine ⟨z, y, x, ?_, ?_⟩
        · intro hc; exact hne (by simp_all)
        · rw [← heq]; ring
      rw [if_pos hs, if_pos hs']
    · have hs' : ¬ ∃ z x y : k,
          (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - b * x ^ 2 - a * y ^ 2 = 0 := by
        rintro ⟨z, x, y, hne, heq⟩
        exact hs ⟨z, y, x, by intro hc; exact hne (by simp_all), by rw [← heq]; ring⟩
      rw [if_neg hs, if_neg hs']

class HasBilinHilbertSym (k : Type*) [Field k] : Prop where
  mul_left_eq {a a' b : k} : hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b

namespace HasBilinHilbertSym

variable {k : Type*} [Field k] [HasBilinHilbertSym k]

-- Theorem: bilinearity in the second argument, derived from `mul_left_eq` and symmetry.
theorem mul_right_eq {a b b' : k} :
    hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b' := by
  rw [hilbertSym_comm a (b * b'), mul_left_eq, hilbertSym_comm b a, hilbertSym_comm b' a]

end HasBilinHilbertSym

end Pptc.HasseMinkowski
