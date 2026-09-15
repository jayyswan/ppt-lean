import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

set_option linter.style.openClassical false

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 2 * x ^ 2 - 6 * y ^ 2 = 0 := by decide

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 2 * x ^ 2 - 10 * y ^ 2 = 0 := by decide

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 6 * x ^ 2 - 2 * y ^ 2 = 0 := by decide

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 6 * x ^ 2 - 6 * y ^ 2 = 0 := by decide

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 10 * x ^ 2 - 2 * y ^ 2 = 0 := by decide

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 10 * x ^ 2 - 14 * y ^ 2 = 0 := by decide

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 14 * x ^ 2 - 10 * y ^ 2 = 0 := by decide

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 14 * x ^ 2 - 14 * y ^ 2 = 0 := by decide

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 3 * x ^ 2 - 2 * y ^ 2 = 0 := by decide

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 5 * x ^ 2 - 14 * y ^ 2 = 0 := by decide

example : ¬ ∃ z x y : ZMod 16, (IsUnit z ∨ IsUnit x ∨ IsUnit y) ∧
    z ^ 2 - 7 * x ^ 2 - 14 * y ^ 2 = 0 := by decide
