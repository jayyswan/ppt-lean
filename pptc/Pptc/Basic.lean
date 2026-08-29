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

import Mathlib
import Pptc.Defs

/-! # Pptc.Basic

Basic theorems about P-constructible numbers.

`PConstructible` itself (and the mutually-inductive `PConstructibleCurve`) are
defined in `Pptc.Defs`; this module proves the numbers reachable through the base
arithmetic closure (`+ - * /` from `1`) alone are exactly the rationals.
-/

namespace Pconstructible

-- Theorem: All natural numbers are P-constructible.
theorem nat_Pconstructible (n : ℕ) : PConstructible (n : ℝ) := by
  induction n with
  | zero =>
    -- 0 = 1 - 1
    convert PConstructible.sub PConstructible.base_one PConstructible.base_one
    simp
  | succ n ih =>
    -- n + 1 = (n : ℝ) + 1
    convert PConstructible.add ih PConstructible.base_one
    push_cast
    rfl

-- Theorem: All integers are P-constructible.
theorem int_Pconstructible (z : ℤ) : PConstructible (z : ℝ) := by
  cases z with
  | ofNat n =>
    exact nat_Pconstructible n
  | negSucc n =>
    have h1 : PConstructible ((n + 1 : ℕ) : ℝ) := nat_Pconstructible (n + 1)
    have h0 : PConstructible (0 : ℝ) := by
      convert PConstructible.sub PConstructible.base_one PConstructible.base_one
      simp
    -- z = 0 - (n + 1)
    convert PConstructible.sub h0 h1
    push_cast
    ring

-- Theorem: All rational numbers are P-constructible.
theorem rat_Pconstructible (q : ℚ) : PConstructible (q : ℝ) := by
  -- Use q.num and q.den directly instead of structural 'cases q' to
  -- match Mathlib's cast definitions
  have h1 : PConstructible (q.num : ℝ) := int_Pconstructible q.num
  have h2 : PConstructible (q.den : ℝ) := nat_Pconstructible q.den
  convert PConstructible.div h1 h2
  exact Rat.cast_def q

-- Theorem: 420/69 is P-constructible.
theorem example_420_69_Pconstructible : PConstructible (420 / 69 : ℝ) := by
  have := rat_Pconstructible ((420 : ℚ) / 69)
  simp only [Rat.cast_div, Rat.cast_ofNat] at this
  convert this

-- Theorem: 0 is P-constructible.
theorem zero_Pconstructible : PConstructible (0 : ℝ) := by
  convert PConstructible.sub PConstructible.base_one PConstructible.base_one
  simp

-- Theorem: the square root of a P-constructible number is P-constructible.
theorem sqrt_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.sqrt x) := by
  by_cases h : x ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos h]
    exact zero_Pconstructible
  · push Not at h
    -- x > 0: construct `sqrt x` as the intersection of `y = t ^ (1/2)` with the
    -- vertical segment `t = x`, using `sqrt x ≤ (x + 1) / 2` (AM-GM) to guarantee
    -- the segment is tall enough to actually meet the curve.
    have hx1 : PConstructible (x + 1) := PConstructible.add hx PConstructible.base_one
    have hS := PConstructibleCurve.power_law 1 (1 / 2)
    have hT := PConstructibleCurve.rectangle x 0 0 (x + 1) hx zero_Pconstructible
      zero_Pconstructible hx1
    refine PConstructible.inter_y (x := x) hS hT ?_
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    push_cast
    constructor
    · rintro ⟨⟨ha, hb⟩, hor⟩
      have ha' : a = x := by
        rcases hor with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · linarith
        · rcases h3 with h3 | h3 <;> linarith
      subst ha'
      exact ⟨rfl, by rw [hb, one_mul, Real.sqrt_eq_rpow]⟩
    · rintro ⟨ha, hb⟩
      subst ha
      refine ⟨⟨h, by rw [hb, one_mul, Real.sqrt_eq_rpow]⟩, Or.inr ⟨?_, ?_, Or.inl (by ring)⟩⟩
      · nlinarith [Real.sq_sqrt h.le, Real.sqrt_nonneg a]
      · nlinarith [Real.sq_sqrt h.le, Real.sqrt_nonneg a, sq_nonneg (Real.sqrt a - 1)]

end Pconstructible
