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
-- Most of the mathematical content arrives transitively through `Pptc.Defs`.
import Pptc.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

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

-- Theorem: the square of a P-constructible number is P-constructible.
theorem sq_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible (x ^ 2) := by
  have := PConstructible.mul hx hx
  rwa [← sq] at this

-- Theorem: the distance between two P-constructible points is P-constructible.
-- This needs no appeal to `PConstructible.arc_length`; it is just the distance formula
-- fed through `sqrt_Pconstructible`.
theorem dist_Pconstructible {x₀ y₀ x₁ y₁ : ℝ}
    (hx₀ : PConstructible x₀) (hy₀ : PConstructible y₀)
    (hx₁ : PConstructible x₁) (hy₁ : PConstructible y₁) :
    PConstructible (Real.sqrt ((x₁ - x₀) ^ 2 + (y₁ - y₀) ^ 2)) :=
  sqrt_Pconstructible
    (PConstructible.add (sq_Pconstructible (PConstructible.sub hx₁ hx₀))
      (sq_Pconstructible (PConstructible.sub hy₁ hy₀)))

/-- The linear parametrization of the segment from `p` to `q`, traced over `[0, 1]`. -/
noncomputable def segmentParam (p q : ℝ × ℝ) : ℝ → ℝ × ℝ :=
  fun t => (p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2))

-- Theorem: a segment is traced at constant speed, namely the distance between its
-- endpoints.
theorem speed_segmentParam (p q : ℝ × ℝ) :
    speed (segmentParam p q) = fun _ => Real.sqrt ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by
  have hd : ∀ (c d : ℝ) (t : ℝ), HasDerivAt (fun s : ℝ => c + s * d) d t := by
    intro c d t
    simpa using ((hasDerivAt_id t).mul_const d).const_add c
  ext t
  change Real.sqrt (deriv (fun s : ℝ => p.1 + s * (q.1 - p.1)) t ^ 2 +
      deriv (fun s : ℝ => p.2 + s * (q.2 - p.2)) t ^ 2) = _
  rw [(hd p.1 (q.1 - p.1) t).deriv, (hd p.2 (q.2 - p.2) t).deriv]

-- Theorem: `arcLengthOf` really does compute length — on a straight segment it returns
-- exactly the distance formula. This is the sanity check that `speed` / `arcLengthOf`
-- were written correctly.
theorem arcLengthOf_segmentParam (p q : ℝ × ℝ) :
    arcLengthOf (segmentParam p q) 0 1 =
      Real.sqrt ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by
  rw [arcLengthOf, speed_segmentParam]
  simp

-- Theorem: a straight segment lying inside a constructible curve, with `PConstructible`
-- endpoints, has `PConstructible` arc length.
--
-- Note the conclusion is *identical* to that of `dist_Pconstructible` above, which is
-- proved without `PConstructible.arc_length`. That is the intended sanity check on the
-- new constructor: on straight segments it grants no number that was not already
-- constructible. It also exercises every side condition of the constructor, confirming
-- they are dischargeable in practice.
theorem arcLength_segment_Pconstructible {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (p q : ℝ × ℝ) (hne : p ≠ q)
    (hsub : segmentParam p q '' Set.Icc 0 1 ⊆ S)
    (hp1 : PConstructible p.1) (hp2 : PConstructible p.2)
    (hq1 : PConstructible q.1) (hq2 : PConstructible q.2) :
    PConstructible (Real.sqrt ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2)) := by
  rw [← arcLengthOf_segmentParam p q]
  -- `p ≠ q` means the segment is nondegenerate in at least one coordinate, which is what
  -- makes the parametrization injective.
  have hkey : q.1 - p.1 ≠ 0 ∨ q.2 - p.2 ≠ 0 := by
    rcases eq_or_ne (q.1 - p.1) 0 with h1 | h1
    · refine Or.inr fun h2 => hne ?_
      have e1 : p.1 = q.1 := by linarith
      have e2 : p.2 = q.2 := by linarith
      exact Prod.ext e1 e2
    · exact Or.inl h1
  refine PConstructible.arc_length hS _ zero_le_one hsub ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- injective on `[0, 1]`
    intro t₁ _ t₂ _ h
    have h1 : p.1 + t₁ * (q.1 - p.1) = p.1 + t₂ * (q.1 - p.1) := congrArg Prod.fst h
    have h2 : p.2 + t₁ * (q.2 - p.2) = p.2 + t₂ * (q.2 - p.2) := congrArg Prod.snd h
    rcases hkey with hk | hk
    · exact mul_right_cancel₀ hk (by linarith : t₁ * (q.1 - p.1) = t₂ * (q.1 - p.1))
    · exact mul_right_cancel₀ hk (by linarith : t₁ * (q.2 - p.2) = t₂ * (q.2 - p.2))
  · -- differentiable in each coordinate
    intro t _
    exact ⟨by fun_prop, by fun_prop⟩
  · -- the speed is constant, hence integrable
    rw [speed_segmentParam]
    exact intervalIntegrable_const
  · simpa [segmentParam] using hp1
  · simpa [segmentParam] using hp2
  · simpa [segmentParam] using hq1
  · simpa [segmentParam] using hq2

end Pconstructible
