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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! # Pptc.Basic

Basic theorems about P-constructible numbers.

`PConstructible` itself (and the mutually-inductive `PConstructibleCurve`) are
defined in `Pptc.Defs`; this module proves various facts about P-constructible numbers.
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
    -- x > 0. A zero-width rectangle is not a drawable shape, so the vertical segment
    -- `{x} × [-(x+1)/2, (x+1)/2]` is obtained instead as the *left edge* of a genuine
    -- rectangle — centre `(x + 1, 0)`, width `2`, height `x + 1`, so its left edge sits
    -- at `x` and its right edge at `x + 2` — isolated by cropping to `x`-coordinates at
    -- most `x`. That segment meets the curve `y = t ^ (1/2)` exactly at `(x, √x)`, using
    -- `√x ≤ (x + 1)/2` (AM-GM) to know the edge is tall enough to reach the curve.
    have h_two : PConstructible (2 : ℝ) := by
      convert PConstructible.add PConstructible.base_one PConstructible.base_one
      norm_num
    have hx1 : PConstructible (x + 1) := PConstructible.add hx PConstructible.base_one
    have hxm1 : PConstructible (x - 1) := PConstructible.sub hx PConstructible.base_one
    have hnx1 : PConstructible (-(x + 1)) := by
      convert PConstructible.sub zero_Pconstructible hx1
      ring
    have hS := PConstructibleCurve.power_law 1 (1 / 2)
    have hRect := PConstructibleCurve.rectangle (x + 1) 0 2 (x + 1) hx1 zero_Pconstructible
      h_two hx1 (by norm_num) (by linarith)
    have hT := PConstructibleCurve.restrict hRect (x - 1) x (-(x + 1)) (x + 1)
      hxm1 hx hnx1 hx1
    refine PConstructible.inter_y (x := x) hS hT ?_
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    push_cast
    constructor
    · rintro ⟨⟨ha, hb⟩, hor, hbox⟩
      obtain ⟨hb1, hb2, _, _⟩ := hbox
      have ha' : a = x := by
        rcases hor with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · linarith
        · rcases h3 with h3 | h3 <;> linarith
      subst ha'
      exact ⟨rfl, by rw [hb, one_mul, Real.sqrt_eq_rpow]⟩
    · rintro ⟨ha, hb⟩
      subst ha
      subst hb
      have hnn := Real.sqrt_nonneg a
      have hamgm : Real.sqrt a ≤ (a + 1) / 2 := by
        nlinarith [Real.sq_sqrt h.le, Real.sqrt_nonneg a, sq_nonneg (Real.sqrt a - 1)]
      refine ⟨⟨h, by rw [one_mul, Real.sqrt_eq_rpow]⟩,
        Or.inr ⟨by linarith, by linarith, Or.inl (by ring)⟩, ?_⟩
      exact ⟨by linarith, le_refl a, by linarith, by linarith⟩

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
def segmentParam (p q : ℝ × ℝ) : ℝ → ℝ × ℝ :=
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

/-! ### π is P-constructible

Measuring half of the unit circle. A *full* circle cannot be used directly: `θ ↦ (cos θ,
sin θ)` on `[0, 2π]` has `γ 0 = γ (2π)`, so it fails the injectivity side condition of
`PConstructible.arc_length`. The upper half circle avoids that, and its two endpoints
`(1, 0)` and `(-1, 0)` are P-constructible points, as required. Its length is `π`. -/

-- Theorem: 2 is P-constructible.
theorem two_Pconstructible : PConstructible (2 : ℝ) := by
  convert PConstructible.add PConstructible.base_one PConstructible.base_one
  norm_num

-- Theorem: -1 is P-constructible.
theorem neg_one_Pconstructible : PConstructible (-1 : ℝ) := by
  convert PConstructible.sub zero_Pconstructible PConstructible.base_one
  norm_num

/-- The unit circle, obtained from the `ellipse` constructor with centre `(0, 0)` and
bounding box `2 × 2`. -/
theorem unitCircle_PConstructibleCurve :
    PConstructibleCurve
      {p : ℝ × ℝ | ((p.1 - 0) / (2 / 2)) ^ 2 + ((p.2 - 0) / (2 / 2)) ^ 2 = 1} :=
  PConstructibleCurve.ellipse 0 0 2 2 zero_Pconstructible zero_Pconstructible
    two_Pconstructible two_Pconstructible (by norm_num) (by norm_num)

/-- The unit circle parametrized by angle. Restricted to `[0, π]` this traces the upper
half circle injectively. -/
noncomputable def circleParam : ℝ → ℝ × ℝ := fun θ => (Real.cos θ, Real.sin θ)

-- Theorem: the circle is traced at unit speed, so arc length agrees with angle.
theorem speed_circleParam (θ : ℝ) : speed circleParam θ = 1 := by
  have hc : HasDerivAt (fun s : ℝ => (circleParam s).1) (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hs : HasDerivAt (fun s : ℝ => (circleParam s).2) (Real.cos θ) θ := Real.hasDerivAt_sin θ
  rw [speed, hc.deriv, hs.deriv, neg_sq, Real.sin_sq_add_cos_sq, Real.sqrt_one]

-- Theorem: the upper half of the unit circle has arc length exactly π.
theorem arcLengthOf_circleParam : arcLengthOf circleParam 0 Real.pi = Real.pi := by
  rw [arcLengthOf]
  simp [speed_circleParam]

-- Theorem: π is P-constructible.
--
-- Note this is a genuinely new number: unlike `arcLength_segment_Pconstructible`, whose
-- conclusion was already reachable via `dist_Pconstructible`, π is transcendental and so
-- is *not* obtainable from the arithmetic closure or from `sqrt_Pconstructible`. It
-- enters only through `PConstructible.arc_length`.
theorem pi_Pconstructible : PConstructible Real.pi := by
  rw [← arcLengthOf_circleParam]
  refine PConstructible.arc_length unitCircle_PConstructibleCurve circleParam
    Real.pi_pos.le ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the half circle lies on the unit circle
    rintro p ⟨θ, _, rfl⟩
    simp only [Set.mem_ofPred_eq, circleParam, sub_zero]
    norm_num
  · -- injective on `[0, π]`, because `cos` is
    intro t₁ h₁ t₂ h₂ h
    exact Real.injOn_cos h₁ h₂ (congrArg Prod.fst h)
  · -- differentiable in each coordinate
    intro t _
    exact ⟨(Real.hasDerivAt_cos t).differentiableAt, (Real.hasDerivAt_sin t).differentiableAt⟩
  · -- unit speed, hence integrable
    rw [show speed circleParam = fun _ => (1 : ℝ) from funext speed_circleParam]
    exact intervalIntegrable_const
  · simpa [circleParam] using PConstructible.base_one
  · simpa [circleParam] using zero_Pconstructible
  · simpa [circleParam] using neg_one_Pconstructible
  · simpa [circleParam] using zero_Pconstructible

end Pconstructible
