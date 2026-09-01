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
import Mathlib.Analysis.SpecialFunctions.Log.Base
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

-- Theorem: 2 is P-constructible.
theorem two_Pconstructible : PConstructible (2 : ℝ) := by
  convert PConstructible.add PConstructible.base_one PConstructible.base_one
  norm_num

/-! ### Reading a coordinate off a curve

The two workhorses. If a vertical line at a P-constructible abscissa meets a
constructible curve in a single point, that point's ordinate is P-constructible — and
symmetrically for horizontal lines.

No bound on the coordinate is needed. Cutting the curve requires a segment long enough
to reach it, but by the Archimedean property some natural number exceeds the coordinate
in absolute value, and every natural number is P-constructible, so a big enough
rectangle always exists. Geometrically: "draw a rectangle large enough". This is what
frees the results below from having to supply explicit bounds. -/

-- Theorem: the ordinate of a single crossing with a vertical line is P-constructible.
theorem ordinate_Pconstructible {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {c y : ℝ} (hc : PConstructible c)
    (h : S ∩ {p : ℝ × ℝ | p.1 = c} = {(c, y)}) :
    PConstructible y := by
  obtain ⟨n, hn⟩ := exists_nat_gt |y|
  obtain ⟨hylo, hyhi⟩ := abs_lt.mp hn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (abs_nonneg y) hn
  have hnP : PConstructible ((n : ℝ)) := nat_Pconstructible n
  have hnegn : PConstructible (-(n : ℝ)) := by
    convert PConstructible.sub zero_Pconstructible hnP
    ring
  have hmem : ((c, y) : ℝ × ℝ) ∈ S := by
    have hx : ((c, y) : ℝ × ℝ) ∈ S ∩ {p : ℝ × ℝ | p.1 = c} := by
      rw [h]; exact rfl
    exact hx.1
  -- Rectangle of centre `(c + 1, 0)`, width `2`, height `2n`; its left edge is the
  -- segment `{c} × [-n, n]`, isolated by cropping to abscissae at most `c`.
  have hRect := PConstructibleCurve.rectangle (c + 1) 0 2 (2 * (n : ℝ))
    (PConstructible.add hc PConstructible.base_one) zero_Pconstructible
    two_Pconstructible (PConstructible.mul two_Pconstructible hnP)
    (by norm_num) (by linarith)
  have hT := PConstructibleCurve.restrict hRect (c - 1) c (-(n : ℝ)) (n : ℝ)
    (PConstructible.sub hc PConstructible.base_one) hc hnegn hnP
  refine PConstructible.inter_y (x := c) hS hT ?_
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hSmem, hR, hb1, hb2, hb3, hb4⟩
    have hu : u = c := by
      rcases hR with ⟨h1, _, _⟩ | ⟨_, _, h3⟩
      · linarith
      · rcases h3 with h3 | h3 <;> linarith
    have hpt : ((u, v) : ℝ × ℝ) ∈ S ∩ {p : ℝ × ℝ | p.1 = c} := ⟨hSmem, hu⟩
    rw [h] at hpt
    simpa using hpt
  · rintro ⟨rfl, rfl⟩
    exact ⟨hmem, Or.inr ⟨by linarith, by linarith, Or.inl (by ring)⟩,
      by linarith, le_rfl, by linarith, by linarith⟩

-- Theorem: the abscissa of a single crossing with a horizontal line is P-constructible.
theorem abscissa_Pconstructible {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {x c : ℝ} (hc : PConstructible c)
    (h : S ∩ {p : ℝ × ℝ | p.2 = c} = {(x, c)}) :
    PConstructible x := by
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  obtain ⟨hxlo, hxhi⟩ := abs_lt.mp hn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (abs_nonneg x) hn
  have hnP : PConstructible ((n : ℝ)) := nat_Pconstructible n
  have hnegn : PConstructible (-(n : ℝ)) := by
    convert PConstructible.sub zero_Pconstructible hnP
    ring
  have hmem : ((x, c) : ℝ × ℝ) ∈ S := by
    have hy : ((x, c) : ℝ × ℝ) ∈ S ∩ {p : ℝ × ℝ | p.2 = c} := by
      rw [h]; exact rfl
    exact hy.1
  -- Rectangle of centre `(0, c + 1)`, width `2n`, height `2`; its bottom edge is the
  -- segment `[-n, n] × {c}`, isolated by cropping to ordinates at most `c`.
  have hRect := PConstructibleCurve.rectangle 0 (c + 1) (2 * (n : ℝ)) 2
    zero_Pconstructible (PConstructible.add hc PConstructible.base_one)
    (PConstructible.mul two_Pconstructible hnP) two_Pconstructible
    (by linarith) (by norm_num)
  have hT := PConstructibleCurve.restrict hRect (-(n : ℝ)) (n : ℝ) (c - 1) c
    hnegn hnP (PConstructible.sub hc PConstructible.base_one) hc
  refine PConstructible.inter_x (y := c) hS hT ?_
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hSmem, hR, hb1, hb2, hb3, hb4⟩
    have hv : v = c := by
      rcases hR with ⟨_, _, h3⟩ | ⟨h1, _, _⟩
      · rcases h3 with h3 | h3 <;> linarith
      · linarith
    have hpt : ((u, v) : ℝ × ℝ) ∈ S ∩ {p : ℝ × ℝ | p.2 = c} := ⟨hSmem, hv⟩
    rw [h] at hpt
    simpa using hpt
  · rintro ⟨rfl, rfl⟩
    exact ⟨hmem, Or.inl ⟨by linarith, by linarith, Or.inl (by ring)⟩,
      by linarith, by linarith, by linarith, le_rfl⟩

-- Theorem: the square root of a P-constructible number is P-constructible.
theorem sqrt_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.sqrt x) := by
  by_cases h : x ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos h]
    exact zero_Pconstructible
  · push Not at h
    -- `√x` is just the ordinate of the curve `y = t ^ (1/2)` above `t = x`. No bound on
    -- `√x` is needed; `ordinate_Pconstructible` supplies a large enough rectangle.
    refine ordinate_Pconstructible (PConstructibleCurve.power_law 1 (1 / 2)) hx ?_
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    push_cast
    constructor
    · rintro ⟨⟨ha, hb⟩, hline⟩
      subst hline
      exact ⟨rfl, by rw [hb, one_mul, Real.sqrt_eq_rpow]⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨h, by rw [one_mul, Real.sqrt_eq_rpow]⟩, rfl⟩

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

/-! ### `logb 2` is P-constructible

Reading off the *other* coordinate of the exponential curve. The point of `y = 2 ^ x`
lying at height `a` sits at abscissa `logb 2 a`, so a horizontal line at height `a` cuts
the curve exactly there — which is precisely what `abscissa_Pconstructible` consumes. -/

-- Theorem: `logb 2 x` is P-constructible for positive P-constructible `x`.
theorem logb_two_Pconstructible {x : ℝ} (hx : PConstructible x) (hxpos : 0 < x) :
    PConstructible (Real.logb 2 x) := by
  refine abscissa_Pconstructible PConstructibleCurve.exp_two hx ?_
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hE, hline⟩
    subst hline
    exact ⟨((Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hxpos).mpr hE.symm).symm, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(Real.rpow_logb (by norm_num) (by norm_num) hxpos).symm, rfl⟩

/-! ### Exponentials and general powers

`rpow_two_Pconstructible` reads off the `y`-coordinate of `y = 2 ^ x` above a given
abscissa, and `rpow_Pconstructible` then gets every positive base from
`a ^ b = 2 ^ (b * logb 2 a)`. -/

-- Theorem: `2 ^ x` is P-constructible.
--
-- `2 ^ x` outgrows every polynomial in `x`, so there is no algebraic bound on it to
-- supply. None is needed: `ordinate_Pconstructible` gets its segment from the
-- Archimedean property rather than from a formula.
theorem rpow_two_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible ((2 : ℝ) ^ x) := by
  refine ordinate_Pconstructible PConstructibleCurve.exp_two hx ?_
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hE, hline⟩
    subst hline
    exact ⟨rfl, hE⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

-- Theorem: `a ^ b` is P-constructible for positive P-constructible `a` and
-- P-constructible `b`, since `a ^ b = 2 ^ (b * logb 2 a)`.
theorem rpow_Pconstructible {a b : ℝ} (ha : PConstructible a) (hb : PConstructible b)
    (hapos : 0 < a) : PConstructible (a ^ b) := by
  have key : (2 : ℝ) ^ (b * Real.logb 2 a) = a ^ b := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hapos]
  rw [← key]
  exact rpow_two_Pconstructible (PConstructible.mul hb (logb_two_Pconstructible ha hapos))

end Pconstructible
