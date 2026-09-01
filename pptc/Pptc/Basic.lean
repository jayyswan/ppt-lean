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
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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

/-! ### Cubic Bézier curves

Sanity checks on the `cubic_bezier` primitive. The drawn arc really does run from the
first control point to the last, and spacing the four control points evenly along a line
collapses the Bernstein cubic to the straight parametrization `segmentParam`.

The latter is what makes the primitive earn its place: it turns every segment between
P-constructible endpoints into a constructible curve. That was not available before —
`poly_graph` is a graph over `x`, so it cannot produce a vertical segment, and its
coefficients are rational rather than merely P-constructible. -/

-- Theorem: a cubic Bézier starts at its first control point.
theorem bezierParam_zero (p₁ p₂ p₃ p₄ : ℝ × ℝ) : bezierParam p₁ p₂ p₃ p₄ 0 = p₁ := by
  simp [bezierParam]

-- Theorem: ... and ends at its last.
theorem bezierParam_one (p₁ p₂ p₃ p₄ : ℝ × ℝ) : bezierParam p₁ p₂ p₃ p₄ 1 = p₄ := by
  simp [bezierParam]

-- Theorem: control points spaced evenly along the segment from `p` to `q` make the
-- Bézier the linear parametrization of that segment (the Bernstein weights reproduce
-- the identity, so the cubic terms cancel exactly).
theorem bezierParam_eq_segmentParam (p q : ℝ × ℝ) :
    bezierParam p (p.1 + (q.1 - p.1) / 3, p.2 + (q.2 - p.2) / 3)
        (p.1 + 2 * (q.1 - p.1) / 3, p.2 + 2 * (q.2 - p.2) / 3) q =
      segmentParam p q := by
  funext t
  simp only [bezierParam, segmentParam, Prod.mk.injEq]
  constructor <;> ring

-- Theorem: 3 is P-constructible.
theorem three_Pconstructible : PConstructible (3 : ℝ) := by
  convert PConstructible.add two_Pconstructible PConstructible.base_one
  norm_num

-- Theorem: the straight segment joining two P-constructible points is a constructible
-- curve.
theorem segment_PConstructibleCurve (p q : ℝ × ℝ)
    (hp1 : PConstructible p.1) (hp2 : PConstructible p.2)
    (hq1 : PConstructible q.1) (hq2 : PConstructible q.2) :
    PConstructibleCurve (segmentParam p q '' Set.Icc 0 1) := by
  rw [← bezierParam_eq_segmentParam]
  -- The interior control points are P-constructible, being built from the endpoints by
  -- `+ - * /` alone.
  have hmid : ∀ c : ℝ, PConstructible c → ∀ a b : ℝ, PConstructible a → PConstructible b →
      PConstructible (a + c * (b - a) / 3) := fun c hc a b ha hb =>
    PConstructible.add ha
      (PConstructible.div (PConstructible.mul hc (PConstructible.sub hb ha))
        three_Pconstructible)
  refine PConstructibleCurve.cubic_bezier _ _ _ _ hp1 hp2 ?_ ?_ ?_ ?_ hq1 hq2
  · simpa using hmid 1 PConstructible.base_one _ _ hp1 hq1
  · simpa using hmid 1 PConstructible.base_one _ _ hp2 hq2
  · exact hmid 2 two_Pconstructible _ _ hp1 hq1
  · exact hmid 2 two_Pconstructible _ _ hp2 hq2

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


/-! ### The natural logarithm

`ln a` comes out of the *arc length of a parabola*, which is the one place the geometry
supplies a logarithm. Arc length of `y = x ^ 2` over `[0, m]` is `∫₀^m √(1 + 4t²) dt`,
whose antiderivative carries an `arsinh`, and `arsinh` is a logarithm.

Choosing `m = (a² - 1) / (4a)` makes that logarithm exactly `ln a`, because

  `√(1 + 4m²) = (a² + 1) / (2a)`  and so  `2m + √(1 + 4m²) = a`.

The standard parabola is used rather than a scaled one, so `poly_graph` applies directly
and no `stretch` is needed; the scaling is absorbed into the endpoint `m` instead. -/

/-- The standard parabola `y = x ^ 2`, parametrized by abscissa. -/
def parabolaParam : ℝ → ℝ × ℝ := fun t => (t, t ^ 2)

theorem speed_parabolaParam (t : ℝ) :
    speed parabolaParam t = Real.sqrt (1 + 4 * t ^ 2) := by
  have h1 : deriv (fun s : ℝ => (parabolaParam s).1) t = 1 := by
    change deriv (fun s : ℝ => s) t = 1
    simp
  have h2 : deriv (fun s : ℝ => (parabolaParam s).2) t = 2 * t := by
    change deriv (fun s : ℝ => s ^ 2) t = 2 * t
    simp
  rw [speed, h1, h2]
  congr 1
  ring

/-- An antiderivative of `√(1 + 4t²)`. -/
noncomputable def parabolaAntideriv (t : ℝ) : ℝ :=
  t * Real.sqrt (1 + 4 * t ^ 2) / 2 + Real.arsinh (2 * t) / 4

theorem hasDerivAt_parabolaAntideriv (t : ℝ) :
    HasDerivAt parabolaAntideriv (Real.sqrt (1 + 4 * t ^ 2)) t := by
  have hu : (0 : ℝ) < 1 + 4 * t ^ 2 := by positivity
  have hspos : (0 : ℝ) < Real.sqrt (1 + 4 * t ^ 2) := Real.sqrt_pos.mpr hu
  have hs2 : Real.sqrt (1 + 4 * t ^ 2) ^ 2 = 1 + 4 * t ^ 2 := Real.sq_sqrt hu.le
  have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
  have hsq : HasDerivAt (fun s : ℝ => 1 + 4 * s ^ 2) (8 * t) t := by
    have h2 : HasDerivAt (fun s : ℝ => 1 + 4 * s ^ 2) (4 * (2 * t)) t :=
      (hp.const_mul (4 : ℝ)).const_add (1 : ℝ)
    have he : (4 : ℝ) * (2 * t) = 8 * t := by ring
    rwa [he] at h2
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (1 + 4 * s ^ 2))
      (8 * t / (2 * Real.sqrt (1 + 4 * t ^ 2))) t := hsq.sqrt hu.ne'
  have hterm1 : HasDerivAt (fun s : ℝ => s * Real.sqrt (1 + 4 * s ^ 2) / 2)
      ((1 * Real.sqrt (1 + 4 * t ^ 2) + t * (8 * t / (2 * Real.sqrt (1 + 4 * t ^ 2)))) / 2) t :=
    ((hasDerivAt_id t).mul hsqrt).div_const 2
  have h2t : (1 : ℝ) + (2 * t) ^ 2 = 1 + 4 * t ^ 2 := by ring
  have hterm2 : HasDerivAt (fun s : ℝ => Real.arsinh (2 * s) / 4)
      ((Real.sqrt (1 + 4 * t ^ 2))⁻¹ * (2 * 1) / 4) t := by
    have hc := (Real.hasDerivAt_arsinh (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
    rw [h2t] at hc
    exact hc.div_const 4
  have hval : (1 * Real.sqrt (1 + 4 * t ^ 2)
        + t * (8 * t / (2 * Real.sqrt (1 + 4 * t ^ 2)))) / 2
      + (Real.sqrt (1 + 4 * t ^ 2))⁻¹ * (2 * 1) / 4 = Real.sqrt (1 + 4 * t ^ 2) := by
    field_simp
    nlinarith [hs2, hspos]
  have hsum := hterm1.add hterm2
  rw [hval] at hsum
  exact hsum

theorem arcLengthOf_parabolaParam (u v : ℝ) :
    arcLengthOf parabolaParam u v = parabolaAntideriv v - parabolaAntideriv u := by
  rw [arcLengthOf]
  simp only [speed_parabolaParam]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_parabolaAntideriv x) ?_
  apply Continuous.intervalIntegrable
  fun_prop

/-- The standard parabola `y = x ^ 2`, as the graph of `X ^ 2` over `ℚ`. -/
theorem parabola_PConstructibleCurve :
    PConstructibleCurve
      {pt : ℝ × ℝ | pt.2 = Polynomial.aeval pt.1 ((Polynomial.X : Polynomial ℚ) ^ 2)} :=
  PConstructibleCurve.poly_graph (Polynomial.X ^ 2) (by simp)

theorem parabolaArc_Pconstructible {u v : ℝ} (hu : PConstructible u) (hv : PConstructible v)
    (huv : u ≤ v) : PConstructible (arcLengthOf parabolaParam u v) := by
  refine PConstructible.arc_length parabola_PConstructibleCurve parabolaParam huv
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro p ⟨t, _, rfl⟩
    simp [parabolaParam]
  · intro t₁ _ t₂ _ h
    exact congrArg Prod.fst h
  · intro t _
    refine ⟨?_, ?_⟩
    · change DifferentiableAt ℝ (fun s : ℝ => s) t
      exact differentiableAt_id
    · change DifferentiableAt ℝ (fun s : ℝ => s ^ 2) t
      exact differentiableAt_id.pow 2
  · rw [show speed parabolaParam = fun t => Real.sqrt (1 + 4 * t ^ 2) from
      funext speed_parabolaParam]
    apply Continuous.intervalIntegrable
    fun_prop
  · simpa [parabolaParam] using hu
  · simpa [parabolaParam] using sq_Pconstructible hu
  · simpa [parabolaParam] using hv
  · simpa [parabolaParam] using sq_Pconstructible hv

theorem parabolaAntideriv_Pconstructible {m : ℝ} (hm : PConstructible m) :
    PConstructible (parabolaAntideriv m) := by
  have h0 : parabolaAntideriv 0 = 0 := by simp [parabolaAntideriv]
  rcases le_total 0 m with hmm | hmm
  · have h := parabolaArc_Pconstructible zero_Pconstructible hm hmm
    rwa [arcLengthOf_parabolaParam, h0, sub_zero] at h
  · have h := parabolaArc_Pconstructible hm zero_Pconstructible hmm
    rw [arcLengthOf_parabolaParam, h0, zero_sub] at h
    have h2 := PConstructible.sub zero_Pconstructible h
    convert h2 using 1
    ring

theorem parabolaAntideriv_val {a : ℝ} (hapos : 0 < a) :
    parabolaAntideriv ((a ^ 2 - 1) / (4 * a))
      = (a ^ 4 - 1) / (16 * a ^ 2) + Real.log a / 4 := by
  have ha : a ≠ 0 := hapos.ne'
  set m := (a ^ 2 - 1) / (4 * a) with hmdef
  have hsv : Real.sqrt (1 + 4 * m ^ 2) = (a ^ 2 + 1) / (2 * a) := by
    rw [show (1 : ℝ) + 4 * m ^ 2 = ((a ^ 2 + 1) / (2 * a)) ^ 2 from by
      rw [hmdef]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have hars : Real.arsinh (2 * m) = Real.log a := by
    unfold Real.arsinh
    rw [show (1 : ℝ) + (2 * m) ^ 2 = 1 + 4 * m ^ 2 from by ring, hsv]
    congr 1
    rw [hmdef]
    field_simp
    ring
  rw [parabolaAntideriv, hsv, hars, hmdef]
  field_simp
  ring

-- Theorem: the natural logarithm of a positive P-constructible number is P-constructible.
theorem log_Pconstructible {a : ℝ} (ha : PConstructible a) (hapos : 0 < a) :
    PConstructible (Real.log a) := by
  have ha0 : a ≠ 0 := hapos.ne'
  have h4 : PConstructible (4 : ℝ) := by
    convert PConstructible.mul two_Pconstructible two_Pconstructible
    norm_num
  have ha2 : PConstructible (a ^ 2) := sq_Pconstructible ha
  have ha4 : PConstructible (a ^ 4) := by
    convert sq_Pconstructible ha2 using 1
    ring
  have hm : PConstructible ((a ^ 2 - 1) / (4 * a)) :=
    PConstructible.div (PConstructible.sub ha2 PConstructible.base_one)
      (PConstructible.mul h4 ha)
  have hG := parabolaAntideriv_Pconstructible hm
  rw [parabolaAntideriv_val hapos] at hG
  have hq : PConstructible ((a ^ 4 - 1) / (4 * a ^ 2)) :=
    PConstructible.div (PConstructible.sub ha4 PConstructible.base_one)
      (PConstructible.mul h4 ha2)
  have hkey : Real.log a
      = 4 * ((a ^ 4 - 1) / (16 * a ^ 2) + Real.log a / 4) - (a ^ 4 - 1) / (4 * a ^ 2) := by
    field_simp
    ring
  rw [hkey]
  exact PConstructible.sub (PConstructible.mul h4 hG) hq

-- e is P-constructible: ln is now available, so `e = 2 ^ (1 / ln 2)`.
theorem exp_one_Pconstructible : PConstructible (Real.exp 1) := by
  have hln2 : PConstructible (Real.log 2) := log_Pconstructible two_Pconstructible (by norm_num)
  have h : Real.exp 1 = (2 : ℝ) ^ (1 / Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    rw [mul_one_div, div_self (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))]
  rw [h]
  exact rpow_Pconstructible two_Pconstructible
    (PConstructible.div PConstructible.base_one hln2) (by norm_num)


/-! ### Sine and cosine

`PConstructibleCurve.arc_of_length` used in earnest. Instead of measuring an arc whose
endpoints are already known, lay out an arc of known *length* and ask where it ends. On
the unit circle that question is radian measure: the arc that starts at `(1, 0)` and runs
for length `x` ends at `(cos x, sin x)`.

Reaching that far endpoint takes a second curve, cutting the first there and nowhere else,
and the complementary arc supplies one — the arc that starts at `(-1, 0)` and runs
backwards for length `π - x` covers the remainder of the upper half circle, so the two
abut at the single point `(cos x, sin x)`. Both start at P-constructible points and have
P-constructible lengths, `x` and `π - x`, the latter because `π` is P-constructible.

That settles `0 ≤ x ≤ π`, and reduction mod `2π` removes the restriction. This is what
`arc_of_length` buys: every earlier constructor locates a point of a curve by cutting it
with another curve, never by measuring along it, so none of them can turn a length into
an angle. -/

/-- The unit circle traced from angle `u` at unit speed, in the direction `s = ±1`
(`s = 1` counterclockwise, `s = -1` clockwise). Unit speed is what makes the parameter
`t` double as arc length. -/
noncomputable def circleArcParam (u s : ℝ) : ℝ → ℝ × ℝ := fun t => circleParam (u + s * t)

theorem speed_circleArcParam {s : ℝ} (hs : s ^ 2 = 1) (u t : ℝ) :
    speed (circleArcParam u s) t = 1 := by
  have hlin : HasDerivAt (fun r : ℝ => u + s * r) s t := by
    simpa using ((hasDerivAt_id t).const_mul s).const_add u
  have hc : HasDerivAt (fun r : ℝ => (circleArcParam u s r).1)
      (-Real.sin (u + s * t) * s) t := hlin.cos
  have hsn : HasDerivAt (fun r : ℝ => (circleArcParam u s r).2)
      (Real.cos (u + s * t) * s) t := hlin.sin
  have hpyth : (-Real.sin (u + s * t) * s) ^ 2 + (Real.cos (u + s * t) * s) ^ 2 = 1 :=
    calc (-Real.sin (u + s * t) * s) ^ 2 + (Real.cos (u + s * t) * s) ^ 2
        = (Real.sin (u + s * t) ^ 2 + Real.cos (u + s * t) ^ 2) * s ^ 2 := by ring
      _ = 1 := by rw [Real.sin_sq_add_cos_sq, hs]; ring
  rw [speed, hc.deriv, hsn.deriv, hpyth, Real.sqrt_one]

-- Theorem: the parameter of `circleArcParam` is arc length, so an arc traced over
-- `[0, L]` has length exactly `L`.
theorem arcLengthOf_circleArcParam {s : ℝ} (hs : s ^ 2 = 1) (u L : ℝ) :
    arcLengthOf (circleArcParam u s) 0 L = L := by
  rw [arcLengthOf, show speed (circleArcParam u s) = fun _ => (1 : ℝ) from
    funext (speed_circleArcParam hs u)]
  simp

-- Theorem: two angles landing on the same point of the unit circle and differing by less
-- than a full turn are equal. This is the injectivity behind both the side condition of
-- `arc_of_length` and the "meet in exactly one point" hypothesis of `inter_x`/`inter_y`.
theorem angle_eq_of_cos_eq_of_sin_eq {θ₁ θ₂ : ℝ} (hlt : |θ₁ - θ₂| < 2 * Real.pi)
    (hc : Real.cos θ₁ = Real.cos θ₂) (hs : Real.sin θ₁ = Real.sin θ₂) : θ₁ = θ₂ := by
  have hone : Real.cos (θ₁ - θ₂) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.sin_sq_add_cos_sq θ₂]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hlt
  have := (Real.cos_eq_one_iff_of_lt_of_lt hlo hhi).mp hone
  linarith

-- Theorem: `s = ±1` is the only content of `s ^ 2 = 1`.
theorem eq_one_or_neg_one_of_sq_eq_one {s : ℝ} (hs : s ^ 2 = 1) : s = 1 ∨ s = -1 := by
  have h : (s - 1) * (s + 1) = 0 := by nlinarith [hs]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

-- Theorem: the arc of the unit circle that starts at a P-constructible point of it and
-- runs for a P-constructible length `L ≤ π` is a P-constructible curve.
--
-- The bound `L ≤ π` is only what the injectivity side condition of `arc_of_length` needs
-- (any `L < 2 * π` would do); it costs nothing below, where the arcs used are shorter
-- than a half turn anyway.
theorem circleArc_PConstructibleCurve {u s L : ℝ} (hs : s ^ 2 = 1)
    (hL : 0 ≤ L) (hLpi : L ≤ Real.pi) (hLc : PConstructible L)
    (hcu : PConstructible (Real.cos u)) (hsu : PConstructible (Real.sin u)) :
    PConstructibleCurve (circleArcParam u s '' Set.Icc 0 L) := by
  have hpi := Real.pi_pos
  have hlin : ∀ t : ℝ, HasDerivAt (fun r : ℝ => u + s * r) s t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul s).const_add u
  refine PConstructibleCurve.arc_of_length unitCircle_PConstructibleCurve (circleArcParam u s)
    hL ?_ ?_ ?_ ?_ ?_ ?_ hLc (arcLengthOf_circleArcParam hs u L)
  · -- the arc lies on the unit circle
    rintro p ⟨t, _, rfl⟩
    simp only [Set.mem_ofPred_eq, circleArcParam, circleParam, sub_zero]
    norm_num
  · -- injective on `[0, L]`: the angles swept differ by at most `L ≤ π < 2 * π`
    intro t₁ ht₁ t₂ ht₂ h
    obtain ⟨ht₁0, ht₁L⟩ := ht₁
    obtain ⟨ht₂0, ht₂L⟩ := ht₂
    have hc : Real.cos (u + s * t₁) = Real.cos (u + s * t₂) := congrArg Prod.fst h
    have hsn : Real.sin (u + s * t₁) = Real.sin (u + s * t₂) := congrArg Prod.snd h
    rcases eq_one_or_neg_one_of_sq_eq_one hs with rfl | rfl
    · have := angle_eq_of_cos_eq_of_sin_eq
        (by rw [abs_lt]; constructor <;> linarith) hc hsn
      linarith
    · have := angle_eq_of_cos_eq_of_sin_eq
        (by rw [abs_lt]; constructor <;> linarith) hc hsn
      linarith
  · -- differentiable in each coordinate
    intro t _
    exact ⟨(hlin t).cos.differentiableAt, (hlin t).sin.differentiableAt⟩
  · -- unit speed, hence integrable
    rw [show speed (circleArcParam u s) = fun _ => (1 : ℝ) from
      funext (speed_circleArcParam hs u)]
    exact intervalIntegrable_const
  · simpa [circleArcParam, circleParam] using hcu
  · simpa [circleArcParam, circleParam] using hsu

-- Theorem: `cos x` and `sin x` are P-constructible for P-constructible `x` in `[0, π]`.
--
-- The two arcs meet only at angle `x`: a point common to both is `(cos θ₁, sin θ₁)` for
-- some `θ₁ ≤ x` and `(cos θ₂, sin θ₂)` for some `θ₂ ≥ x`, and since the two angles differ
-- by less than a full turn they must be equal, which forces both to be `x`.
theorem cos_sin_Pconstructible_of_mem_Icc {x : ℝ} (hx : PConstructible x)
    (h0 : 0 ≤ x) (hpi : x ≤ Real.pi) :
    PConstructible (Real.cos x) ∧ PConstructible (Real.sin x) := by
  have hpipos := Real.pi_pos
  -- The arc from `(1, 0)` of length `x`, sweeping angles `[0, x]`.
  have hA : PConstructibleCurve (circleArcParam 0 1 '' Set.Icc 0 x) :=
    circleArc_PConstructibleCurve (by norm_num) h0 hpi hx
      (by simpa using PConstructible.base_one) (by simpa using zero_Pconstructible)
  -- The arc from `(-1, 0)` of length `π - x`, sweeping angles `[x, π]` backwards.
  have hB : PConstructibleCurve (circleArcParam Real.pi (-1) '' Set.Icc 0 (Real.pi - x)) :=
    circleArc_PConstructibleCurve (by norm_num) (by linarith) (by linarith)
      (PConstructible.sub pi_Pconstructible hx)
      (by simpa using neg_one_Pconstructible) (by simpa using zero_Pconstructible)
  have hinter : circleArcParam 0 1 '' Set.Icc 0 x ∩
      circleArcParam Real.pi (-1) '' Set.Icc 0 (Real.pi - x) = {(Real.cos x, Real.sin x)} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨t₁, ⟨ht₁0, ht₁x⟩, rfl⟩, t₂, ⟨ht₂0, ht₂x⟩, heq⟩
      have hc : Real.cos (Real.pi + -1 * t₂) = Real.cos (0 + 1 * t₁) := congrArg Prod.fst heq
      have hsn : Real.sin (Real.pi + -1 * t₂) = Real.sin (0 + 1 * t₁) := congrArg Prod.snd heq
      have hang : Real.pi + -1 * t₂ = 0 + 1 * t₁ :=
        angle_eq_of_cos_eq_of_sin_eq (by rw [abs_lt]; constructor <;> linarith) hc hsn
      have ht₁ : t₁ = x := by linarith
      subst ht₁
      simp [circleArcParam, circleParam]
    · rintro rfl
      exact ⟨⟨x, ⟨h0, le_rfl⟩, by simp [circleArcParam, circleParam]⟩,
        Real.pi - x, ⟨by linarith, le_rfl⟩, by simp [circleArcParam, circleParam]⟩
  exact ⟨PConstructible.inter_x hA hB hinter, PConstructible.inter_y hA hB hinter⟩

-- Theorem: every real number sits a whole number of turns away from one in `[0, 2π)`.
theorem exists_int_turns (x : ℝ) :
    ∃ n : ℤ, 0 ≤ x - n * (2 * Real.pi) ∧ x - n * (2 * Real.pi) < 2 * Real.pi := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  refine ⟨⌊x / (2 * Real.pi)⌋, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right (Int.floor_le (x / (2 * Real.pi))) h2pi.le
    rw [div_mul_cancel₀ _ h2pi.ne'] at h
    linarith
  · have h := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x / (2 * Real.pi))) h2pi
    rw [div_mul_cancel₀ _ h2pi.ne'] at h
    linarith

-- Theorem: `cos x` and `sin x` are P-constructible for every P-constructible `x`.
--
-- Reduction mod `2π`: the residue `r = x - n * (2π)` is P-constructible because `π` is,
-- and if it exceeds `π` the reflection `2π - r` brings it back into `[0, π]` at the cost
-- of a sign on the sine.
theorem cos_sin_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.cos x) ∧ PConstructible (Real.sin x) := by
  obtain ⟨n, hr0, hr2⟩ := exists_int_turns x
  have hrP : PConstructible (x - n * (2 * Real.pi)) :=
    PConstructible.sub hx (PConstructible.mul (int_Pconstructible n)
      (PConstructible.mul two_Pconstructible pi_Pconstructible))
  rw [← Real.cos_sub_int_mul_two_pi x n, ← Real.sin_sub_int_mul_two_pi x n]
  rcases le_total (x - n * (2 * Real.pi)) Real.pi with h | h
  · exact cos_sin_Pconstructible_of_mem_Icc hrP hr0 h
  · obtain ⟨hc, hsn⟩ := cos_sin_Pconstructible_of_mem_Icc
      (PConstructible.sub (PConstructible.mul two_Pconstructible pi_Pconstructible) hrP)
      (by linarith) (by linarith [Real.pi_pos])
    rw [Real.cos_two_pi_sub] at hc
    rw [Real.sin_two_pi_sub] at hsn
    refine ⟨hc, ?_⟩
    have h0 := PConstructible.sub zero_Pconstructible hsn
    convert h0 using 1
    ring

-- Theorem: the cosine of a P-constructible number is P-constructible.
theorem cos_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible (Real.cos x) :=
  (cos_sin_Pconstructible hx).1

-- Theorem: the sine of a P-constructible number is P-constructible.
theorem sin_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible (Real.sin x) :=
  (cos_sin_Pconstructible hx).2

-- Theorem: the tangent of a P-constructible number is P-constructible. No hypothesis is
-- needed at the poles: there `cos x = 0`, and Lean's division makes `tan x = 0`, which is
-- P-constructible anyway.
theorem tan_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible (Real.tan x) := by
  rw [Real.tan_eq_sin_div_cos]
  exact PConstructible.div (sin_Pconstructible hx) (cos_Pconstructible hx)
end Pconstructible
