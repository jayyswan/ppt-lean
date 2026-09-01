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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
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

-- Theorem: the negation of a P-constructible number is P-constructible. `PConstructible`
-- has no negation constructor, but `0 - x` serves and this saves spelling that out.
theorem neg_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible (-x) := by
  simpa using PConstructible.sub zero_Pconstructible hx

-- Theorem: the reciprocal of a P-constructible number is P-constructible. As for
-- `neg_Pconstructible`, this is just the corresponding closure constructor with `1` on
-- the left, restated in the form Mathlib's lemmas produce.
theorem inv_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible x⁻¹ := by
  simpa [one_div] using PConstructible.div PConstructible.base_one hx

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
  have hnegn : PConstructible (-(n : ℝ)) := neg_Pconstructible hnP
  have hmem : ((c, y) : ℝ × ℝ) ∈ S := (h.ge rfl).1
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
  have hnegn : PConstructible (-(n : ℝ)) := neg_Pconstructible hnP
  have hmem : ((x, c) : ℝ × ℝ) ∈ S := (h.ge rfl).1
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
    simpa [sub_ne_zero, ne_comm, Prod.ext_iff, not_and_or, or_iff_not_imp_left] using hne
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
theorem neg_one_Pconstructible : PConstructible (-1 : ℝ) :=
  neg_Pconstructible PConstructible.base_one

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

-- Theorem: `circleParam` traces the circle at unit speed, so the arc swept from angle `0`
-- to angle `L` has length exactly `L`; the upper half circle (`L = π`) is the case used
-- for `pi_Pconstructible`.
theorem arcLengthOf_circleParam (L : ℝ) : arcLengthOf circleParam 0 L = L := by
  rw [arcLengthOf]
  simp [speed_circleParam]

/-! ### The circular arc: `arccos` and `π`

The arc of the unit circle running from `(1, 0)` to `(x, √(1 - x²))` has length exactly
`arccos x`, and both of those endpoints are P-constructible as soon as `x` is — so
`PConstructible.arc_length` can measure it with no auxiliary curve. Taking `x = -1`
sweeps the entire upper half circle and so produces `π`. -/

-- Theorem: `arccos x` is P-constructible for P-constructible `x` in `[-1, 1]`.
--
-- The angle `arccos x` is at most `π`, which is exactly the range on which `cos` is
-- injective, so the arc traced over `[0, arccos x]` never doubles back and its integral
-- is a genuine length.
theorem arccos_Pconstructible_of_mem_Icc {x : ℝ} (hx : PConstructible x)
    (h₁ : -1 ≤ x) (h₂ : x ≤ 1) : PConstructible (Real.arccos x) := by
  rw [← arcLengthOf_circleParam (Real.arccos x)]
  refine PConstructible.arc_length unitCircle_PConstructibleCurve circleParam
    (Real.arccos_nonneg x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the arc lies on the unit circle
    rintro p ⟨θ, _, rfl⟩
    simp only [Set.mem_ofPred_eq, circleParam, sub_zero]
    norm_num
  · -- injective on `[0, arccos x] ⊆ [0, π]`, because `cos` is
    intro t₁ ht₁ t₂ ht₂ h
    exact Real.injOn_cos.mono (Set.Icc_subset_Icc le_rfl (Real.arccos_le_pi x))
      ht₁ ht₂ (congrArg Prod.fst h)
  · -- differentiable in each coordinate
    intro t _
    exact ⟨(Real.hasDerivAt_cos t).differentiableAt, (Real.hasDerivAt_sin t).differentiableAt⟩
  · -- unit speed, hence integrable
    rw [show speed circleParam = fun _ => (1 : ℝ) from funext speed_circleParam]
    exact intervalIntegrable_const
  · simpa [circleParam] using PConstructible.base_one
  · simpa [circleParam] using zero_Pconstructible
  · -- the far endpoint is `(x, √(1 - x²))`
    simpa [circleParam, Real.cos_arccos h₁ h₂] using hx
  · simpa [circleParam, Real.sin_arccos, pow_two] using
      sqrt_Pconstructible (PConstructible.sub PConstructible.base_one (PConstructible.mul hx hx))

-- Theorem: π is P-constructible.
--
-- Note this is a genuinely new number: unlike `arcLength_segment_Pconstructible`, whose
-- conclusion was already reachable via `dist_Pconstructible`, π is transcendental and so
-- is *not* obtainable from the arithmetic closure or from `sqrt_Pconstructible`. It
-- enters only through `PConstructible.arc_length`.
--
-- It is the case `x = -1` of the lemma above: the arc from `(1, 0)` round to `(-1, 0)`
-- is the whole upper half circle, so its length is `arccos (-1) = π`.
theorem pi_Pconstructible : PConstructible Real.pi := by
  rw [← Real.arccos_neg_one]
  exact arccos_Pconstructible_of_mem_Icc neg_one_Pconstructible (by norm_num) (by norm_num)

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
    have h2 := (hp.const_mul (4 : ℝ)).const_add (1 : ℝ)
    rwa [show (4 : ℝ) * (2 * t) = 8 * t from by ring] at h2
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
  rw [← hval]
  exact hterm1.add hterm2

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
    simpa using neg_Pconstructible h

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
    -- both signs of `s` run the same argument
    rcases eq_one_or_neg_one_of_sq_eq_one hs with rfl | rfl <;>
      have := angle_eq_of_cos_eq_of_sin_eq
        (by rw [abs_lt]; constructor <;> linarith) hc hsn <;>
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
    simpa using neg_Pconstructible hsn

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

/-! ### Inverse trigonometric functions

`arccos_Pconstructible_of_mem_Icc`, proved above alongside `π`, already does all of the
geometry; what is left here is bookkeeping. Note how much cheaper these are than `cos`
and `sin`: those needed `arc_of_length` to *lay out* an arc of known length, and then a
second curve to discover where it landed. Here both endpoints are known from the start
and only their separation along the circle is wanted, so `PConstructible.arc_length`
simply reads it off.

All three statements come out unconditional. Mathlib clamps the inverse functions outside
their natural domain — `arccos x` is `π` for `x ≤ -1` and `0` for `x ≥ 1` — and those
values are P-constructible too, so the bound `-1 ≤ x ≤ 1` is needed only by the geometric
core and not by anything built on it. -/

-- Theorem: the arccosine of a P-constructible number is P-constructible. No bound on `x`
-- is needed: outside `[-1, 1]` Mathlib's `arccos` is constantly `π` or `0`.
theorem arccos_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.arccos x) := by
  rcases le_total x (-1) with h | h₁
  · rw [Real.arccos_eq_pi.mpr h]
    exact pi_Pconstructible
  rcases le_total x 1 with h₂ | h₂
  · exact arccos_Pconstructible_of_mem_Icc hx h₁ h₂
  · rw [Real.arccos_eq_zero.mpr h₂]
    exact zero_Pconstructible

-- Theorem: the arcsine of a P-constructible number is P-constructible.
--
-- `arccos` is *defined* in Mathlib as `π / 2 - arcsin`, so this is the previous theorem
-- rearranged; the complementary angle costs only a subtraction and a halving.
theorem arcsin_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.arcsin x) := by
  have h := PConstructible.sub (PConstructible.div pi_Pconstructible two_Pconstructible)
    (arccos_Pconstructible hx)
  rwa [Real.arccos_eq_pi_div_two_sub_arcsin, sub_sub_cancel] at h

-- Theorem: the arctangent of a P-constructible number is P-constructible.
--
-- Via `arctan x = arcsin (x / √(1 + x²))`. Unlike `tan_Pconstructible` there are no poles
-- to worry about, and `1 + x²` is positive, so the square root is a genuine one.
theorem arctan_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.arctan x) := by
  rw [Real.arctan_eq_arcsin]
  refine arcsin_Pconstructible (PConstructible.div hx (sqrt_Pconstructible ?_))
  simpa [pow_two] using PConstructible.add PConstructible.base_one (PConstructible.mul hx hx)


/-! ### The incomplete elliptic integral of the second kind

`E(φ) = ∫₀^φ √(1 - c sin²θ) dθ` *is* an arc length of an ellipse, and at the right size
it is one on the nose. Trace the ellipse with semi-axes `1` and `b = √(1 - c)` by

  `γ θ = (sin θ, b cos θ)`,

so `θ = 0` is the top of the ellipse and `θ` increases towards the right. Its speed is

  `√(cos²θ + b² sin²θ) = √(cos²θ + (1 - c) sin²θ) = √(1 - c sin²θ)`,

which is the integrand, so the arc swept over `[0, φ]` has length exactly `E(φ)`.

Both endpoints of that arc are P-constructible points of the plane: the near one is
`(0, b)` and the far one is `(sin φ, b cos φ)`. That is where `sin_Pconstructible` and
`cos_Pconstructible` are spent, and it is all `PConstructible.arc_length` asks for — so
the integral is read straight off the plane, with no auxiliary curve.

A drawing program cannot name the parameter `φ`, and would instead cut the arc out with a
wedge at the centre of the ellipse of angle `arctan (tan φ / b)`, the polar angle at which
the parameter `φ` sits, after stretching the ellipse by `1 / b` to put a `1` on the other
semi-axis and dividing the measured length by that same factor afterwards. Both steps are
ways of *locating* the far endpoint; `arc_length` only requires that endpoint to be
P-constructible, which the sine and cosine theorems already supply. So the ellipse is used
here at exactly the size at which its arc length is `E(φ)`, and nothing is rescaled.

Mathlib does not define the elliptic integrals, so they are spelled out here.

Throughout, the elliptic integrals are indexed by the **parameter** `c`, the square of the
more familiar modulus `k`; `c < 1` is the standing hypothesis. Legendre's `E(φ, k)` is the
case `c = k²`, recorded as `ellipticE_sq_Pconstructible` at the end of the next section.
Allowing negative `c` is not idle generality: the reflection that carries the first-kind
integral past `φ = π/2` lands on the complementary parameter `-c / (1 - c)`, which is
negative whenever `c` is positive. -/

/-- The integrand of the elliptic integral of the second kind, `√(1 - c sin²θ)`. It is
also the reciprocal of the first-kind integrand, so the two share this definition. -/
noncomputable def ellipticEIntegrand (c θ : ℝ) : ℝ :=
  Real.sqrt (1 - c * Real.sin θ ^ 2)

/-- The incomplete elliptic integral of the second kind,
`E(φ) = ∫₀^φ √(1 - c sin²θ) dθ`, in terms of the parameter `c = k²`. -/
noncomputable def ellipticE (c φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, ellipticEIntegrand c θ

-- Theorem: at `c = 0` the ellipse is the unit circle and `E(φ) = φ`, the arc length of
-- the circle being its angle. A check that the definition is the right one.
theorem ellipticE_zero (φ : ℝ) : ellipticE 0 φ = φ := by
  simp [ellipticE, ellipticEIntegrand]

-- Theorem: for `c < 1` the integrand is strictly positive, so it is safe to invert.
-- Both signs of `c` need saying: `c sin²θ` is at most `c` when `c ≥ 0` and at most `0`
-- when `c ≤ 0`.
theorem one_sub_mul_sin_sq_pos {c : ℝ} (hc : c < 1) (θ : ℝ) : 0 < 1 - c * Real.sin θ ^ 2 := by
  rcases le_total c 0 with h | h
  · nlinarith [sq_nonneg (Real.sin θ)]
  · nlinarith [Real.sin_sq_le_one θ]

theorem ellipticEIntegrand_pos {c : ℝ} (hc : c < 1) (θ : ℝ) : 0 < ellipticEIntegrand c θ :=
  Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos hc θ)

theorem ellipticEIntegrand_sq {c : ℝ} (hc : c < 1) (θ : ℝ) :
    ellipticEIntegrand c θ ^ 2 = 1 - c * Real.sin θ ^ 2 :=
  Real.sq_sqrt (one_sub_mul_sin_sq_pos hc θ).le

theorem continuous_ellipticEIntegrand (c : ℝ) : Continuous (ellipticEIntegrand c) := by
  unfold ellipticEIntegrand
  fun_prop

theorem intervalIntegrable_ellipticEIntegrand (c a b : ℝ) :
    IntervalIntegrable (ellipticEIntegrand c) MeasureTheory.volume a b :=
  (continuous_ellipticEIntegrand c).intervalIntegrable a b

/-- The ellipse centred at the origin with horizontal semi-axis `1` and vertical
semi-axis `b`, from the `ellipse` constructor with bounding box `2 × 2b`. -/
theorem ellipse_PConstructibleCurve {b : ℝ} (hb : PConstructible b) (hbpos : 0 < b) :
    PConstructibleCurve
      {p : ℝ × ℝ | ((p.1 - 0) / (2 / 2)) ^ 2 + ((p.2 - 0) / (2 * b / 2)) ^ 2 = 1} :=
  PConstructibleCurve.ellipse 0 0 2 (2 * b) zero_Pconstructible zero_Pconstructible
    two_Pconstructible (PConstructible.mul two_Pconstructible hb) (by norm_num) (by positivity)

/-- The ellipse with semi-axes `1` and `b`, parametrized from the top. On `[0, π]` this
traces the right half of it injectively, since `cos` is injective there. -/
noncomputable def ellipseParam (b : ℝ) : ℝ → ℝ × ℝ := fun θ => (Real.sin θ, b * Real.cos θ)

-- Theorem: the ellipse is traced at speed `√(cos²θ + b² sin²θ)`.
theorem speed_ellipseParam (b θ : ℝ) :
    speed (ellipseParam b) θ = Real.sqrt (Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) := by
  have hc : HasDerivAt (fun s : ℝ => (ellipseParam b s).1) (Real.cos θ) θ :=
    Real.hasDerivAt_sin θ
  have hs : HasDerivAt (fun s : ℝ => (ellipseParam b s).2) (b * -Real.sin θ) θ :=
    (Real.hasDerivAt_cos θ).const_mul b
  rw [speed, hc.deriv, hs.deriv]
  congr 1
  ring

-- Theorem: with `b² = 1 - c` that speed is exactly the elliptic integrand.
theorem speed_ellipseParam_eq {c b : ℝ} (hb : b ^ 2 = 1 - c) (θ : ℝ) :
    speed (ellipseParam b) θ = ellipticEIntegrand c θ := by
  rw [speed_ellipseParam, hb, ellipticEIntegrand]
  congr 1
  linear_combination Real.sin_sq_add_cos_sq θ

-- Theorem: so the arc swept over `[0, φ]` has length `E(φ)`.
theorem arcLengthOf_ellipseParam {c b : ℝ} (hb : b ^ 2 = 1 - c) (φ : ℝ) :
    arcLengthOf (ellipseParam b) 0 φ = ellipticE c φ := by
  rw [arcLengthOf, ellipticE]
  simp only [speed_ellipseParam_eq hb]

-- Theorem: `E(φ)` is P-constructible for `0 ≤ φ ≤ π`.
--
-- The bound `φ ≤ π` is exactly what the injectivity side condition of
-- `PConstructible.arc_length` needs: past a half turn the parametrization comes back over
-- ellipse it has already covered, and the integral would stop being a length.
theorem ellipticE_Pconstructible_of_mem_Icc {c b φ : ℝ} (hb : b ^ 2 = 1 - c)
    (hbpos : 0 < b) (hbP : PConstructible b) (hφ : PConstructible φ)
    (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi) : PConstructible (ellipticE c φ) := by
  rw [← arcLengthOf_ellipseParam hb φ]
  refine PConstructible.arc_length (ellipse_PConstructibleCurve hbP hbpos) (ellipseParam b)
    h0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the arc lies on the ellipse
    rintro p ⟨θ, _, rfl⟩
    simp only [Set.mem_ofPred_eq, ellipseParam, sub_zero]
    field_simp
    linear_combination Real.sin_sq_add_cos_sq θ
  · -- injective on `[0, φ] ⊆ [0, π]`, because `cos` is
    intro t₁ ht₁ t₂ ht₂ h
    have hcos : Real.cos t₁ = Real.cos t₂ :=
      mul_left_cancel₀ hbpos.ne' (congrArg Prod.snd h)
    exact Real.injOn_cos (Set.Icc_subset_Icc le_rfl hpi ht₁)
      (Set.Icc_subset_Icc le_rfl hpi ht₂) hcos
  · -- differentiable in each coordinate
    intro t _
    exact ⟨(Real.hasDerivAt_sin t).differentiableAt,
      ((Real.hasDerivAt_cos t).const_mul b).differentiableAt⟩
  · -- the speed is continuous, hence integrable
    rw [show speed (ellipseParam b) = ellipticEIntegrand c from
      funext (speed_ellipseParam_eq hb)]
    exact intervalIntegrable_ellipticEIntegrand c 0 φ
  · simpa [ellipseParam] using zero_Pconstructible
  · simpa [ellipseParam] using hbP
  · simpa [ellipseParam] using sin_Pconstructible hφ
  · simpa [ellipseParam] using PConstructible.mul hbP (cos_Pconstructible hφ)

/-! Beyond a half turn the ellipse repeats, and so does `E`. Only `sin²θ` occurs in the
integrand, so it has period `π`, and `E(φ + nπ) = E(φ) + n · E(π)`: reducing `φ` modulo
`π` removes the restriction `0 ≤ φ ≤ π` above, exactly as reduction modulo `2π` did for
`cos` and `sin`. The same two facts serve the first-kind integral in the next section,
whose integrand is the reciprocal of this one and so has the same period. -/

-- Theorem: the second-kind integrand has period `π`, since `sin (θ + π) = -sin θ` is
-- squared.
theorem periodic_ellipticEIntegrand (c : ℝ) :
    Function.Periodic (ellipticEIntegrand c) Real.pi := fun θ => by
  simp [ellipticEIntegrand, Real.sin_add_pi]

-- Theorem: `E(φ + nπ) = E(φ) + n · E(π)`.
theorem ellipticE_add_int_mul_pi (c φ : ℝ) (n : ℤ) :
    ellipticE c (φ + n * Real.pi) = ellipticE c φ + n * ellipticE c Real.pi := by
  have hper := periodic_ellipticEIntegrand c
  have hint : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (ellipticEIntegrand c) MeasureTheory.volume t₁ t₂ :=
    fun t₁ t₂ => intervalIntegrable_ellipticEIntegrand c t₁ t₂
  -- the whole turns: `n` copies of one period, each of length `E(π)`
  have hA : (∫ θ in (0 : ℝ)..(n : ℝ) * Real.pi, ellipticEIntegrand c θ)
      = n * ellipticE c Real.pi := by
    have h := hper.intervalIntegral_add_zsmul_eq n 0 hint
    simpa [ellipticE, zsmul_eq_mul] using h
  -- the remainder: a translate of `[0, φ]` by a whole number of periods
  have hB : (∫ θ in ((n : ℝ) * Real.pi)..(φ + (n : ℝ) * Real.pi), ellipticEIntegrand c θ)
      = ellipticE c φ := by
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := φ)
      (ellipticEIntegrand c) ((n : ℝ) * Real.pi)
    have hshift : ∀ x : ℝ,
        ellipticEIntegrand c (x + (n : ℝ) * Real.pi) = ellipticEIntegrand c x :=
      fun x => hper.int_mul n x
    simp only [hshift, zero_add] at h
    rw [ellipticE, h]
  rw [ellipticE, ← intervalIntegral.integral_add_adjacent_intervals
    (b := (n : ℝ) * Real.pi) (hint 0 _) (hint _ _), hA, hB]
  ring

-- Theorem: every real number sits a whole number of half-turns away from one in `[0, π)`.
theorem exists_int_half_turns (x : ℝ) :
    ∃ n : ℤ, 0 ≤ x - n * Real.pi ∧ x - n * Real.pi ≤ Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨⌊x / Real.pi⌋, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right (Int.floor_le (x / Real.pi)) hpi.le
    rw [div_mul_cancel₀ _ hpi.ne'] at h
    linarith
  · have h := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x / Real.pi)) hpi
    rw [div_mul_cancel₀ _ hpi.ne'] at h
    linarith

-- Theorem: `E(φ)` is P-constructible for every P-constructible `φ` and every
-- P-constructible parameter `c < 1`.
--
-- `c < 1` is what makes the ellipse drawable: `b = √(1 - c)` has to be a positive length.
-- It is also exactly the range in which the integrand is real for every `θ`.
theorem ellipticE_Pconstructible {c φ : ℝ} (hc : PConstructible c) (hφ : PConstructible φ)
    (hc1 : c < 1) : PConstructible (ellipticE c φ) := by
  have hb : Real.sqrt (1 - c) ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  have hbpos : 0 < Real.sqrt (1 - c) := Real.sqrt_pos.mpr (by linarith)
  have hbP : PConstructible (Real.sqrt (1 - c)) :=
    sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hc)
  obtain ⟨n, h0, hpi⟩ := exists_int_half_turns φ
  have hrP : PConstructible (φ - n * Real.pi) :=
    PConstructible.sub hφ (PConstructible.mul (int_Pconstructible n) pi_Pconstructible)
  have hr := ellipticE_Pconstructible_of_mem_Icc hb hbpos hbP hrP h0 hpi
  have hEpi := ellipticE_Pconstructible_of_mem_Icc hb hbpos hbP pi_Pconstructible
    Real.pi_pos.le le_rfl
  have hkey : ellipticE c φ
      = ellipticE c (φ - n * Real.pi) + n * ellipticE c Real.pi := by
    have h := ellipticE_add_int_mul_pi c (φ - n * Real.pi) n
    rwa [sub_add_cancel] at h
  rw [hkey]
  exact PConstructible.add hr (PConstructible.mul (int_Pconstructible n) hEpi)


/-! ### The incomplete elliptic integral of the first kind

`F(φ) = ∫₀^φ dθ/√(1 - c sin²θ)` is not the arc length of an ellipse, or of any other
curve on the list: an arc length is `∫√(x'² + y'²)`, always a square *root* of something,
while `F` carries its radical in the denominator. What produces `F` is one arc length
together with an integration by parts.

Take `t = tan ψ`, which turns the integrand into

  `∫₀^φ dψ/√(1 - c sin²ψ) = ∫₀^{tan φ} dt/√((1 + t²)(1 + m² t²))`,  `m² = 1 - c`.

The point of that substitution is the shape of the new quartic. A cubic Bézier moves with
speed `√(x'(t)² + y'(t)²)` for quadratics `x'`, `y'`, so the quartics it can realise are
exactly the *sums of two squares* — the ones that are non-negative everywhere. Jacobi's
`(1 - t²)(1 - k² t²)` goes negative past `t = 1` and is therefore out of reach, but the
tangent form is positive definite, and Brahmagupta–Fibonacci exhibits the two squares:

  `(1² + t²)(1² + (mt)²) = (1 - m t²)² + (t + m t)²`.

So the cubic `t ↦ (t - m t³/3, (1 + m) t²/2)` — control points `(0,0)`, `(T/3, 0)`,
`(2T/3, (1+m)T²/6)`, `(T - mT³/3, (1+m)T²/2)`, all P-constructible — moves at exactly
speed `√((1+t²)(1+m²t²))`, and its arc length `J` is P-constructible.

Two integrations by parts then turn `J` back into `F`. Differentiating `t √P` gives

  `3√P - ((1 + m²)t² + 2)/√P`,

so `3J - T √P(T) = (1 + m²) I₂ + 2 F` where `I₂ = ∫₀^T t² dt/√P`; and differentiating
`tan ψ · Δ(ψ)`, with `Δ = √(1 - c sin²ψ)`, gives `m² tan²ψ/Δ + Δ`, so
`m² I₂ + E(φ) = tan φ · Δ(φ)`. Eliminating `I₂`:

  `F(φ) = (3J + (1 + m²)/m² · E(φ) - tan φ · Δ(φ) · (1/cos²φ + (1 + m²)/m²)) / 2`.

Everything on the right is P-constructible, so `F` is. At `c = 0` the formula collapses:
`J = T + T³/3`, `Δ = 1`, `E(φ) = φ`, and the right-hand side is `φ`, as it must be.

`tan φ` is what confines the construction to `|φ| < π/2`. Oddness of the integrand covers
negative `φ`, and the reflection `ψ ↦ π/2 + ψ` carries the rest of the line into range at
the cost of moving to the complementary parameter `-c/(1 - c)` — which is why the whole
development is indexed by a parameter allowed to be negative. -/

/-- The integrand of the elliptic integral of the first kind, `1/√(1 - c sin²θ)`. -/
noncomputable def ellipticFIntegrand (c θ : ℝ) : ℝ := (ellipticEIntegrand c θ)⁻¹

/-- The incomplete elliptic integral of the first kind,
`F(φ) = ∫₀^φ dθ/√(1 - c sin²θ)`, in terms of the parameter `c = k²`. -/
noncomputable def ellipticF (c φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, ellipticFIntegrand c θ

-- Theorem: at `c = 0` the circle again, and `F(φ) = φ`.
theorem ellipticF_zero (φ : ℝ) : ellipticF 0 φ = φ := by
  simp [ellipticF, ellipticFIntegrand, ellipticEIntegrand]

theorem ellipticFIntegrand_pos {c : ℝ} (hc : c < 1) (θ : ℝ) : 0 < ellipticFIntegrand c θ :=
  inv_pos.mpr (ellipticEIntegrand_pos hc θ)

theorem continuous_ellipticFIntegrand {c : ℝ} (hc : c < 1) :
    Continuous (ellipticFIntegrand c) :=
  (continuous_ellipticEIntegrand c).inv₀ fun θ => (ellipticEIntegrand_pos hc θ).ne'

theorem intervalIntegrable_ellipticFIntegrand {c : ℝ} (hc : c < 1) (a b : ℝ) :
    IntervalIntegrable (ellipticFIntegrand c) MeasureTheory.volume a b :=
  (continuous_ellipticFIntegrand hc).intervalIntegrable a b

/-! #### The Bézier cubic and its quartic -/

/-- The quartic `(1 + t²)(1 + m² t²)`, written as the sum of two squares that a cubic
Bézier can realise as its speed. -/
def firstKindQuartic (m t : ℝ) : ℝ := (1 - m * t ^ 2) ^ 2 + ((1 + m) * t) ^ 2

-- Theorem: Brahmagupta–Fibonacci — the two squares really do multiply out to the quartic.
theorem firstKindQuartic_eq (m t : ℝ) :
    firstKindQuartic m t = m ^ 2 * t ^ 4 + (1 + m ^ 2) * t ^ 2 + 1 := by
  unfold firstKindQuartic
  ring

theorem firstKindQuartic_pos (m t : ℝ) : 0 < firstKindQuartic m t := by
  rw [show firstKindQuartic m t = (1 + t ^ 2) * (1 + m ^ 2 * t ^ 2) from by
    rw [firstKindQuartic_eq]; ring]
  positivity

theorem sqrt_firstKindQuartic_pos (m t : ℝ) : 0 < Real.sqrt (firstKindQuartic m t) :=
  Real.sqrt_pos.mpr (firstKindQuartic_pos m t)

theorem sq_sqrt_firstKindQuartic (m t : ℝ) :
    Real.sqrt (firstKindQuartic m t) ^ 2 = firstKindQuartic m t :=
  Real.sq_sqrt (firstKindQuartic_pos m t).le

theorem continuous_sqrt_firstKindQuartic (m : ℝ) :
    Continuous fun t => Real.sqrt (firstKindQuartic m t) := by
  unfold firstKindQuartic
  fun_prop

-- Theorem: at `t = tan ψ` the quartic is `Δ(ψ)² / cos⁴ψ`, so its square root is
-- `Δ(ψ) / cos²ψ`. This is the bridge between the Bézier and the angle.
theorem sqrt_firstKindQuartic_tan {c m ψ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (hcos : Real.cos ψ ≠ 0) :
    Real.sqrt (firstKindQuartic m (Real.tan ψ))
      = ellipticEIntegrand c ψ / Real.cos ψ ^ 2 := by
  have hE := ellipticEIntegrand_pos hc ψ
  rw [show firstKindQuartic m (Real.tan ψ)
      = (ellipticEIntegrand c ψ / Real.cos ψ ^ 2) ^ 2 from ?_]
  · exact Real.sqrt_sq (by positivity)
  · rw [div_pow, ellipticEIntegrand_sq hc, firstKindQuartic_eq, Real.tan_eq_sin_div_cos]
    field_simp
    linear_combination (1 + m ^ 2 * Real.sin ψ ^ 2 + Real.cos ψ ^ 2) *
        Real.sin_sq_add_cos_sq ψ + Real.sin ψ ^ 2 * hm

/-- The cubic `t ↦ (t - m t³/3, (1+m) t²/2)`, whose coordinate derivatives `1 - m t²` and
`(1+m) t` are the two quadratics of `firstKindQuartic`. -/
noncomputable def firstKindCurve (m t : ℝ) : ℝ × ℝ := (t - m * t ^ 3 / 3, (1 + m) * t ^ 2 / 2)

-- Theorem: `s ↦ firstKindCurve m (T s)` is a cubic Bézier with these control points.
theorem bezierParam_firstKind (m T s : ℝ) :
    bezierParam (0, 0) (T / 3, 0) (2 * T / 3, (1 + m) * T ^ 2 / 6)
        (T - m * T ^ 3 / 3, (1 + m) * T ^ 2 / 2) s
      = firstKindCurve m (T * s) := by
  simp only [bezierParam, firstKindCurve, Prod.mk.injEq]
  constructor <;> ring

-- Theorem: that Bézier is a constructible curve.
theorem firstKindBezier_PConstructibleCurve {m T : ℝ} (hm : PConstructible m)
    (hT : PConstructible T) :
    PConstructibleCurve (bezierParam (0, 0) (T / 3, 0) (2 * T / 3, (1 + m) * T ^ 2 / 6)
      (T - m * T ^ 3 / 3, (1 + m) * T ^ 2 / 2) '' Set.Icc 0 1) := by
  have h3 : PConstructible (3 : ℝ) := three_Pconstructible
  have h6 : PConstructible (6 : ℝ) := by
    convert PConstructible.mul two_Pconstructible h3 using 1
    norm_num
  have hT2 : PConstructible (T ^ 2) := sq_Pconstructible hT
  have hT3 : PConstructible (T ^ 3) := by
    convert PConstructible.mul hT2 hT using 1
    ring
  have h1m : PConstructible (1 + m) := PConstructible.add PConstructible.base_one hm
  exact PConstructibleCurve.cubic_bezier _ _ _ _
    zero_Pconstructible zero_Pconstructible (PConstructible.div hT h3) zero_Pconstructible
    (PConstructible.div (PConstructible.mul two_Pconstructible hT) h3)
    (PConstructible.div (PConstructible.mul h1m hT2) h6)
    (PConstructible.sub hT (PConstructible.div (PConstructible.mul hm hT3) h3))
    (PConstructible.div (PConstructible.mul h1m hT2) two_Pconstructible)

/-- The same cubic, parametrized by the angle `ψ` through `t = tan ψ`. Its speed is
`Δ(ψ)/cos⁴ψ`, which is what makes its arc length an integral in `ψ`. -/
noncomputable def firstKindTanParam (m : ℝ) : ℝ → ℝ × ℝ :=
  fun ψ => firstKindCurve m (Real.tan ψ)

theorem hasDerivAt_firstKindTanParam_fst {m ψ : ℝ} (hcos : Real.cos ψ ≠ 0) :
    HasDerivAt (fun s : ℝ => (firstKindTanParam m s).1)
      ((1 - m * Real.tan ψ ^ 2) * (1 / Real.cos ψ ^ 2)) ψ := by
  have ht : HasDerivAt Real.tan (1 / Real.cos ψ ^ 2) ψ := Real.hasDerivAt_tan hcos
  have h : HasDerivAt (fun s : ℝ => Real.tan s - m * Real.tan s ^ 3 / 3)
      ((1 - m * Real.tan ψ ^ 2) * (1 / Real.cos ψ ^ 2)) ψ :=
    (ht.sub (((ht.pow 3).const_mul m).div_const 3)).congr_deriv (by push_cast; ring)
  exact h

theorem hasDerivAt_firstKindTanParam_snd {m ψ : ℝ} (hcos : Real.cos ψ ≠ 0) :
    HasDerivAt (fun s : ℝ => (firstKindTanParam m s).2)
      ((1 + m) * Real.tan ψ * (1 / Real.cos ψ ^ 2)) ψ := by
  have ht : HasDerivAt Real.tan (1 / Real.cos ψ ^ 2) ψ := Real.hasDerivAt_tan hcos
  have h : HasDerivAt (fun s : ℝ => (1 + m) * Real.tan s ^ 2 / 2)
      ((1 + m) * Real.tan ψ * (1 / Real.cos ψ ^ 2)) ψ :=
    (((ht.pow 2).const_mul (1 + m)).div_const 2).congr_deriv (by push_cast; ring)
  exact h

-- Theorem: the cubic, read in the angle `ψ`, moves at speed `Δ(ψ)/cos⁴ψ`.
theorem speed_firstKindTanParam {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1) {ψ : ℝ}
    (hcos : Real.cos ψ ≠ 0) :
    speed (firstKindTanParam m) ψ = ellipticEIntegrand c ψ / Real.cos ψ ^ 4 := by
  have hE := ellipticEIntegrand_pos hc ψ
  rw [speed, (hasDerivAt_firstKindTanParam_fst (m := m) hcos).deriv,
    (hasDerivAt_firstKindTanParam_snd (m := m) hcos).deriv]
  rw [show ((1 - m * Real.tan ψ ^ 2) * (1 / Real.cos ψ ^ 2)) ^ 2
        + ((1 + m) * Real.tan ψ * (1 / Real.cos ψ ^ 2)) ^ 2
      = (ellipticEIntegrand c ψ / Real.cos ψ ^ 4) ^ 2 from ?_]
  · exact Real.sqrt_sq (by positivity)
  · have h2 : firstKindQuartic m (Real.tan ψ)
        = (ellipticEIntegrand c ψ / Real.cos ψ ^ 2) ^ 2 := by
      rw [← sqrt_firstKindQuartic_tan hm hc hcos, sq_sqrt_firstKindQuartic]
    have hexp : ((1 - m * Real.tan ψ ^ 2) * (1 / Real.cos ψ ^ 2)) ^ 2
        + ((1 + m) * Real.tan ψ * (1 / Real.cos ψ ^ 2)) ^ 2
        = firstKindQuartic m (Real.tan ψ) * (1 / Real.cos ψ ^ 2) ^ 2 := by
      unfold firstKindQuartic
      ring
    rw [hexp, h2]
    field_simp

/-! #### The change of variables `t = tan ψ` -/

-- Theorem: on the interval between `0` and any `φ` with `|φ| < π/2`, the cosine is
-- positive — so `tan` is smooth there and the substitution below is legitimate.
theorem cos_pos_of_mem_uIcc {φ ψ : ℝ} (hφ : |φ| < Real.pi / 2)
    (hψ : ψ ∈ Set.uIcc (0 : ℝ) φ) : 0 < Real.cos ψ := by
  have hpi := Real.pi_pos
  rw [abs_lt] at hφ
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;>
    rcases Set.mem_uIcc.mp hψ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith

-- Theorem: `t = tan ψ` carries an integral over `[0, tan φ]` back to one over `[0, φ]`.
theorem integral_comp_tan {φ : ℝ} (hφ : |φ| < Real.pi / 2) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ ψ in (0 : ℝ)..φ, (1 / Real.cos ψ ^ 2) * g (Real.tan ψ))
      = ∫ t in (0 : ℝ)..Real.tan φ, g t := by
  have hd : ∀ ψ ∈ Set.uIcc (0 : ℝ) φ, HasDerivAt Real.tan (1 / Real.cos ψ ^ 2) ψ :=
    fun ψ hψ => Real.hasDerivAt_tan (cos_pos_of_mem_uIcc hφ hψ).ne'
  have hc' : ContinuousOn (fun ψ => 1 / Real.cos ψ ^ 2) (Set.uIcc (0 : ℝ) φ) := by
    refine ContinuousOn.div continuousOn_const (Continuous.continuousOn (by fun_prop))
      fun ψ hψ => pow_ne_zero 2 (cos_pos_of_mem_uIcc hφ hψ).ne'
  simpa [Real.tan_zero] using intervalIntegral.integral_deriv_smul_comp hd hc' hg

/-! #### The two integrations by parts -/

-- Theorem: differentiating `t √P` gives `3√P - ((1+m²)t² + 2)/√P`. This is the
-- integration by parts that converts the Bézier's arc length into first-kind integrals.
theorem hasDerivAt_mul_sqrt_firstKindQuartic (m t : ℝ) :
    HasDerivAt (fun s : ℝ => s * Real.sqrt (firstKindQuartic m s))
      (3 * Real.sqrt (firstKindQuartic m t)
        - ((1 + m ^ 2) * t ^ 2 + 2) / Real.sqrt (firstKindQuartic m t)) t := by
  have hpos := sqrt_firstKindQuartic_pos m t
  have hsq := sq_sqrt_firstKindQuartic m t
  have hP : HasDerivAt (firstKindQuartic m) (4 * m ^ 2 * t ^ 3 + 2 * (1 + m ^ 2) * t) t := by
    rw [show firstKindQuartic m = fun s : ℝ => m ^ 2 * s ^ 4 + (1 + m ^ 2) * s ^ 2 + 1 from
      funext (firstKindQuartic_eq m)]
    exact ((((hasDerivAt_pow 4 t).const_mul (m ^ 2)).add
      ((hasDerivAt_pow 2 t).const_mul (1 + m ^ 2))).add_const 1).congr_deriv (by push_cast; ring)
  have hs := hP.sqrt (firstKindQuartic_pos m t).ne'
  have hsq' : Real.sqrt (firstKindQuartic m t) ^ 2
      = m ^ 2 * t ^ 4 + (1 + m ^ 2) * t ^ 2 + 1 := by
    rw [hsq, firstKindQuartic_eq]
  refine ((hasDerivAt_id t).mul hs).congr_deriv ?_
  simp only [id_eq]
  field_simp
  linear_combination (-4 : ℝ) * hsq'

-- Theorem: differentiating `tan ψ · Δ(ψ)` gives `m² tan²ψ/Δ + Δ`. This is the
-- integration by parts that brings in the second-kind integral.
theorem hasDerivAt_tan_mul_ellipticEIntegrand {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    {ψ : ℝ} (hcos : Real.cos ψ ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.tan s * ellipticEIntegrand c s)
      (m ^ 2 * Real.tan ψ ^ 2 * ellipticFIntegrand c ψ + ellipticEIntegrand c ψ) ψ := by
  have hE := ellipticEIntegrand_pos hc ψ
  have hEsq := ellipticEIntegrand_sq hc ψ
  have ht : HasDerivAt Real.tan (1 / Real.cos ψ ^ 2) ψ := Real.hasDerivAt_tan hcos
  have hu : HasDerivAt (fun s : ℝ => 1 - c * Real.sin s ^ 2)
      (-(2 * c * Real.sin ψ * Real.cos ψ)) ψ :=
    ((((Real.hasDerivAt_sin ψ).pow 2).const_mul c).const_sub 1).congr_deriv
      (by push_cast; ring)
  have hD : HasDerivAt (ellipticEIntegrand c)
      (-(2 * c * Real.sin ψ * Real.cos ψ) / (2 * ellipticEIntegrand c ψ)) ψ :=
    hu.sqrt (one_sub_mul_sin_sq_pos hc ψ).ne'
  refine (ht.mul hD).congr_deriv ?_
  simp only [ellipticFIntegrand]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination (2 - 2 * Real.cos ψ ^ 2 - Real.sin ψ ^ 2) * hEsq
    - Real.sin ψ ^ 2 * hm
    + (ellipticEIntegrand c ψ ^ 2 + c * Real.sin ψ ^ 2 - 2) * Real.sin_sq_add_cos_sq ψ


/-! #### The arc length of the Bézier -/

-- Theorem: read in the angle, the Bézier's arc length is `∫₀^{tan φ} √P`.
theorem arcLengthOf_firstKindTanParam {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1) {φ : ℝ}
    (hφ : |φ| < Real.pi / 2) :
    arcLengthOf (firstKindTanParam m) 0 φ
      = ∫ t in (0 : ℝ)..Real.tan φ, Real.sqrt (firstKindQuartic m t) := by
  rw [arcLengthOf, ← integral_comp_tan hφ (continuous_sqrt_firstKindQuartic m)]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have hcos := cos_pos_of_mem_uIcc hφ hψ
  rw [speed_firstKindTanParam hm hc hcos.ne', sqrt_firstKindQuartic_tan hm hc hcos.ne']
  field_simp

-- Theorem: that arc length is P-constructible. This is the one place the geometry is
-- used; everything after it is calculus.
theorem arcLength_firstKind_Pconstructible {c m φ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (hmpos : 0 < m) (hmP : PConstructible m) (hφP : PConstructible φ)
    (h0 : 0 < φ) (hlt : φ < Real.pi / 2) :
    PConstructible (arcLengthOf (firstKindTanParam m) 0 φ) := by
  have hpi := Real.pi_pos
  have habs : |φ| < Real.pi / 2 := by rw [abs_lt]; constructor <;> linarith
  have hTpos : 0 < Real.tan φ := by
    have := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two le_rfl hlt h0
    rwa [Real.tan_zero] at this
  have hTP : PConstructible (Real.tan φ) := tan_Pconstructible hφP
  have hmemI : ∀ ψ ∈ Set.Icc (0 : ℝ) φ, 0 < Real.cos ψ := fun ψ hψ =>
    cos_pos_of_mem_uIcc habs (by rwa [Set.uIcc_of_le h0.le])
  have htan_nonneg : ∀ ψ ∈ Set.Icc (0 : ℝ) φ, 0 ≤ Real.tan ψ := fun ψ hψ => by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 (by linarith [hψ.2]))
      (hmemI ψ hψ).le
  refine PConstructible.arc_length (firstKindBezier_PConstructibleCurve hmP hTP)
    (firstKindTanParam m) h0.le ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the arc lies on the Bézier: the parameter `tan ψ / tan φ` lands in `[0, 1]`
    rintro p ⟨ψ, hψ, rfl⟩
    have htanle : Real.tan ψ ≤ Real.tan φ := by
      rcases eq_or_lt_of_le hψ.2 with rfl | h
      · exact le_rfl
      · exact (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hψ.1 hlt h).le
    refine ⟨Real.tan ψ / Real.tan φ,
      ⟨div_nonneg (htan_nonneg ψ hψ) hTpos.le, (div_le_one hTpos).mpr htanle⟩, ?_⟩
    rw [bezierParam_firstKind]
    simp only [firstKindTanParam]
    congr 1
    field_simp
  · -- injective: the second coordinate is increasing in `tan ψ`, and `tan` is injective
    intro ψ₁ h₁ ψ₂ h₂ heq
    have h1m : (1 : ℝ) + m ≠ 0 := by linarith
    have hsq : Real.tan ψ₁ ^ 2 = Real.tan ψ₂ ^ 2 := by
      have h : (1 + m) * Real.tan ψ₁ ^ 2 / 2 = (1 + m) * Real.tan ψ₂ ^ 2 / 2 :=
        congrArg Prod.snd heq
      have hz : (1 + m) * (Real.tan ψ₁ ^ 2 - Real.tan ψ₂ ^ 2) = 0 := by
        linear_combination 2 * h
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' h1m
      · linarith
    have htan : Real.tan ψ₁ = Real.tan ψ₂ := by
      have hz : (Real.tan ψ₁ - Real.tan ψ₂) * (Real.tan ψ₁ + Real.tan ψ₂) = 0 := by
        linear_combination hsq
      have hn₁ := htan_nonneg ψ₁ h₁
      have hn₂ := htan_nonneg ψ₂ h₂
      rcases mul_eq_zero.mp hz with h | h
      · linarith
      · have e₁ : Real.tan ψ₁ = 0 := by linarith
        have e₂ : Real.tan ψ₂ = 0 := by linarith
        rw [e₁, e₂]
    exact Real.injOn_tan ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
      ⟨by linarith [h₂.1], by linarith [h₂.2]⟩ htan
  · -- differentiable in each coordinate
    intro ψ hψ
    exact ⟨(hasDerivAt_firstKindTanParam_fst (hmemI ψ hψ).ne').differentiableAt,
      (hasDerivAt_firstKindTanParam_snd (hmemI ψ hψ).ne').differentiableAt⟩
  · -- the speed agrees on `[0, φ]` with a continuous function, hence is integrable
    refine ContinuousOn.intervalIntegrable (ContinuousOn.congr
      (f := fun ψ => ellipticEIntegrand c ψ / Real.cos ψ ^ 4) ?_ ?_)
    · exact ContinuousOn.div (continuous_ellipticEIntegrand c).continuousOn
        (Continuous.continuousOn (by fun_prop))
        fun ψ hψ => pow_ne_zero 4 (cos_pos_of_mem_uIcc habs hψ).ne'
    · exact fun ψ hψ => speed_firstKindTanParam hm hc (cos_pos_of_mem_uIcc habs hψ).ne'
  · simpa [firstKindTanParam, firstKindCurve] using zero_Pconstructible
  · simpa [firstKindTanParam, firstKindCurve] using zero_Pconstructible
  · have hT3 : PConstructible (Real.tan φ ^ 3) := by
      convert PConstructible.mul (sq_Pconstructible hTP) hTP using 1
      ring
    simpa [firstKindTanParam, firstKindCurve] using
      PConstructible.sub hTP (PConstructible.div (PConstructible.mul hmP hT3)
        three_Pconstructible)
  · simpa [firstKindTanParam, firstKindCurve] using
      PConstructible.div (PConstructible.mul
        (PConstructible.add PConstructible.base_one hmP) (sq_Pconstructible hTP))
        two_Pconstructible

/-! #### Eliminating the auxiliary integral

Two integrations by parts. The first, in `t`, converts the Bézier's arc length into the
two integrals `∫ dt/√P` and `∫ t² dt/√P`; the second, in `ψ`, identifies the latter with
the second-kind integral. Together they leave `F` alone on one side. -/

-- Theorem: `3J - T √P(T) = (1 + m²) I₂ + 2 I₀`, from differentiating `t √P`.
theorem firstKind_ibp_t (m T : ℝ) :
    3 * (∫ t in (0 : ℝ)..T, Real.sqrt (firstKindQuartic m t))
        - (1 + m ^ 2) * (∫ t in (0 : ℝ)..T, t ^ 2 * (Real.sqrt (firstKindQuartic m t))⁻¹)
        - 2 * ∫ t in (0 : ℝ)..T, (Real.sqrt (firstKindQuartic m t))⁻¹
      = T * Real.sqrt (firstKindQuartic m T) := by
  have hc1 : Continuous fun t => Real.sqrt (firstKindQuartic m t) :=
    continuous_sqrt_firstKindQuartic m
  have hc2 : Continuous fun t : ℝ => (Real.sqrt (firstKindQuartic m t))⁻¹ :=
    hc1.inv₀ fun t => (sqrt_firstKindQuartic_pos m t).ne'
  have hc3 : Continuous fun t : ℝ => t ^ 2 * (Real.sqrt (firstKindQuartic m t))⁻¹ :=
    (continuous_pow 2).mul hc2
  have hcD : Continuous fun t : ℝ => 3 * Real.sqrt (firstKindQuartic m t)
      - ((1 + m ^ 2) * t ^ 2 + 2) / Real.sqrt (firstKindQuartic m t) :=
    (hc1.const_mul 3).sub (Continuous.div (by fun_prop) hc1
      fun t => (sqrt_firstKindQuartic_pos m t).ne')
  have i1 : IntervalIntegrable _ MeasureTheory.volume 0 T := hc1.intervalIntegrable 0 T
  have i2 : IntervalIntegrable _ MeasureTheory.volume 0 T := hc2.intervalIntegrable 0 T
  have i3 : IntervalIntegrable _ MeasureTheory.volume 0 T := hc3.intervalIntegrable 0 T
  have iD : IntervalIntegrable _ MeasureTheory.volume 0 T := hcD.intervalIntegrable 0 T
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => s * Real.sqrt (firstKindQuartic m s))
    (fun t _ => hasDerivAt_mul_sqrt_firstKindQuartic m t) iD
  rw [zero_mul, sub_zero] at hkey
  have e1 : (∫ t in (0 : ℝ)..T, (3 * Real.sqrt (firstKindQuartic m t)
        - ((1 + m ^ 2) * t ^ 2 + 2) / Real.sqrt (firstKindQuartic m t)))
      = ∫ t in (0 : ℝ)..T, (3 * Real.sqrt (firstKindQuartic m t)
          - ((1 + m ^ 2) * (t ^ 2 * (Real.sqrt (firstKindQuartic m t))⁻¹)
            + 2 * (Real.sqrt (firstKindQuartic m t))⁻¹)) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have := (sqrt_firstKindQuartic_pos m t).ne'
    field_simp
  rw [e1, intervalIntegral.integral_sub (i1.const_mul 3)
      ((i3.const_mul (1 + m ^ 2)).add (i2.const_mul 2)),
    intervalIntegral.integral_add (i3.const_mul (1 + m ^ 2)) (i2.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hkey
  linarith [hkey]

-- Theorem: `m² I₂ + E(φ) = tan φ · Δ(φ)`, from differentiating `tan ψ · Δ(ψ)`.
theorem firstKind_ibp_angle {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1) {φ : ℝ}
    (hφ : |φ| < Real.pi / 2) :
    m ^ 2 * (∫ ψ in (0 : ℝ)..φ, Real.tan ψ ^ 2 * ellipticFIntegrand c ψ) + ellipticE c φ
      = Real.tan φ * ellipticEIntegrand c φ := by
  have htanC : ContinuousOn (fun ψ : ℝ => Real.tan ψ ^ 2) (Set.uIcc (0 : ℝ) φ) :=
    ContinuousOn.pow (fun ψ hψ =>
      (Real.continuousAt_tan.mpr (cos_pos_of_mem_uIcc hφ hψ).ne').continuousWithinAt) 2
  have i1 : IntervalIntegrable (fun ψ => Real.tan ψ ^ 2 * ellipticFIntegrand c ψ)
      MeasureTheory.volume 0 φ :=
    ContinuousOn.intervalIntegrable
      (htanC.mul (continuous_ellipticFIntegrand hc).continuousOn)
  have hcont : ContinuousOn
      (fun ψ => m ^ 2 * Real.tan ψ ^ 2 * ellipticFIntegrand c ψ + ellipticEIntegrand c ψ)
      (Set.uIcc (0 : ℝ) φ) :=
    ((continuousOn_const.mul htanC).mul
      (continuous_ellipticFIntegrand hc).continuousOn).add
      (continuous_ellipticEIntegrand c).continuousOn
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => Real.tan s * ellipticEIntegrand c s)
    (fun ψ hψ => hasDerivAt_tan_mul_ellipticEIntegrand hm hc
      (cos_pos_of_mem_uIcc hφ hψ).ne') hcont.intervalIntegrable
  rw [Real.tan_zero, zero_mul, sub_zero] at hkey
  have e1 : (∫ ψ in (0 : ℝ)..φ,
        (m ^ 2 * Real.tan ψ ^ 2 * ellipticFIntegrand c ψ + ellipticEIntegrand c ψ))
      = ∫ ψ in (0 : ℝ)..φ,
        (m ^ 2 * (Real.tan ψ ^ 2 * ellipticFIntegrand c ψ) + ellipticEIntegrand c ψ) := by
    refine intervalIntegral.integral_congr fun ψ _ => ?_
    ring
  rw [e1, intervalIntegral.integral_add (i1.const_mul (m ^ 2))
      (intervalIntegrable_ellipticEIntegrand c 0 φ),
    intervalIntegral.integral_const_mul] at hkey
  rw [ellipticE]
  linarith [hkey]

-- Theorem: the auxiliary integral in `t` is the auxiliary integral in `ψ`.
theorem integral_sq_div_sqrt_firstKindQuartic {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    {φ : ℝ} (hφ : |φ| < Real.pi / 2) :
    (∫ t in (0 : ℝ)..Real.tan φ, t ^ 2 * (Real.sqrt (firstKindQuartic m t))⁻¹)
      = ∫ ψ in (0 : ℝ)..φ, Real.tan ψ ^ 2 * ellipticFIntegrand c ψ := by
  have hg : Continuous fun t : ℝ => t ^ 2 * (Real.sqrt (firstKindQuartic m t))⁻¹ :=
    (continuous_pow 2).mul ((continuous_sqrt_firstKindQuartic m).inv₀
      fun t => (sqrt_firstKindQuartic_pos m t).ne')
  rw [← integral_comp_tan hφ hg]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have hcos := cos_pos_of_mem_uIcc hφ hψ
  have hE := ellipticEIntegrand_pos hc ψ
  rw [sqrt_firstKindQuartic_tan hm hc hcos.ne', ellipticFIntegrand]
  field_simp

-- Theorem: the first-kind integral in `ψ` is the reciprocal-quartic integral in `t`.
theorem integral_inv_sqrt_firstKindQuartic {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    {φ : ℝ} (hφ : |φ| < Real.pi / 2) :
    (∫ t in (0 : ℝ)..Real.tan φ, (Real.sqrt (firstKindQuartic m t))⁻¹) = ellipticF c φ := by
  have hg : Continuous fun t : ℝ => (Real.sqrt (firstKindQuartic m t))⁻¹ :=
    (continuous_sqrt_firstKindQuartic m).inv₀ fun t => (sqrt_firstKindQuartic_pos m t).ne'
  rw [← integral_comp_tan hφ hg, ellipticF]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have hcos := cos_pos_of_mem_uIcc hφ hψ
  have hE := ellipticEIntegrand_pos hc ψ
  rw [sqrt_firstKindQuartic_tan hm hc hcos.ne', ellipticFIntegrand]
  field_simp

/-! #### The construction -/

-- Theorem: `F(φ)` is P-constructible for `0 < φ < π/2`.
--
-- This is the construction itself. `J` is the Bézier's arc length, the only geometric
-- input; the two integrations by parts and a division by `m²` do the rest.
theorem ellipticF_Pconstructible_of_pos {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) (h0 : 0 < φ) (hlt : φ < Real.pi / 2) :
    PConstructible (ellipticF c φ) := by
  have hpi := Real.pi_pos
  have habs : |φ| < Real.pi / 2 := by rw [abs_lt]; constructor <;> linarith
  obtain ⟨m, hmpos, hm, hmP⟩ : ∃ m : ℝ, 0 < m ∧ m ^ 2 = 1 - c ∧ PConstructible m :=
    ⟨Real.sqrt (1 - c), Real.sqrt_pos.mpr (by linarith), Real.sq_sqrt (by linarith),
      sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hcP)⟩
  have hm0 : m ^ 2 ≠ 0 := by positivity
  have hTP : PConstructible (Real.tan φ) := tan_Pconstructible hφP
  -- the geometric input
  have hJ := arcLength_firstKind_Pconstructible hm hc hmpos hmP hφP h0 hlt
  rw [arcLengthOf_firstKindTanParam hm hc habs] at hJ
  -- the two integrations by parts, transported to the angle
  have ha := firstKind_ibp_t m (Real.tan φ)
  rw [integral_inv_sqrt_firstKindQuartic hm hc habs,
    integral_sq_div_sqrt_firstKindQuartic hm hc habs] at ha
  have hb := firstKind_ibp_angle hm hc habs
  -- solve for `F`
  have hkey : ellipticF c φ
      = (3 * (∫ t in (0 : ℝ)..Real.tan φ, Real.sqrt (firstKindQuartic m t))
          - (1 + m ^ 2) * ((Real.tan φ * ellipticEIntegrand c φ - ellipticE c φ) / m ^ 2)
          - Real.tan φ * Real.sqrt (firstKindQuartic m (Real.tan φ))) / 2 := by
    have hI2 : (∫ ψ in (0 : ℝ)..φ, Real.tan ψ ^ 2 * ellipticFIntegrand c ψ)
        = (Real.tan φ * ellipticEIntegrand c φ - ellipticE c φ) / m ^ 2 := by
      field_simp
      linarith [hb]
    rw [hI2] at ha
    linarith [ha]
  rw [hkey]
  -- and every piece of that is P-constructible
  have hEint : PConstructible (ellipticEIntegrand c φ) := by
    unfold ellipticEIntegrand
    exact sqrt_Pconstructible (PConstructible.sub PConstructible.base_one
      (PConstructible.mul hcP (sq_Pconstructible (sin_Pconstructible hφP))))
  have hQ : PConstructible (Real.sqrt (firstKindQuartic m (Real.tan φ))) := by
    refine sqrt_Pconstructible ?_
    unfold firstKindQuartic
    exact PConstructible.add
      (sq_Pconstructible (PConstructible.sub PConstructible.base_one
        (PConstructible.mul hmP (sq_Pconstructible hTP))))
      (sq_Pconstructible (PConstructible.mul
        (PConstructible.add PConstructible.base_one hmP) hTP))
  have hE := ellipticE_Pconstructible hcP hφP hc
  exact PConstructible.div
    (PConstructible.sub
      (PConstructible.sub (PConstructible.mul three_Pconstructible hJ)
        (PConstructible.mul (PConstructible.add PConstructible.base_one (sq_Pconstructible hmP))
          (PConstructible.div (PConstructible.sub (PConstructible.mul hTP hEint) hE)
            (sq_Pconstructible hmP))))
      (PConstructible.mul hTP hQ))
    two_Pconstructible

-- Theorem: `F` is odd, since its integrand is even.
theorem ellipticF_neg (c φ : ℝ) : ellipticF c (-φ) = -ellipticF c φ := by
  have heven : ∀ x : ℝ, ellipticFIntegrand c (-x) = ellipticFIntegrand c x := fun x => by
    simp [ellipticFIntegrand, ellipticEIntegrand]
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -φ)
    (ellipticFIntegrand c)
  simp only [heven, neg_neg, neg_zero] at h
  rw [ellipticF, h, intervalIntegral.integral_symm, ellipticF]

-- Theorem: `F(φ)` is P-constructible for every `|φ| < π/2`.
theorem ellipticF_Pconstructible_of_abs_lt {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) (hφ : |φ| < Real.pi / 2) :
    PConstructible (ellipticF c φ) := by
  rcases lt_trichotomy φ 0 with hneg | rfl | hpos
  · have h := ellipticF_Pconstructible_of_pos hcP (neg_Pconstructible hφP) hc
      (by linarith) (by rw [abs_lt] at hφ; linarith [hφ.1])
    rw [← neg_neg φ, ellipticF_neg]
    exact neg_Pconstructible h
  · simpa [ellipticF] using zero_Pconstructible
  · exact ellipticF_Pconstructible_of_pos hcP hφP hc hpos (by rw [abs_lt] at hφ; exact hφ.2)


/-! #### Past the quarter turn

`tan φ` runs out at `φ = π/2`, so the construction above stops there. Two symmetries carry
it over the whole line. The integrand has period `π`, exactly as in the second-kind case;
and reflecting in `π/2` sends

  `1 - c sin²(π/2 + w) = 1 - c cos²w = (1 - c)(1 - c' sin²w)`,  `c' = -c/(1 - c)`,

so a quarter turn past `π/2` is a quarter turn from `0` at the *complementary* parameter
`c'`, scaled by `1/√(1 - c)`. Since `c > 0` makes `c' < 0`, this is what forces the whole
development to be indexed by a parameter rather than a modulus `k`: there is no real `k`
with `k² = c'`. Note `c' < 1` whenever `c < 1`, so the complementary parameter stays
inside the hypothesis. -/

-- Theorem: the complementary parameter is again admissible.
theorem compl_param_lt_one {c : ℝ} (hc : c < 1) : -c / (1 - c) < 1 :=
  (div_lt_one (by linarith)).mpr (by linarith)

-- Theorem: reflecting the integrand in `π/2` moves to the complementary parameter.
theorem ellipticFIntegrand_pi_div_two_add {c : ℝ} (hc : c < 1) (w : ℝ) :
    ellipticFIntegrand c (Real.pi / 2 + w)
      = (Real.sqrt (1 - c))⁻¹ * ellipticFIntegrand (-c / (1 - c)) w := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hsin : Real.sin (Real.pi / 2 + w) = Real.cos w := by
    rw [show Real.pi / 2 + w = Real.pi / 2 - -w by ring, Real.sin_pi_div_two_sub, Real.cos_neg]
  simp only [ellipticFIntegrand, ellipticEIntegrand, hsin]
  rw [← mul_inv, ← Real.sqrt_mul h1c.le]
  congr 2
  field_simp
  linear_combination (-c) * Real.sin_sq_add_cos_sq w

-- Theorem: hence `F` past `π/2` is `F` at the complementary parameter.
theorem ellipticF_pi_div_two_add {c : ℝ} (hc : c < 1) (u : ℝ) :
    ellipticF c (Real.pi / 2 + u)
      = ellipticF c (Real.pi / 2) + (Real.sqrt (1 - c))⁻¹ * ellipticF (-c / (1 - c)) u := by
  have hshift : (∫ ψ in (Real.pi / 2)..(Real.pi / 2 + u), ellipticFIntegrand c ψ)
      = (Real.sqrt (1 - c))⁻¹ * ellipticF (-c / (1 - c)) u := by
    have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := u)
      (ellipticFIntegrand c) (Real.pi / 2)
    rw [add_zero] at h
    rw [← h, ellipticF, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun w _ => ellipticFIntegrand_pi_div_two_add hc w
  rw [← hshift, ellipticF, ellipticF,
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_ellipticFIntegrand hc 0 (Real.pi / 2))
      (intervalIntegrable_ellipticFIntegrand hc (Real.pi / 2) (Real.pi / 2 + u))]

-- Theorem: the complete integral `F(π/2) = K` is P-constructible, as two quarter turns:
-- one at `c` and one at the complementary parameter.
theorem ellipticF_pi_div_two_Pconstructible {c : ℝ} (hcP : PConstructible c) (hc : c < 1) :
    PConstructible (ellipticF c (Real.pi / 2)) := by
  have hpi := Real.pi_pos
  have hquarter : |Real.pi / 4| < Real.pi / 2 := by
    rw [abs_of_pos (by linarith)]; linarith
  have hpi4 : PConstructible (Real.pi / 4) := by
    have h4 : PConstructible (4 : ℝ) := by
      convert PConstructible.mul two_Pconstructible two_Pconstructible using 1
      norm_num
    exact PConstructible.div pi_Pconstructible h4
  have hc'P : PConstructible (-c / (1 - c)) :=
    PConstructible.div (neg_Pconstructible hcP)
      (PConstructible.sub PConstructible.base_one hcP)
  have h := ellipticF_pi_div_two_add hc (-(Real.pi / 4))
  rw [show Real.pi / 2 + -(Real.pi / 4) = Real.pi / 4 by ring, ellipticF_neg] at h
  have hkey : ellipticF c (Real.pi / 2)
      = ellipticF c (Real.pi / 4)
        + (Real.sqrt (1 - c))⁻¹ * ellipticF (-c / (1 - c)) (Real.pi / 4) := by
    linear_combination -h
  rw [hkey]
  exact PConstructible.add
    (ellipticF_Pconstructible_of_abs_lt hcP hpi4 hc hquarter)
    (PConstructible.mul
      (inv_Pconstructible
        (sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hcP)))
      (ellipticF_Pconstructible_of_abs_lt hc'P hpi4 (compl_param_lt_one hc) hquarter))

-- Theorem: `F(φ)` is P-constructible for `|φ| ≤ π/2`, the quarter turn now included.
theorem ellipticF_Pconstructible_of_abs_le {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) (hφ : |φ| ≤ Real.pi / 2) :
    PConstructible (ellipticF c φ) := by
  have hpi := Real.pi_pos
  rcases eq_or_lt_of_le hφ with h | h
  · rcases (abs_eq (by positivity)).mp h with rfl | rfl
    · exact ellipticF_pi_div_two_Pconstructible hcP hc
    · rw [ellipticF_neg]
      exact neg_Pconstructible (ellipticF_pi_div_two_Pconstructible hcP hc)
  · exact ellipticF_Pconstructible_of_abs_lt hcP hφP hc h

-- Theorem: `F(φ)` is P-constructible for `0 ≤ φ ≤ π`, one full period.
theorem ellipticF_Pconstructible_of_mem_Icc {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi) :
    PConstructible (ellipticF c φ) := by
  have hpipos := Real.pi_pos
  have hc'P : PConstructible (-c / (1 - c)) :=
    PConstructible.div (neg_Pconstructible hcP)
      (PConstructible.sub PConstructible.base_one hcP)
  have huP : PConstructible (φ - Real.pi / 2) :=
    PConstructible.sub hφP (PConstructible.div pi_Pconstructible two_Pconstructible)
  have hu : |φ - Real.pi / 2| ≤ Real.pi / 2 := by
    rw [abs_le]; constructor <;> linarith
  rw [show φ = Real.pi / 2 + (φ - Real.pi / 2) by ring, ellipticF_pi_div_two_add hc]
  exact PConstructible.add (ellipticF_pi_div_two_Pconstructible hcP hc)
    (PConstructible.mul
      (inv_Pconstructible
        (sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hcP)))
      (ellipticF_Pconstructible_of_abs_le hc'P huP (compl_param_lt_one hc) hu))

-- Theorem: the first-kind integrand has period `π`, being the reciprocal of the
-- second-kind one.
theorem periodic_ellipticFIntegrand (c : ℝ) :
    Function.Periodic (ellipticFIntegrand c) Real.pi := fun θ => by
  simp [ellipticFIntegrand, ellipticEIntegrand, Real.sin_add_pi]

-- Theorem: `F(φ + nπ) = F(φ) + n · F(π)`, exactly as for `E`.
theorem ellipticF_add_int_mul_pi {c : ℝ} (hc : c < 1) (φ : ℝ) (n : ℤ) :
    ellipticF c (φ + n * Real.pi) = ellipticF c φ + n * ellipticF c Real.pi := by
  have hper := periodic_ellipticFIntegrand c
  have hint : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (ellipticFIntegrand c) MeasureTheory.volume t₁ t₂ :=
    fun t₁ t₂ => intervalIntegrable_ellipticFIntegrand hc t₁ t₂
  have hA : (∫ θ in (0 : ℝ)..(n : ℝ) * Real.pi, ellipticFIntegrand c θ)
      = n * ellipticF c Real.pi := by
    have h := hper.intervalIntegral_add_zsmul_eq n 0 hint
    simpa [ellipticF, zsmul_eq_mul] using h
  have hB : (∫ θ in ((n : ℝ) * Real.pi)..(φ + (n : ℝ) * Real.pi), ellipticFIntegrand c θ)
      = ellipticF c φ := by
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := φ)
      (ellipticFIntegrand c) ((n : ℝ) * Real.pi)
    have hshift : ∀ x : ℝ,
        ellipticFIntegrand c (x + (n : ℝ) * Real.pi) = ellipticFIntegrand c x :=
      fun x => hper.int_mul n x
    simp only [hshift, zero_add] at h
    rw [ellipticF, h]
  rw [ellipticF, ← intervalIntegral.integral_add_adjacent_intervals
    (b := (n : ℝ) * Real.pi) (hint 0 _) (hint _ _), hA, hB]
  ring

-- Theorem: `F(φ)` is P-constructible for every P-constructible `φ` and every
-- P-constructible parameter `c < 1`.
--
-- Reduction modulo `π` on top of the reflection above, so no restriction on `φ` at all —
-- matching `ellipticE_Pconstructible`.
theorem ellipticF_Pconstructible {c φ : ℝ} (hcP : PConstructible c) (hφP : PConstructible φ)
    (hc : c < 1) : PConstructible (ellipticF c φ) := by
  obtain ⟨n, h0, hpi⟩ := exists_int_half_turns φ
  have hrP : PConstructible (φ - n * Real.pi) :=
    PConstructible.sub hφP (PConstructible.mul (int_Pconstructible n) pi_Pconstructible)
  have hr := ellipticF_Pconstructible_of_mem_Icc hcP hrP hc h0 hpi
  have hFpi := ellipticF_Pconstructible_of_mem_Icc hcP pi_Pconstructible hc
    Real.pi_pos.le le_rfl
  have hkey : ellipticF c φ
      = ellipticF c (φ - n * Real.pi) + n * ellipticF c Real.pi := by
    have h := ellipticF_add_int_mul_pi hc (φ - n * Real.pi) n
    rwa [sub_add_cancel] at h
  rw [hkey]
  exact PConstructible.add hr (PConstructible.mul (int_Pconstructible n) hFpi)

/-! #### In terms of the modulus

Legendre writes both integrals with the modulus `k`, where `c = k²`. Those are the
statements one would quote; they are the case `c = k²` of the theorems above, and the
hypothesis `k² < 1` is the usual `|k| < 1`. -/

-- Theorem: `E(φ, k) = ∫₀^φ √(1 - k² sin²θ) dθ` is P-constructible.
theorem ellipticE_sq_Pconstructible {k φ : ℝ} (hk : PConstructible k)
    (hφ : PConstructible φ) (hk1 : k ^ 2 < 1) : PConstructible (ellipticE (k ^ 2) φ) :=
  ellipticE_Pconstructible (sq_Pconstructible hk) hφ hk1

-- Theorem: `F(φ, k) = ∫₀^φ dθ/√(1 - k² sin²θ)` is P-constructible.
theorem ellipticF_sq_Pconstructible {k φ : ℝ} (hk : PConstructible k)
    (hφ : PConstructible φ) (hk1 : k ^ 2 < 1) : PConstructible (ellipticF (k ^ 2) φ) :=
  ellipticF_Pconstructible (sq_Pconstructible hk) hφ hk1

end Pconstructible
