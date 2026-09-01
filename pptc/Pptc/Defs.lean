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

-- Targeted imports rather than `import Mathlib`: the latter pulls in all 8317 Mathlib
-- modules and roughly doubles the time to check this file. If a future addition needs a
-- Mathlib result that is not in scope, add the specific module here.
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Pptc.Defs

Core definitions for the Pptc (PowerPoint Constructibility) project:
`PConstructible : ℝ → Prop` for real numbers reachable by a finite sequence of
arithmetic operations (`+ - * /`) from `1`, together with intersecting a point out
of two constructible curves, and `PConstructibleCurve : Set (ℝ × ℝ) → Prop` for
point-sets reachable from a finite sequence of curve constructions (axis-aligned
ellipses, axis-aligned rectangles, degree-≤7 polynomial graphs with rational
coefficients, power laws, the exponential `y = 2 ^ x`) and the geometric operations of
stretching, rotating by whole-degree increments, cropping to a rectangular window, and
marking off an arc of prescribed length.

The two are mutually inductive: a `PConstructibleCurve` may need `PConstructible`
parameters (e.g. an ellipse's center and dimensions), and `PConstructible` may need
a `PConstructibleCurve` (reading off the coordinate of a curve-curve intersection
point, or the arc length of a piece of one), so they must be declared together.

Arc length is measured by `arcLengthOf`, which integrates `speed` over a parameter
interval, and it is used in both directions: `PConstructible.arc_length` reads the
length of a given arc off the plane, while `PConstructibleCurve.arc_of_length` lays out
an arc of a given length. Either way the parametrization is supplied at the point of
use rather than being stored in `PConstructibleCurve`; see the comment on
`PConstructible.arc_length`.
-/

namespace Pconstructible

/-- The speed of a plane curve `γ` at parameter `t`, i.e. the Euclidean norm of its
velocity vector.

The Euclidean norm is written out as `√(x' ^ 2 + y' ^ 2)` rather than as `‖deriv γ t‖`
on purpose: the product norm that Mathlib puts on `ℝ × ℝ` is the *supremum* norm, so
`‖deriv γ t‖` would silently compute the wrong quantity. -/
noncomputable def speed (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (deriv (fun s => (γ s).1) t ^ 2 + deriv (fun s => (γ s).2) t ^ 2)

/-- The arc length of the plane curve `γ` traced over the parameter interval `[a, b]`. -/
noncomputable def arcLengthOf (γ : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, speed γ t

mutual

/-- `PConstructible x` holds if `x` can be reached by a finite sequence of
legal construction steps from the base numbers. -/
inductive PConstructible : ℝ → Prop
  | base_one : PConstructible 1
  -- Additive closure
  | add {x y} (hx : PConstructible x) (hy : PConstructible y) :
       PConstructible (x + y)
  -- Subtractive closure
  | sub {x y} (hx : PConstructible x) (hy : PConstructible y) :
       PConstructible (x - y)
  -- Multiplicative closure
  | mul {x y} (hx : PConstructible x) (hy : PConstructible y) :
       PConstructible (x * y)
  -- Divisive closure
  | div {x y} (hx : PConstructible x) (hy : PConstructible y) :
       PConstructible (x / y)
  -- The x-coordinate of a point where two constructible curves meet in
  -- exactly one point (not a shared segment or multiple points).
  | inter_x {S T : Set (ℝ × ℝ)} (hS : PConstructibleCurve S) (hT : PConstructibleCurve T)
      {x y : ℝ} (h : S ∩ T = {(x, y)}) :
      PConstructible x
  -- The y-coordinate of a point where two constructible curves meet in
  -- exactly one point (not a shared segment or multiple points).
  | inter_y {S T : Set (ℝ × ℝ)} (hS : PConstructibleCurve S) (hT : PConstructibleCurve T)
      {x y : ℝ} (h : S ∩ T = {(x, y)}) :
      PConstructible y
  -- The arc length of a piece of a constructible curve. The parametrization `γ` is
  -- supplied here, at the point of extraction, rather than being stored in
  -- `PConstructibleCurve`: it is a witness that the thing being measured really is an
  -- arc of `S`, and (for a closed curve such as an ellipse, where two points bound two
  -- different arcs) it is also what selects *which* arc is meant.
  --
  -- The endpoints of the arc are required to be `PConstructible` *points of the plane*,
  -- not merely `PConstructible` parameter values. Constraining `a` and `b` would achieve
  -- nothing, since `γ` is arbitrary and can always be reparametrized: taking `a = 0`,
  -- `b = 1` and `γ t = (π * t, (π * t) ^ 2)` traces the parabola `y = x ^ 2` out to
  -- `x = π`, and letting that endpoint vary continuously would make every real number an
  -- arc length, collapsing `PConstructible` to all of `ℝ`. Pinning the endpoints in the
  -- plane instead makes reparametrization harmless, since any two injective tracings of
  -- the same arc give the same integral.
  | arc_length {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
      (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a ≤ b)
      -- `γ` traces an arc of `S` ...
      (hsub : γ '' Set.Icc a b ⊆ S)
      -- ... without retracing any part of it, so the integral below is a genuine length ...
      (hinj : Set.InjOn γ (Set.Icc a b))
      -- ... and is smooth enough for that integral to mean anything.
      (hdiff : ∀ t ∈ Set.Icc a b,
        DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t)
      (hint : IntervalIntegrable (speed γ) MeasureTheory.volume a b)
      -- Both endpoints of the arc are P-constructible points of the plane.
      (hx₀ : PConstructible (γ a).1) (hy₀ : PConstructible (γ a).2)
      (hx₁ : PConstructible (γ b).1) (hy₁ : PConstructible (γ b).2) :
      PConstructible (arcLengthOf γ a b)

/-- `PConstructibleCurve S` holds if the point-set `S ⊆ ℝ × ℝ` can be reached by a
finite sequence of legal curve constructions and geometric operations. -/
inductive PConstructibleCurve : Set (ℝ × ℝ) → Prop
  -- Base curve families
  -- An axis-aligned ellipse, given by center `(cx, cy)` and full bounding-box
  -- `width`/`height` (semi-axes `width / 2`, `height / 2`), all `PConstructible`.
  -- `width` and `height` must be positive: a degenerate ellipse cannot be drawn, and
  -- without this the divisions below would be by zero (which Lean evaluates to `0`,
  -- making the whole locus meaningless rather than merely empty).
  | ellipse (cx cy width height : ℝ)
      (hcx : PConstructible cx) (hcy : PConstructible cy)
      (hw : PConstructible width) (hh : PConstructible height)
      (hw_pos : 0 < width) (hh_pos : 0 < height) :
      PConstructibleCurve
        {p : ℝ × ℝ | ((p.1 - cx) / (width / 2)) ^ 2 + ((p.2 - cy) / (height / 2)) ^ 2 = 1}
  -- An axis-aligned rectangle (its boundary), given by center `(cx, cy)` and full
  -- `width`/`height`, all `PConstructible`.
  -- As for `ellipse`, `width` and `height` must be positive: a rectangle collapsed to a
  -- segment or a point is not a drawable shape. Use `restrict` to cut a genuine
  -- rectangle down to one of its edges instead.
  | rectangle (cx cy width height : ℝ)
      (hcx : PConstructible cx) (hcy : PConstructible cy)
      (hw : PConstructible width) (hh : PConstructible height)
      (hw_pos : 0 < width) (hh_pos : 0 < height) :
      PConstructibleCurve
        {p : ℝ × ℝ |
          (cx - width / 2 ≤ p.1 ∧ p.1 ≤ cx + width / 2 ∧
            (p.2 = cy - height / 2 ∨ p.2 = cy + height / 2)) ∨
          (cy - height / 2 ≤ p.2 ∧ p.2 ≤ cy + height / 2 ∧
            (p.1 = cx - width / 2 ∨ p.1 = cx + width / 2))}
  -- The graph of a polynomial of degree ≤ 7 with rational (not merely
  -- `PConstructible`) coefficients.
  | poly_graph (p : Polynomial ℚ) (hdeg : p.natDegree ≤ 7) :
      PConstructibleCurve {pt : ℝ × ℝ | pt.2 = Polynomial.aeval pt.1 p}
  -- A power-law curve `y = a * x ^ b` for `x > 0`, with rational `a`, `b`.
  | power_law (a b : ℚ) :
      PConstructibleCurve {pt : ℝ × ℝ | 0 < pt.1 ∧ pt.2 = (a : ℝ) * pt.1 ^ (b : ℝ)}
  -- The exponential curve `y = 2 ^ x`, with `^` real exponentiation. Unlike `power_law`
  -- the variable is in the exponent, so this is genuinely a new family: it is what makes
  -- logarithms reachable, by reading off the other coordinate.
  | exp_two :
      PConstructibleCurve {p : ℝ × ℝ | p.2 = (2 : ℝ) ^ p.1}
  -- Closure operations (axioms, not derived from `PConstructible` on ℝ)
  -- Uniform scaling by a `PConstructible` factor.
  | stretch {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
      {s : ℝ} (hs : PConstructible s) :
      PConstructibleCurve ((fun p : ℝ × ℝ => (s * p.1, s * p.2)) '' S)
  -- Rotation by any whole number of degrees. Taken as an axiom: unlike `stretch`,
  -- this does not require `Real.cos`/`Real.sin` of the angle to be `PConstructible`.
  | rotate {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S) (n : ℤ) :
      PConstructibleCurve
        ((fun p : ℝ × ℝ =>
            let θ := (n : ℝ) * (Real.pi / 180)
            (p.1 * Real.cos θ - p.2 * Real.sin θ,
             p.1 * Real.sin θ + p.2 * Real.cos θ)) '' S)
  -- Crop a curve to an axis-aligned window with `PConstructible` bounds, modelling
  -- cropping a shape to a rectangular frame.
  --
  -- This is not needed for arc length: `PConstructible.arc_length` takes `γ '' Icc a b ⊆ S`,
  -- a *subset*, so a piece of a curve can already be measured without cutting the curve
  -- itself. Its purpose is `inter_x` / `inter_y`, which demand that two curves meet in
  -- exactly one point. Most natural intersections are not singletons (a line crosses a
  -- circle twice, a polynomial can meet a line at up to `natDegree` points), so cropping
  -- one curve until only the wanted crossing survives is what makes those constructors
  -- usable.
  | restrict {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
      (xmin xmax ymin ymax : ℝ)
      (hxmin : PConstructible xmin) (hxmax : PConstructible xmax)
      (hymin : PConstructible ymin) (hymax : PConstructible ymax) :
      PConstructibleCurve
        (S ∩ {p : ℝ × ℝ | xmin ≤ p.1 ∧ p.1 ≤ xmax ∧ ymin ≤ p.2 ∧ p.2 ≤ ymax})

  -- Mark off an arc of prescribed `PConstructible` length `x` along a constructible
  -- curve, starting from a `PConstructible` point of it. Modelling: pinning a string of
  -- known length to a marked point of a drawn curve and laying it along the curve.
  --
  -- This is the converse of `PConstructible.arc_length`, and the two are deliberately
  -- complementary. There one knows *both* endpoints of an arc and reads off its length;
  -- here one knows *one* endpoint and the length, and gets the arc itself as a curve. So
  -- the far endpoint `γ b` is emphatically not required to be `PConstructible`: that is
  -- the whole point, since intersecting the resulting arc against another curve is what
  -- makes the far endpoint's coordinates reachable in turn (this is how `Real.cos` and
  -- `Real.sin` become P-constructible; see `Pptc.Basic`).
  --
  -- The side conditions on `γ` are exactly those of `PConstructible.arc_length`, and for
  -- the same reasons: `hsub` and `hinj` make `γ` a genuine non-retracing tracing of a
  -- piece of `S`, `hdiff` and `hint` make its length meaningful. Note `hdiff` also forces
  -- `γ` to be continuous, so the arc produced is connected: a single stroke, not a
  -- scattering of pieces of `S`.
  --
  -- Unlike `PConstructible.arc_length` no constraint on `b` is needed, even though `γ` is
  -- again arbitrary and reparametrizable. Reparametrizing moves `b`, but it moves it in
  -- lockstep with the arc's length, and that length is pinned to the `PConstructible`
  -- number `x`; the traced set is unchanged.
  | arc_of_length {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
      (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a ≤ b)
      -- `γ` traces an arc of `S`, without retracing, smoothly enough to have a length ...
      (hsub : γ '' Set.Icc a b ⊆ S)
      (hinj : Set.InjOn γ (Set.Icc a b))
      (hdiff : ∀ t ∈ Set.Icc a b,
        DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t)
      (hint : IntervalIntegrable (speed γ) MeasureTheory.volume a b)
      -- ... starting at a P-constructible point of the plane ...
      (hx₀ : PConstructible (γ a).1) (hy₀ : PConstructible (γ a).2)
      -- ... and running for the P-constructible length `x`.
      {x : ℝ} (hx : PConstructible x) (hlen : arcLengthOf γ a b = x) :
      PConstructibleCurve (γ '' Set.Icc a b)
end

end Pconstructible
