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
coefficients, power laws) and the geometric operations of stretching, rotating by
whole-degree increments, and intersecting.

The two are mutually inductive: a `PConstructibleCurve` may need `PConstructible`
parameters (e.g. an ellipse's center and dimensions), and `PConstructible` may need
a `PConstructibleCurve` (reading off the coordinate of a curve-curve intersection
point, or the arc length of a piece of one), so they must be declared together.

Arc length is measured by `arcLengthOf`, which integrates `speed` over a parameter
interval. The parametrization is supplied at the point of extraction rather than being
stored in `PConstructibleCurve`; see the comment on `PConstructible.arc_length`.
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
  | ellipse (cx cy width height : ℝ)
      (hcx : PConstructible cx) (hcy : PConstructible cy)
      (hw : PConstructible width) (hh : PConstructible height) :
      PConstructibleCurve
        {p : ℝ × ℝ | ((p.1 - cx) / (width / 2)) ^ 2 + ((p.2 - cy) / (height / 2)) ^ 2 = 1}
  -- An axis-aligned rectangle (its boundary), given by center `(cx, cy)` and full
  -- `width`/`height`, all `PConstructible`.
  | rectangle (cx cy width height : ℝ)
      (hcx : PConstructible cx) (hcy : PConstructible cy)
      (hw : PConstructible width) (hh : PConstructible height) :
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

end

end Pconstructible
