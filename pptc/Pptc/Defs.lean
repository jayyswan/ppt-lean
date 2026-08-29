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
point), so they must be declared together.
-/

namespace Pconstructible

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
