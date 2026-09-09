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
ellipses, axis-aligned rectangles, degree-≤6 polynomial graphs with rational
coefficients, power laws, the exponential `y = 2 ^ x`, the sine curve `y = sin x`,
cubic Bézier curves with P-constructible control points) and the geometric operations of
translating along either axis, scaling either axis, rotating by whole-degree increments,
cropping to a rectangular window, marking off an arc of prescribed length, and offsetting
an arc sideways by a fixed normal distance.

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

`PConstructibleCurve.offset` follows the same convention for the same reason: it takes a
tracing `γ` of an arc and pushes every point of it a fixed signed distance along the
`unitNormal` there, so it too needs a parametrization at the point of use, and it needs
that parametrization to be regular (nonvanishing `speed`) for the normal to exist at all.
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

/-- The cubic Bézier curve with control points `p₁ p₂ p₃ p₄`, in Bernstein form: at
parameter `t` it is the weighted average of the control points with weights
`(1-t)³, 3(1-t)²t, 3(1-t)t², t³`.

`p₁` and `p₄` are the endpoints (`bezierParam p₁ p₂ p₃ p₄ 0 = p₁` and `… 1 = p₄`); `p₂`
and `p₃` are the off-curve handles that set the initial and final tangent directions.
Only `t ∈ [0, 1]` is drawn; that is where the weights are non-negative and the curve
stays inside the convex hull of the control points. -/
def bezierParam (p₁ p₂ p₃ p₄ : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  ((1 - t) ^ 3 * p₁.1 + 3 * (1 - t) ^ 2 * t * p₂.1
      + 3 * (1 - t) * t ^ 2 * p₃.1 + t ^ 3 * p₄.1,
   (1 - t) ^ 3 * p₁.2 + 3 * (1 - t) ^ 2 * t * p₂.2
      + 3 * (1 - t) * t ^ 2 * p₃.2 + t ^ 3 * p₄.2)

/-- The unit normal of a plane curve `γ` at parameter `t`: the velocity vector turned a
quarter turn counterclockwise and rescaled to length one.

As in `speed`, the coordinates are written out rather than routed through Mathlib's norm
on `ℝ × ℝ`, which is the supremum norm and would rescale by the wrong quantity. At a
singular parameter (`speed γ t = 0`) the divisions evaluate to `0`; nothing below relies
on that junk value, as every use carries a regularity hypothesis ruling the case out. -/
noncomputable def unitNormal (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (-deriv (fun s => (γ s).2) t / speed γ t, deriv (fun s => (γ s).1) t / speed γ t)

/-- The curve `γ` displaced by the fixed signed distance `d`: each point is pushed `d`
along the `unitNormal` there, so the new curve runs alongside the old one at constant
clearance `|d|`. Positive `d` moves to the left of the direction of travel, negative `d`
to the right, and `d = 0` reproduces the curve. -/
noncomputable def offsetParam (γ : ℝ → ℝ × ℝ) (d : ℝ) (t : ℝ) : ℝ × ℝ :=
  ((γ t).1 + d * (unitNormal γ t).1, (γ t).2 + d * (unitNormal γ t).2)

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
  -- The graph of a polynomial of degree ≤ 6 with rational (not merely
  -- `PConstructible`) coefficients.
  | poly_graph (p : Polynomial ℚ) (hdeg : p.natDegree ≤ 6) :
      PConstructibleCurve {pt : ℝ × ℝ | pt.2 = Polynomial.aeval pt.1 p}
  -- A power-law curve `y = a * x ^ b` for `x > 0`, with rational `a`, `b`.
  | power_law (a b : ℚ) :
      PConstructibleCurve {pt : ℝ × ℝ | 0 < pt.1 ∧ pt.2 = (a : ℝ) * pt.1 ^ (b : ℝ)}
  -- The exponential curve `y = 2 ^ x`, with `^` real exponentiation. Unlike `power_law`
  -- the variable is in the exponent, so this is genuinely a new family: it is what makes
  -- logarithms reachable, by reading off the other coordinate.
  | exp_two :
      PConstructibleCurve {p : ℝ × ℝ | p.2 = (2 : ℝ) ^ p.1}
  -- The sine curve `y = sin x`. Like `exp_two` this is a single fixed curve rather than a
  -- family: the drawing program offers one wave shape, and everything else about a sinusoid
  -- is reached by moving and resizing it. `scale_y` sets the amplitude, `scale_x` the
  -- frequency, `translate_x` the phase and `translate_y` the vertical offset, so the general
  -- `y = A * sin (ω * x + φ) + c` with `PConstructible` `A, ω, φ, c` follows from this
  -- constructor together with the closure operations below.
  --
  -- Individual values `Real.sin x` are already reachable without this: `sin_Pconstructible`
  -- in `Pptc.Basic` gets them one at a time off a circular arc. But a point is not a curve,
  -- and only a curve can be crossed by `inter_x` / `inter_y` or measured by `arc_length`.
  -- What this adds is the whole graph at once — the transcendental counterpart of
  -- `poly_graph` — bringing solutions of mixed equations such as `sin x = x / 2` within
  -- reach, once `restrict` has cut the two graphs down to a single crossing.
  | sine :
      PConstructibleCurve {p : ℝ × ℝ | p.2 = Real.sin p.1}
  -- A cubic Bézier curve with `PConstructible` control points `p₁, p₂, p₃, p₄`, drawn
  -- over the parameter interval `[0, 1]`. This is the curve tool of the drawing program:
  -- two endpoints (`p₁`, `p₄`) plus two handles (`p₂`, `p₃`).
  --
  -- Unlike `poly_graph` this is a *parametric* curve, so it is genuinely new in two ways:
  -- its coefficients are `PConstructible` rather than rational, and it need not be the
  -- graph of a function of `x` (both coordinates move cubically in `t`, so the curve may
  -- double back over an abscissa, or close up into a loop).
  --
  -- No non-degeneracy hypothesis is imposed. Coincident control points are legal input to
  -- the drawing program and still produce a drawable stroke; with all four equal the image
  -- is a single point, a degenerate but harmless member of the class. Contrast `ellipse`
  -- and `rectangle`, which need positive dimensions because their defining equations would
  -- otherwise divide by zero.
  | cubic_bezier (p₁ p₂ p₃ p₄ : ℝ × ℝ)
      (hx₁ : PConstructible p₁.1) (hy₁ : PConstructible p₁.2)
      (hx₂ : PConstructible p₂.1) (hy₂ : PConstructible p₂.2)
      (hx₃ : PConstructible p₃.1) (hy₃ : PConstructible p₃.2)
      (hx₄ : PConstructible p₄.1) (hy₄ : PConstructible p₄.2) :
      PConstructibleCurve (bezierParam p₁ p₂ p₃ p₄ '' Set.Icc 0 1)
  -- Closure operations (axioms, not derived from `PConstructible` on ℝ)
  -- Translating along the `x` axis by a `PConstructible` distance, and along the `y`
  -- axis by one. These are the plainest operation the drawing program has: picking a
  -- shape up and dropping it somewhere else.
  --
  -- Every other operation here fixes the origin — `scale_x`, `scale_y` and `rotate` all
  -- hold it still — so without these two the only curves that could be placed anywhere
  -- were `ellipse` and `rectangle`, which carry their own centre. Adding them is what
  -- closes the class under *affine* maps of the plane rather than merely linear ones,
  -- and it is what puts a hyperbola anywhere but astride the axes: `power_law` draws
  -- `y = c / x` and nothing else, while `y = c / (x - u) + v` needs a genuine move.
  | translate_x {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
      {u : ℝ} (hu : PConstructible u) :
      PConstructibleCurve ((fun p : ℝ × ℝ => (p.1 + u, p.2)) '' S)
  | translate_y {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
      {v : ℝ} (hv : PConstructible v) :
      PConstructibleCurve ((fun p : ℝ × ℝ => (p.1, p.2 + v)) '' S)
  -- Scaling the `x` axis by a `PConstructible` factor, and scaling the `y` axis by one.
  -- These are the resize handles of the drawing program: dragging the side handle of a
  -- shape changes its width and leaves its height alone, and vice versa. Uniform scaling
  -- is the composite with a common factor; see `stretch_PConstructibleCurve`.
  --
  -- Having the two axes move independently is strictly stronger than moving them
  -- together, and not by a little. A uniform scale and a rotation are both conformal, so
  -- no composite of those could ever carry a circle to a non-circular ellipse. Splitting
  -- the factors is what makes `linearMap_PConstructibleCurve` possible, and what lets
  -- `rotate_PConstructibleCurve` reach angles that are not whole numbers of degrees.
  | scale_x {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
      {s : ℝ} (hs : PConstructible s) :
      PConstructibleCurve ((fun p : ℝ × ℝ => (s * p.1, p.2)) '' S)
  | scale_y {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
      {s : ℝ} (hs : PConstructible s) :
      PConstructibleCurve ((fun p : ℝ × ℝ => (p.1, s * p.2)) '' S)
  -- Rotation by any whole number of degrees. Taken as an axiom: unlike `scale_x`, this
  -- does not require `Real.cos`/`Real.sin` of the angle to be `PConstructible`.
  --
  -- The restriction to whole degrees restricts what is *assumed*, not what is reachable:
  -- `rotate_PConstructibleCurve` derives rotation by every `PConstructible` angle from
  -- this constructor together with `scale_x` and `scale_y`.
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

  -- Offset an arc of a constructible curve sideways by a fixed `PConstructible` normal
  -- distance `d`: push every point of the arc `d` units along its unit normal
  -- (`offsetParam`). Modelling: the parallel-copy or outline operation of the drawing
  -- program, the stroke that runs alongside a drawn path at constant clearance. That is
  -- not a scaled copy — scaling moves points along rays from a centre, so the clearance
  -- it leaves varies from place to place, while this one is the same everywhere.
  --
  -- `d` is required to be `PConstructible` but not positive. Its sign chooses which side
  -- of the path the copy runs on, and both sides are equally drawable.
  --
  -- The arc is presented by a tracing `γ`, as in `PConstructible.arc_length` and
  -- `arc_of_length`, with the same `hsub` and `hinj` making `γ` a genuine non-retracing
  -- tracing of a piece of `S`. Nothing is integrated here, so `hint` is absent; two
  -- hypotheses take its place, both about the *velocity*, which is what the offset moves
  -- with:
  --
  -- * `hreg` says the arc is regular, its speed never vanishing. This is what gives the
  --   arc a tangent direction at every parameter, and so makes `unitNormal` an honest
  --   unit vector rather than the `0` that dividing by `0` would return. A curve may stop
  --   dead in `arc_of_length`, where it merely contributes no length; here stopping dead
  --   would leave the offset direction undefined.
  -- * `hC1` says the two velocity components are continuous, so the normal turns
  --   continuously and the offset is a single connected stroke. For `arc_of_length` that
  --   came for free, `hdiff` alone forcing `γ` continuous; mere differentiability lets
  --   the derivative jump about, which would scatter the offset into pieces.
  --
  -- The result is geometric, depending on the arc only as a subset of the plane: a
  -- reparametrization leaves each point's tangent line alone, hence its unit normal up to
  -- sign, and reversing the direction of travel flips exactly that sign — which changes
  -- nothing about what is reachable, since `-d` is `PConstructible` whenever `d` is.
  --
  -- No injectivity is claimed of the offset itself, and it can genuinely fail: pushed
  -- further than the radius of curvature, a parallel copy folds over and acquires cusps
  -- and self-crossings. That is what the operation draws, so it is not excluded.
  | offset {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
      (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a ≤ b)
      -- `γ` traces an arc of `S` without retracing it ...
      (hsub : γ '' Set.Icc a b ⊆ S)
      (hinj : Set.InjOn γ (Set.Icc a b))
      -- ... and does so with a continuous, nowhere-vanishing velocity, so that the arc
      -- has a continuously turning unit normal at every point.
      (hdiff : ∀ t ∈ Set.Icc a b,
        DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t)
      (hreg : ∀ t ∈ Set.Icc a b, speed γ t ≠ 0)
      (hC1 : ContinuousOn (deriv (fun s => (γ s).1)) (Set.Icc a b) ∧
        ContinuousOn (deriv (fun s => (γ s).2)) (Set.Icc a b))
      -- The displacement is a P-constructible signed distance, of either sign.
      {d : ℝ} (hd : PConstructible d) :
      PConstructibleCurve (offsetParam γ d '' Set.Icc a b)
end

end Pconstructible
