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

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Pptc.Curves

Plain curve helpers shared by `Pptc.TextBox` (text warps trace their guides by arc length)
and `Pptc.Defs` (the `arc_length`, `arc_of_length` and `cubic_bezier` constructors). They
were moved here from `Pptc.Defs` unchanged, so that `Pptc.TextBox`, which `Pptc.Defs`
imports, can use them too.
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

end Pconstructible
