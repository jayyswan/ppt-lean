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
-- `CubicSetup` supplies the parametric series `α, β, γ` of the cubic transformation and the
-- identities they satisfy; `SubstODE` supplies the general pullback of the hypergeometric
-- equation along an arbitrary substitution.
import Pptc.Hypergeometric.CubicSetup
import Pptc.Hypergeometric.SubstODE

open scoped PowerSeries

namespace Pconstructible

noncomputable section

/-! # Pptc.Hypergeometric.Cubic

Ramanujan's **cubic** signature transformation, as a formal power series identity in the
parameter `p`:

`₂F₁(1/3, 2/3; 1; β(p)) = γ(p) · ₂F₁(1/2, 1/2; 1; α(p))`,

with `β(p) = 27p²(1+p)²/(4(1+p+p²)³)`, `α(p) = p³(2+p)/(1+2p)` and
`γ(p) = (1+p+p²)/√(1+2p)`.

The proof follows the same pattern as Goursat's quartic transformation (`Pptc.Hypergeometric.V7`):
both sides satisfy one shared second-order linear ODE, so they are equal once their constant
terms agree. The shared operator is the pullback of the `(1/3, 2/3; 1)` hypergeometric equation
along `β`, multiplied through by `(β')³` so that no division by `β'` (which vanishes at `p = 0`)
is needed:

`cubicOp F = β(1−β)β' F'' + [−β(1−β)β'' + (1−2β)(β')²] F' − (2/9)(β')³ F`.

This file defines `cubicOp` and proves that the *left* side solves it; the right side and the
uniqueness/assembly live in later files.
-/

/-- The pullback of the `(1/3, 2/3; 1)` hypergeometric equation along the cubic map `β`,
multiplied through by `(β')³`. -/
noncomputable def cubicOp (F : PowerSeries ℝ) : PowerSeries ℝ :=
    betaSeries * (1 - betaSeries) * PowerSeries.derivative ℝ betaSeries
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ F)
      + (-(betaSeries * (1 - betaSeries)
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ betaSeries))
          + (1 - 2 * betaSeries) * (PowerSeries.derivative ℝ betaSeries) ^ 2)
        * PowerSeries.derivative ℝ F
      - PowerSeries.C (2 / 9) * (PowerSeries.derivative ℝ betaSeries) ^ 3 * F

/-- The left-hand side of the cubic transformation, `₂F₁(1/3,2/3;1;β)`, solves `cubicOp`. -/
-- Theorem: `cubicOp (₂F₁(1/3,2/3;1;β)) = 0`.
theorem cubicOp_lhs :
    cubicOp (PowerSeries.subst betaSeries (hypSeries (1 / 3) (2 / 3) 1)) = 0 := by
  rw [cubicOp]
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n hn
    have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := hypSeries_subst_ode (a := (1 : ℝ) / 3) (b := (2 : ℝ) / 3) (c := 1) hc
    hasSubst_betaSeries
  rw [show PowerSeries.C (1 : ℝ) = (1 : PowerSeries ℝ) from rfl,
    show PowerSeries.C ((1 : ℝ) / 3 + (2 : ℝ) / 3 + 1) = (2 : PowerSeries ℝ)
      from by rw [show (1 : ℝ) / 3 + (2 : ℝ) / 3 + 1 = 2 by norm_num]; rfl,
    show PowerSeries.C ((1 : ℝ) / 3 * ((2 : ℝ) / 3)) = PowerSeries.C (2 / 9 : ℝ)
      from by norm_num] at h
  exact h

end

end Pconstructible
