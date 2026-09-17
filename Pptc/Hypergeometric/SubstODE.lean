/-
Copyright (c) 2024 Lean Community. All rights reserved.

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
-- `Goursat` supplies the general hypergeometric equation `hypSeries_ode` and, through
-- `Quadratic`, the substitution and chain-rule API of `PowerSeries` used below.
import Pptc.Hypergeometric.Goursat
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Pptc.Hypergeometric.SubstODE

The hypergeometric equation of `hypSeries a b c` is not tied to the variable `X`: it pulls
back along *any* power series `φ` with vanishing constant term, i.e. any valid substitution.
Writing `D` for `PowerSeries.derivative ℝ`, `H = hypSeries a b c` and `F = subst φ H`, the
chain rule for formal substitution gives

`D F = subst φ (D H) · D φ`,
`D D F = subst φ (D D H) · (D φ)² + subst φ (D H) · D D φ`.

Substituting `X ↦ φ` in `X(1−X) H'' + (c − (a+b+1)X) H' − ab H = 0` turns the first three
factors into their `φ`-images, and eliminating `subst φ (D D H)` and `subst φ (D H)` from the
two chain-rule identities leaves a single equation for `F` alone. Clearing the denominator
`D φ` (the classical reduced equation divides by `D φ`, which need not be invertible as a
formal series) multiplies it through by `(D φ)³` and yields the statement below. It is the
formal engine behind every reduction of the hypergeometric equation — the `w = 4X(1−X)` and
`w = X²` pullbacks of `Pptc.Hypergeometric.Quadratic` and `Pptc.Hypergeometric.Heun` are the
cases `φ = 4X(1−X)` and `φ = X²`.
-/

open scoped PowerSeries

namespace Pconstructible

noncomputable section

/-- The hypergeometric equation of `hypSeries a b c` pulled back along an arbitrary
substitution `φ` with vanishing constant term, multiplied through by `(φ')³`. With
`F = subst φ (hypSeries a b c)` this reads
`φ(1−φ)φ' F'' + (−φ(1−φ)φ'' + (c − (a+b+1)φ)φ'²) F' − ab φ'³ F = 0`. -/
-- Theorem: the hypergeometric equation pulled back along any substitution `φ` with
-- vanishing constant term, cleared of the `φ'` denominator by multiplying by `(φ')³`.
theorem hypSeries_subst_ode {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    {φ : PowerSeries ℝ} (hφ : PowerSeries.HasSubst φ) :
    φ * (1 - φ) * PowerSeries.derivative ℝ φ
        * PowerSeries.derivative ℝ
            (PowerSeries.derivative ℝ (PowerSeries.subst φ (hypSeries a b c)))
      + (-(φ * (1 - φ) * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ φ))
          + (PowerSeries.C c - PowerSeries.C (a + b + 1) * φ)
            * (PowerSeries.derivative ℝ φ) ^ 2)
        * PowerSeries.derivative ℝ (PowerSeries.subst φ (hypSeries a b c))
      - PowerSeries.C (a * b) * (PowerSeries.derivative ℝ φ) ^ 3
        * PowerSeries.subst φ (hypSeries a b c) = 0 := by
  have hzero : PowerSeries.subst φ (0 : PowerSeries ℝ) = 0 := by
    simp only [← PowerSeries.coe_substAlgHom hφ, map_zero]
  -- The hypergeometric ODE of `H = hypSeries a b c` after applying `X ↦ φ`.
  have hsubst : PowerSeries.subst φ
      (PowerSeries.X * (1 - PowerSeries.X)
          * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries a b c))
        + (PowerSeries.C c - PowerSeries.C (a + b + 1) * PowerSeries.X)
          * PowerSeries.derivative ℝ (hypSeries a b c)
        - PowerSeries.C (a * b) * hypSeries a b c) = 0 := by
    rw [hypSeries_ode a b c hc, hzero]
  have key : φ * (1 - φ)
        * PowerSeries.subst φ
            (PowerSeries.derivative ℝ
              (PowerSeries.derivative ℝ (hypSeries a b c)))
      + (PowerSeries.C c - PowerSeries.C (a + b + 1) * φ)
        * PowerSeries.subst φ (PowerSeries.derivative ℝ (hypSeries a b c))
      - PowerSeries.C (a * b) * PowerSeries.subst φ (hypSeries a b c) = 0 := by
    rw [← hsubst]
    simp only [← PowerSeries.coe_substAlgHom hφ, map_add, map_sub, map_mul, map_one,
      PowerSeries.substAlgHom_X hφ, PowerSeries.C_eq_algebraMap, AlgHom.commutes]
  -- The two chain-rule identities for `F = subst φ H`.
  have hB1 : PowerSeries.derivative ℝ (PowerSeries.subst φ (hypSeries a b c))
      = PowerSeries.subst φ (PowerSeries.derivative ℝ (hypSeries a b c))
        * PowerSeries.derivative ℝ φ :=
    PowerSeries.derivative_subst hφ
  have hB2 : PowerSeries.derivative ℝ (PowerSeries.derivative ℝ
        (PowerSeries.subst φ (hypSeries a b c)))
      = (PowerSeries.subst φ
              (PowerSeries.derivative ℝ
                (PowerSeries.derivative ℝ (hypSeries a b c)))
            * PowerSeries.derivative ℝ φ)
          * PowerSeries.derivative ℝ φ
        + PowerSeries.subst φ
              (PowerSeries.derivative ℝ (hypSeries a b c))
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ φ) := by
    rw [hB1, Derivation.leibniz, PowerSeries.derivative_subst hφ, smul_eq_mul, smul_eq_mul]
    ring
  rw [hB2, hB1]
  linear_combination (PowerSeries.derivative ℝ φ) ^ 3 * key

end

end Pconstructible
