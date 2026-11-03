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
import Pptc.Basic

/-! # Pptc.OffsetInversion.Projectile — the optimal launch angle

Stream L0 of `PLAN-offset-inversion.md`. The angle that maximises the ground-to-ground
arc length of a vacuum projectile solves

    `sin θ · (gd⁻¹ θ) = 1`,   `gd⁻¹ θ = log (sec θ + tan θ)`.

The reduction is Cooper & Swifton's: put `θ = gd z`; then `sin θ = tanh z` and
`gd⁻¹ θ = z`, so the equation becomes the Laplace-limit equation `z tanh z = 1`. Writing
`λ = csch z` for the Laplace limit constant turns the solution into

    `θ* = arctan (1 / λ)`.

Since `Pptc/Basic.lean` already proves `laplaceLimit_Pconstructible`, the angle is
P-constructible immediately. `projectileAngle_spec` verifies that this explicit angle
really satisfies the stationarity equation.

**Gap, deliberately left as the plan allows.** Uniqueness of the root of
`sin θ · gd⁻¹ θ = 1` on `(0, π/2)` is *not* proved here: it needs strict monotonicity of
`θ ↦ sin θ · gd⁻¹ θ` (whose derivative is `cos θ · gd⁻¹ θ + tan θ > 0`) plus an existence
step. The plan's fallback is exactly this file: the explicit `arctan (1/λ)` together with
the identity, and a note of the gap. The monotonicity route is recorded in
`HANDOFF-offinv-L0.md`.
-/

namespace Pconstructible

/-- The launch angle that maximises the arc length of a vacuum projectile trajectory,
in the explicit form `arctan (1 / λ)` where `λ` is the Laplace limit constant. -/
noncomputable def projectileAngle : ℝ := Real.arctan (1 / laplaceLimit)

-- Theorem: `arctan (1 / λ)` is P-constructible, because `λ` is and `arctan` preserves
-- P-constructibility.
theorem projectileAngle_Pconstructible : PConstructible projectileAngle := by
  unfold projectileAngle
  pconstructible

-- Theorem: the optimal launch angle is strictly positive.
theorem projectileAngle_pos : 0 < projectileAngle := by
  unfold projectileAngle
  rw [Real.arctan_pos]
  exact one_div_pos.mpr laplaceLimit_pos

-- Theorem: the optimal launch angle is less than a right angle.
theorem projectileAngle_lt_pi_div_two : projectileAngle < Real.pi / 2 :=
  Real.arctan_lt_pi_div_two _

-- Theorem: the explicit angle `arctan (1 / λ)` satisfies the projectile stationarity
-- equation `sin θ · log (sec θ + tan θ) = 1`.
theorem projectileAngle_spec :
    Real.sin projectileAngle *
      Real.log ((Real.cos projectileAngle)⁻¹ + Real.tan projectileAngle) = 1 := by
  set φ : ℝ := Real.sqrt (1 + laplaceLimit ^ 2) with hφdef
  have hφpos : 0 < φ := by
    rw [hφdef]
    exact Real.sqrt_pos.mpr (by positivity)
  -- `laplaceLimit_spec` in the `φ` notation.
  have hspec : laplaceLimit * Real.exp φ = 1 + φ := by
    have hφ : Real.sqrt (1 + laplaceLimit ^ 2) = φ := hφdef.symm
    simpa [hφ] using laplaceLimit_spec
  -- `sqrt (1 + (1/λ)²) = φ / λ`.
  have hsqrt : Real.sqrt (1 + (1 / laplaceLimit) ^ 2) = φ / laplaceLimit := by
    rw [show 1 + (1 / laplaceLimit) ^ 2 = (1 + laplaceLimit ^ 2) / laplaceLimit ^ 2 by
      field_simp [laplaceLimit_pos.ne']
      ring]
    rw [Real.sqrt_div (by positivity) (laplaceLimit ^ 2), Real.sqrt_sq laplaceLimit_pos.le]
  have hsin : Real.sin projectileAngle = 1 / φ := by
    unfold projectileAngle
    rw [Real.sin_arctan, hsqrt]
    field_simp [laplaceLimit_pos.ne', hφpos.ne']
  have hcos : Real.cos projectileAngle = laplaceLimit / φ := by
    unfold projectileAngle
    rw [Real.cos_arctan, hsqrt]
    field_simp [hφpos.ne']
  have htan : Real.tan projectileAngle = 1 / laplaceLimit := by
    unfold projectileAngle
    rw [Real.tan_arctan]
  -- `log ((φ + 1)/λ) = φ`, which is `laplaceLimit_spec` inverted.
  have hexp : Real.exp φ = (φ + 1) / laplaceLimit := by
    rw [eq_div_iff laplaceLimit_pos.ne']
    linarith [hspec]
  have hlog : Real.log ((φ + 1) / laplaceLimit) = φ := by
    rw [← hexp, Real.log_exp]
  rw [hsin, hcos, htan]
  have hsec : (laplaceLimit / φ)⁻¹ + 1 / laplaceLimit = (φ + 1) / laplaceLimit := by
    field_simp [hφpos.ne']
  rw [hsec, hlog]
  field_simp [hφpos.ne']

end Pconstructible
