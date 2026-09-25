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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The half-Beta integral

`B(α, β) = ∫₀¹ t ^ (α - 1) (1 - t) ^ (β - 1) dt` is Mathlib's Beta integral, and the
route to `Γ` at every rational runs through the *half* of it that sits on `(0, 1/2)`:

    halfBeta α β = ∫_{(0,1/2)} t ^ (α - 1) (1 - t) ^ (β - 1) dt.

The point of the half is that it is the side the single substitution
`t = x ^ σ / (1 + x ^ σ)` reaches, and that substitution turns it into a power-law arc
length — no improper integral, and no Beta integral of the second kind, is needed.
Reflecting the other half (`t ↦ 1 - t`) recovers the full `B(α, β)` as
`halfBeta α β + halfBeta β α`, which `Pptc.GammaRational.BetaSplit` does.

This file only fixes the definition; the analyses live in the sibling modules. -/

namespace Pconstructible

/-- The Beta integrand integrated over the left half `(0, 1/2)` of `[0, 1]`. -/
noncomputable def halfBeta (α β : ℝ) : ℝ :=
  ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (α - 1) * (1 - t) ^ (β - 1)

end Pconstructible
