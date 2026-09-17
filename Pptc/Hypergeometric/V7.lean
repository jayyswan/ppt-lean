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
-- `Heun` supplies the pulled-back left-hand series `phiSeries` and the uniqueness of
-- solutions of its Heun equation; `HeunMobius` supplies the right-hand series `rSeries`
-- (the Möbius pullback of `₂F₁(1/2,1/2;1;·)` times the `(1+X)^(-1/2)` prefactor) and the
-- fact that it solves the same equation.
import Pptc.Hypergeometric.Heun
import Pptc.Hypergeometric.HeunMobius

open scoped PowerSeries

namespace Pconstructible

noncomputable section

/-! # Pptc.Hypergeometric.V7

The formal-power-series form of Goursat's quartic transformation (V7 of
`PLAN-hypergeometric-00-overview.md`):

`phiSeries = rSeries`, where `phiSeries = ₂F₁(1/4,3/4;1;X²)` is the `w = √z` pullback of the
left-hand `(1/4, 3/4; 1)` series and `rSeries = (1+X)^(-1/2) · ₂F₁(1/2,1/2;1;2X/(1+X))` is the
right-hand side, both as formal power series in `w = X`. This is the coefficient identity
underlying V7, and it is a consequence of the two halves of `Heun` / `HeunMobius`:
`phiSeries` and `rSeries` both solve the Heun equation

`X(1 − X²) F'' + (1 − 3X²) F' − (3/4) X F = 0`

and both have constant term `1`, so `heun_uniqueness` identifies them. The analytic transfer
from this coefficient identity to the real statement of V7 is a separate step. -/

/-- The formal-power-series form of Goursat's V7: the `w = √z` pullback of
`₂F₁(1/4,3/4;1;·)` equals `(1+X)^(-1/2)` times the Möbius pullback of `₂F₁(1/2,1/2;1;·)`. -/
-- Theorem: `phiSeries = rSeries` (formal Goursat transformation).
theorem phiSeries_eq_rSeries : phiSeries = rSeries :=
  heun_uniqueness phiSeries_heun rSeries_heun (by rw [coeff_zero_phiSeries, coeff_zero_rSeries])

end

end Pconstructible
