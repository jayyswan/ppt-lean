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

import Pptc.TotallyReal.Engines
import Pptc.TotallyReal.Newton
import Pptc.TotallyReal.YSpace
import Pptc.TotallyReal.Certificate
import Pptc.TotallyReal.Main

/-! # Pptc.TotallyReal

Totally real septics and octics over the P-constructible reals, following
`Pptc/TotallyReal/PLAN.md`.

The headline results are `root_Pconstructible_deg7_coeffs` and
`root_Pconstructible_totallyReal_eight` in `Pptc/TotallyReal/Main`: every real root of a
polynomial of degree `≤ 7` whose coefficients are P-constructible is P-constructible, and
every real root of a totally real (splitting) octic with P-constructible coefficients is
P-constructible. The new case is the totally real one; `Pptc.DegreeSeven` already handles
septics with a nonreal root and non-separable septics. Octics with a nonreal root are not
covered — see `PLAN.md` §5.

The files, in dependency order:

| file | content |
|---|---|
| `Engines` | quartic graphs are drawable (Lemma Q); `t·R(t²) = c` and `Q(t²) = c·t` are solvable (Lemmas E7, E8) |
| `Newton` | vanishing odd power sums ⟹ vanishing odd `esymm` (Lemma N); the two resolvent shapes |
| `YSpace` | the generic companion matrix; power sums and symmetric moments of y-vectors are P-constructible; density |
| `Certificate` | the four-step odd Tschirnhaus chain, its algebra, Lemma C, and the exact rational certificates |
| `Main` | Theorem 7 and Theorem 8 |
-/
