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

import Pptc.ThirdKindAll.Standard
import Pptc.ThirdKindAll.ModulusZero
import Pptc.ThirdKindAll.ModulusOne
import Pptc.ThirdKindAll.ModulusImag
import Pptc.ThirdKindAll.ModulusRecip

/-! # Pptc.ThirdKindAll.Main

The incomplete third-kind integral is P-constructible for every real modulus and
characteristic, everywhere the integral is defined.

The proof splits on the modulus:

* `c < 0` — imaginary-modulus transformation (`ModulusImag`),
* `c = 0` — elementary antiderivative (`ModulusZero`),
* `0 < c < 1` — the standard case (`Standard`),
* `c = 1` — elementary antiderivative (`ModulusOne`),
* `c > 1` — reciprocal-modulus transformation (`ModulusRecip`),

the last two requiring that the path not meet a branch point of `Δ`. -/

namespace Pconstructible

/-- **The incomplete third-kind integral is P-constructible for every real characteristic.**

The modulus no-pole hypothesis `hmod` says that `[0, Φ]` avoids the branch point of
`Δ(θ) = √(1 - c sin²θ)`, i.e. the point where `1 - c sin²θ = 0`. It is automatic for
`c < 1`, and for `c ≥ 1` it is exactly the condition under which the integral is a
genuine (improper-free) elliptic integral. -/
theorem ellipticPiInc_Pconstructible {c n Φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc c n Φ) := by
  rcases lt_trichotomy c 0 with hcneg | hczero | hcpos
  · exact ellipticPiInc_Pconstructible_imag hcP hnP hΦP hcneg hne
  · subst hczero
    exact ellipticPiInc_zero_modulus_Pconstructible hnP hΦP hne
  · rcases lt_trichotomy c 1 with hc1 | hcone | hc1
    · exact ellipticPiInc_Pconstructible_standard hcP hnP hΦP hcpos hc1 hne
    · subst hcone
      exact ellipticPiInc_one_modulus_Pconstructible hnP hΦP hmod hne
    · exact ellipticPiInc_Pconstructible_recip hcP hnP hΦP hc1 hmod hne

end Pconstructible
