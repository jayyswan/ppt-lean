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
-- `Gauss` supplies the lifted summation theorem `hyp_one_eq_Gamma'`; `GammaRational`
-- the unconditional P-constructibility of `Γ(q)` at every rational `q`.
import Pptc.Hypergeometric.Gauss
import Pptc.GammaRational

/-! # Pptc.Hypergeometric.GaussRational

Gauss's summation theorem at rational parameters,

`₂F₁(a, b; c; 1) = Γ(c) Γ(c − a − b) / (Γ(c − a) Γ(c − b))`,

turns the value at `z = 1` into a quotient of four `Γ` values. At rational `a, b, c` all four
arguments are rational, so `Gamma_rat_Pconstructible` makes every factor P-constructible, and
`PConstructible.div` finishes the job. This is the same argument as the denominator-`24`
family `hyp_one_Pconstructible_of_den_24` in `Gauss.lean`; the only change is that rational
`Γ` values are now available unconditionally rather than just at multiples of `1/24`.

The hypotheses are exactly those of `hyp_one_eq_Gamma'`: `c − a − b > 0` for convergence at
the summation point, and `c`, `c − a`, `c − b` not nonpositive integers so that the four
Gamma values are finite and nonzero.
-/

namespace Pconstructible

noncomputable section

-- Theorem: `₂F₁(a, b; c; 1)` is P-constructible for all rational `a, b, c` with
-- `c − a − b > 0` and none of `c`, `c − a`, `c − b` a nonpositive integer.
theorem hyp_one_rat_Pconstructible {a b c : ℚ} (h : (0 : ℝ) < c - a - b)
    (hca : ∀ n : ℕ, (c : ℝ) - a ≠ -(n : ℝ)) (hcb : ∀ n : ℕ, (c : ℝ) - b ≠ -(n : ℝ))
    (hc : ∀ n : ℕ, (c : ℝ) ≠ -(n : ℝ)) :
    PConstructible (hyp (a : ℝ) b c 1) := by
  rw [hyp_one_eq_Gamma' h hca hcb hc]
  rw [show (c : ℝ) - a - b = ((c - a - b : ℚ) : ℝ) by push_cast; ring,
    show (c : ℝ) - a = ((c - a : ℚ) : ℝ) by push_cast; ring,
    show (c : ℝ) - b = ((c - b : ℚ) : ℝ) by push_cast; ring]
  exact PConstructible.div
    (PConstructible.mul (Gamma_rat_Pconstructible c) (Gamma_rat_Pconstructible (c - a - b)))
    (PConstructible.mul (Gamma_rat_Pconstructible (c - a)) (Gamma_rat_Pconstructible (c - b)))

end

end Pconstructible
