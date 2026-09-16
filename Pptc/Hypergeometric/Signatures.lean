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
-- `Pptc.Basic` supplies `sqrt_Pconstructible` and `rpow_Pconstructible`;
-- `Pptc.Hypergeometric.Elliptic` supplies `hyp` and the elliptic corollary
-- `hyp_half_half_one_Pconstructible`. `Mathlib.Analysis.Real.Sqrt` gives `Real.sqrt_lt'`.
import Pptc.Basic
import Pptc.Hypergeometric.Elliptic
import Mathlib.Analysis.Real.Sqrt

/-! # Pptc.Hypergeometric.Signatures

The quartic Ramanujan signature `₂F₁(1/4, 3/4; 1; z)` (H5, `PLAN-hypergeometric-00-overview`
§2 V7 and §4 H5). The identity that reaches it is Goursat's quadratic transformation

`₂F₁(¼, ¾; 1; z) = (1 + √z)^(−½) · ₂F₁(½, ½; 1; 2√z / (1 + √z))`,   (`V7`)

for `0 ≤ z < 1`, verified numerically to 59 digits (`NOTES-hypergeometric-R2` §1). Its
right-hand side is built from `hyp (1/2) (1/2) 1`, which is P-constructible at every
P-constructible argument of modulus below one (`hyp_half_half_one_Pconstructible`), and from
the real power `(1 + √z)^(−½)`, which is P-constructible by `rpow_Pconstructible`. So `V7`
is exactly what makes the quartic signature P-constructible.

## Why the identity is assumed, not proved

`V7` is a quadratic transformation of the Gauss function. Mathlib has no quadratic
transformations, and this one is *not* a consequence of the one that is available: the
symmetric transform of `Pptc.Hypergeometric.Quadratic` (`V6`) relates
`₂F₁(½,½;1;·)` to `₂F₁(¼,¼;1;·)`, whereas `V7` relates `₂F₁(½,½;1;·)` to `₂F₁(¼,¾;1;·)`.
Combining `V6` with Pfaff/Euler moves the argument and changes the prefactor to
`(1 − z)^{−1/4}` (or `(1 − z)^{−3/4}`), never `(1 + √z)^{−1/2}`, and the numerical check in
`HANDOFF-hypergeometric-L9.md` confirms that the two are different functions. A proof of
`V7` therefore has to be a fresh coefficient identity.

The natural route is a `HasSum`-level coefficient computation, as the task describes:
substitute `z = w²` with `w ≥ 0`, so that
`₂F₁(¼,¾;1;w²) = ∑ₙ hypCoeff (¼)(¾)1 n · w^(2n)`, while
`(1+w)^(−½)·₂F₁(½,½;1;2w/(1+w)) = ∑ₙ hypCoeff (½)(½)1 n · 2^n w^n (1+w)^(−n−½)`,
and match coefficients using the binomial expansion of `(1+w)^(−n−½)`. Equivalently one
shows `(1+w)^(½)·₂F₁(¼,¾;1;w²)` and `₂F₁(½,½;1;2w/(1+w))` satisfy the same second-order ODE
in `w` with the same initial terms. Both are genuine holonomic identities (a
Vandermonde-type finite sum for the coefficient form, a Heun-type equation for the ODE
form) and neither is discharged by `hypCoeff_succ` alone, so `V7` is left as the explicit
hypothesis of the theorem below; the reduction itself is unconditional.

## What is landed

`hyp_quarter_three_quarter_Pconstructible` is the plan's L9 statement *with* `V7` as an
explicit hypothesis. Its proof only uses the closure of `PConstructible` under `+ - * /`,
`Real.sqrt`, real powers and the elliptic corollary, so it closes the moment `V7` is proved
in the form `hyp (1/4) (3/4) 1 z = (1 + √z)^(−½) · hyp (1/2) (1/2) 1 (2√z/(1+√z))`.
-/

open scoped Topology

namespace Pconstructible

noncomputable section

/-! ### The quartic change of variable `w ↦ 2w/(1+w)`

For `0 ≤ w < 1` the map `w ↦ 2w/(1+w)` is the increasing bijection `[0,1) → [0,1)` that
appears on the right of `V7`. It stays inside the unit disc, which is what
`hyp_half_half_one_Pconstructible` needs. -/

-- Theorem: `0 ≤ w < 1` gives `2w/(1+w) < 1`.
theorem two_mul_div_one_add_lt_one {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    2 * w / (1 + w) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

-- Theorem: `0 ≤ w < 1` gives `|2w/(1+w)| < 1`.
theorem abs_two_mul_div_one_add_lt_one {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    |2 * w / (1 + w)| < 1 := by
  rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
  exact two_mul_div_one_add_lt_one hw0 hw1

/-! ### The quartic signature, conditional on `V7`

The hypothesis `hV7` is exactly Goursat's quadratic transformation stated for the given `z`
(see the module docstring). Everything else is unconditional. -/

-- Theorem (L9, conditional on Goursat's V7): if
-- `₂F₁(1/4,3/4;1;z) = (1+√z)^(-1/2) * ₂F₁(1/2,1/2;1; 2√z/(1+√z))`, then the quartic
-- signature is P-constructible for P-constructible `0 ≤ z < 1`.
-- Deliberately *not* tagged `@[pconstructible_cond]`: `hV7` is an unproved transcendental
-- identity, not a side condition. Tagged, it would register an Aesop rule whose side goal
-- goes to `Pconstructible.sideTac` (`norm_num`/`positivity`), which cannot ever discharge
-- it, so every `pconstructible` call would explore a branch that must fail. Tag it once
-- `V7` is proved and the hypothesis disappears.
theorem hyp_quarter_three_quarter_Pconstructible {z : ℝ} (hz : PConstructible z)
    (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hV7 : hyp (1 / 4) (3 / 4) 1 z
      = (1 + Real.sqrt z) ^ (-(1 / 2 : ℝ))
        * hyp (1 / 2) (1 / 2) 1 (2 * Real.sqrt z / (1 + Real.sqrt z))) :
    PConstructible (hyp (1 / 4) (3 / 4) 1 z) := by
  have hw0 : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z
  have hw1 : Real.sqrt z < 1 := by
    rw [Real.sqrt_lt hz0 zero_le_one]
    simpa using hz1
  have hargP : PConstructible (2 * Real.sqrt z / (1 + Real.sqrt z)) := by pconstructible
  have hargabs : |2 * Real.sqrt z / (1 + Real.sqrt z)| < 1 :=
    abs_two_mul_div_one_add_lt_one hw0 hw1
  have hbase : PConstructible (1 + Real.sqrt z) := by pconstructible
  have hexp : PConstructible (-(1 / 2 : ℝ)) := by pconstructible
  have hpowP : PConstructible ((1 + Real.sqrt z) ^ (-(1 / 2 : ℝ))) :=
    rpow_Pconstructible hbase hexp (by positivity)
  rw [hV7]
  exact PConstructible.mul hpowP (hyp_half_half_one_Pconstructible hargP hargabs)

end

end Pconstructible
