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

/-! ### The cubic and sextic Ramanujan signature reductions (H5)

The quartic `V7` above is one of the four Ramanujan signatures. R2
(`NOTES-hypergeometric-R2` §2, §3) supplies two more as *parametric* transformations of
`₂F₁(1/2,1/2;1;·)`, each classical and verified numerically to 79 digits:

* cubic (Ramanujan, 2nd notebook p. 258; Berndt–Bhargava–Garvan Thm 5.6): for `p ∈ [0,1)`,
  `₂F₁(1/3,2/3;1; β(p)) = γ(p) · ₂F₁(1/2,1/2;1; α(p))`;
* sextic (Shen 2013; Robinson Thm 8): for `p ∈ [0,1)`,
  `₂F₁(1/6,5/6;1; ξ(p)) = (1 − x(p) + x(p)²)^{1/4} · ₂F₁(1/2,1/2;1; x(p))`,

with the explicit rational functions below. Both have `V7`'s shape — the right side is the
already-P-constructible family `hyp_half_half_one_Pconstructible` times a prefactor built from
square roots and rational functions.

## Why the identities are hypotheses

As with `V7`, Mathlib has no proof of either transformation, so each theorem below states the
transformation for the given `p` as an explicit hypothesis `hCubic` / `hSextic` and proves the
*reduction* — P-constructibility of `p` makes the left-hand signature P-constructible —
unconditionally. The conditional theorems are deliberately **not** tagged
`@[pconstructible_cond]`: their identity hypothesis is not a dischargeable side condition
(`sideTac` is `assumption`/`norm_num`/`positivity`/`linarith`), so a tag would only register a
branch that must always fail. The *unconditional* closure results — the argument and prefactor
functions are P-constructible whenever `p` is — do carry the tag.

## Why `p` is kept parametric

R2 §4 records that the argument maps have degree 6 and the prefactors degree 12 over `ℚ(z)`.
Eliminating `p` (a cubic, then a fourth root) is unnecessary for the closure statement, and the
parametric form uses only square roots, so the reduction stays parametric exactly as R2
verified it. -/

/-! #### The parametric functions -/

/-- Cubic argument `k² = α(p) = p³(2+p)/(1+2p)`. -/
noncomputable def α (p : ℝ) : ℝ := p ^ 3 * (2 + p) / (1 + 2 * p)

/-- Cubic signature argument `z = β(p) = 27p²(1+p)²/(4(1+p+p²)³)`. -/
noncomputable def β (p : ℝ) : ℝ :=
  27 * p ^ 2 * (1 + p) ^ 2 / (4 * (1 + p + p ^ 2) ^ 3)

/-- Cubic prefactor `γ(p) = (1+p+p²)/√(1+2p)`. -/
noncomputable def γ (p : ℝ) : ℝ := (1 + p + p ^ 2) / Real.sqrt (1 + 2 * p)

/-- Sextic argument `k² = x(p) = p(2+p)/(1+2p)`. -/
noncomputable def x (p : ℝ) : ℝ := p * (2 + p) / (1 + 2 * p)

/-- Sextic signature argument `z = ξ(p) = (27/4)p²(1+p)²/(1+p+p²)³`. -/
noncomputable def ξ (p : ℝ) : ℝ :=
  27 / 4 * p ^ 2 * (1 + p) ^ 2 / (1 + p + p ^ 2) ^ 3

/-- Sextic prefactor `(1-x+x²)^{1/4} = √(1+p+p²)/√(1+2p)`. -/
noncomputable def sexticPrefactor (p : ℝ) : ℝ :=
  Real.sqrt (1 + p + p ^ 2) / Real.sqrt (1 + 2 * p)

/-! #### The parametric domain `0 ≤ p < 1` -/

-- Theorem: `1 + 2p > 0` for `0 ≤ p`.
theorem one_add_two_mul_pos {p : ℝ} (hp0 : 0 ≤ p) : 0 < 1 + 2 * p := by linarith

-- Theorem: `1 + p + p² > 0` for `0 ≤ p`.
theorem one_add_add_sq_pos {p : ℝ} (hp0 : 0 ≤ p) : 0 < 1 + p + p ^ 2 := by
  nlinarith [sq_nonneg p]

/-! #### The arguments lie in `[0, 1)`

`α`, `β`, `x`, `ξ` are increasing from `0` to `1` on `[0,1)` (R2 §2.1, §3.1). Only the
bounds matter here: `hyp_half_half_one_Pconstructible` needs its argument in the unit disc,
and the two series converge absolutely for arguments in `[0,1)`. The `< 1` bounds are the
factorisations `1 + 2p - p³(2+p) = (1-p)(1+p)³` and
`4(1+p+p²)³ - 27p²(1+p)² = (1-p)²(4p⁴+20p³+33p²+20p+4) ≥ 0`. -/

-- Theorem: `0 ≤ α p` for `0 ≤ p`.
theorem α_nonneg {p : ℝ} (hp0 : 0 ≤ p) : 0 ≤ α p := by
  unfold α
  exact div_nonneg (mul_nonneg (pow_nonneg hp0 3) (by linarith)) (by linarith)

-- Theorem: `α p < 1` for `0 ≤ p < 1`.
theorem α_lt_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : α p < 1 := by
  have hden : 0 < 1 + 2 * p := one_add_two_mul_pos hp0
  rw [α, div_lt_one hden]
  have hfac : 1 + 2 * p - p ^ 3 * (2 + p) = (1 - p) * (1 + p) ^ 3 := by ring
  have hpos : 0 < (1 - p) * (1 + p) ^ 3 :=
    mul_pos (by linarith) (pow_pos (by linarith) 3)
  linarith

-- Theorem: `0 ≤ β p` for `0 ≤ p`.
theorem β_nonneg {p : ℝ} (hp0 : 0 ≤ p) : 0 ≤ β p := by
  unfold β
  have hq : 0 < 1 + p + p ^ 2 := one_add_add_sq_pos hp0
  exact div_nonneg (by positivity) (mul_nonneg (by norm_num) (pow_nonneg hq.le 3))

-- Theorem: `β p < 1` for `0 ≤ p < 1`.
theorem β_lt_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : β p < 1 := by
  have hq : 0 < 1 + p + p ^ 2 := one_add_add_sq_pos hp0
  have hden : 0 < 4 * (1 + p + p ^ 2) ^ 3 :=
    mul_pos (by norm_num) (pow_pos hq 3)
  rw [β, div_lt_one hden]
  have hfac : 4 * (1 + p + p ^ 2) ^ 3 - 27 * p ^ 2 * (1 + p) ^ 2 =
      (1 - p) ^ 2 * (4 * p ^ 4 + 20 * p ^ 3 + 33 * p ^ 2 + 20 * p + 4) := by ring
  have hpos : 0 < (1 - p) ^ 2 * (4 * p ^ 4 + 20 * p ^ 3 + 33 * p ^ 2 + 20 * p + 4) := by
    refine mul_pos (pow_pos (by linarith) 2) ?_
    nlinarith [sq_nonneg p, pow_nonneg hp0 3, pow_nonneg hp0 4]
  linarith

-- Theorem: `0 ≤ x p` for `0 ≤ p`.
theorem x_nonneg {p : ℝ} (hp0 : 0 ≤ p) : 0 ≤ x p := by
  unfold x
  exact div_nonneg (mul_nonneg hp0 (by linarith)) (by linarith)

-- Theorem: `x p < 1` for `0 ≤ p < 1`.
theorem x_lt_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : x p < 1 := by
  have hden : 0 < 1 + 2 * p := one_add_two_mul_pos hp0
  have hpp : p * p < 1 := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h]; norm_num
    · have h2 := mul_lt_mul_of_pos_left hp1 h
      rw [mul_one] at h2
      linarith
  rw [x, div_lt_one hden]
  nlinarith [hpp]

-- Theorem: `0 ≤ ξ p` for `0 ≤ p`.
theorem ξ_nonneg {p : ℝ} (hp0 : 0 ≤ p) : 0 ≤ ξ p := by
  unfold ξ
  have hq : 0 < 1 + p + p ^ 2 := one_add_add_sq_pos hp0
  exact div_nonneg (by positivity) (pow_nonneg hq.le 3)

-- Theorem: `ξ p < 1` for `0 ≤ p < 1`.
theorem ξ_lt_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : ξ p < 1 := by
  have hq : 0 < 1 + p + p ^ 2 := one_add_add_sq_pos hp0
  have hden : 0 < (1 + p + p ^ 2) ^ 3 := pow_pos hq 3
  rw [ξ, div_lt_one hden]
  have hfac : 4 * (1 + p + p ^ 2) ^ 3 - 27 * p ^ 2 * (1 + p) ^ 2 =
      (1 - p) ^ 2 * (4 * p ^ 4 + 20 * p ^ 3 + 33 * p ^ 2 + 20 * p + 4) := by ring
  have hpos : 0 < (1 - p) ^ 2 * (4 * p ^ 4 + 20 * p ^ 3 + 33 * p ^ 2 + 20 * p + 4) := by
    refine mul_pos (pow_pos (by linarith) 2) ?_
    nlinarith [sq_nonneg p, pow_nonneg hp0 3, pow_nonneg hp0 4]
  nlinarith [hfac, hpos]

-- Theorem: `|α p| < 1` for `0 ≤ p < 1` (the unit-disc hypothesis for the `K`-family).
theorem abs_α_lt_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : |α p| < 1 := by
  rw [abs_of_nonneg (α_nonneg hp0)]
  exact α_lt_one hp0 hp1

-- Theorem: `|x p| < 1` for `0 ≤ p < 1` (the unit-disc hypothesis for the `K`-family).
theorem abs_x_lt_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : |x p| < 1 := by
  rw [abs_of_nonneg (x_nonneg hp0)]
  exact x_lt_one hp0 hp1

/-! #### PConstructibility of the parametric functions

Each is built from `p` by `+ - * /`, integer powers and `Real.sqrt`, so the `pconstructible`
tactic closes it from `PConstructible p` alone (the radical functions are the unconditional
rule `sqrt_Pconstructible`). These are the unconditional closure results and so are tagged;
the conditional transformation theorems below are not. -/

-- Theorem: `α p` is P-constructible for P-constructible `p`.
@[pconstructible] theorem α_Pconstructible {p : ℝ} (hp : PConstructible p) :
    PConstructible (α p) := by
  unfold α
  pconstructible

-- Theorem: `β p` is P-constructible for P-constructible `p`.
@[pconstructible] theorem β_Pconstructible {p : ℝ} (hp : PConstructible p) :
    PConstructible (β p) := by
  unfold β
  pconstructible

-- Theorem: `γ p` is P-constructible for P-constructible `p`.
@[pconstructible] theorem γ_Pconstructible {p : ℝ} (hp : PConstructible p) :
    PConstructible (γ p) := by
  unfold γ
  pconstructible

-- Theorem: `x p` is P-constructible for P-constructible `p`.
@[pconstructible] theorem x_Pconstructible {p : ℝ} (hp : PConstructible p) :
    PConstructible (x p) := by
  unfold x
  pconstructible

-- Theorem: `ξ p` is P-constructible for P-constructible `p`.
@[pconstructible] theorem ξ_Pconstructible {p : ℝ} (hp : PConstructible p) :
    PConstructible (ξ p) := by
  unfold ξ
  pconstructible

-- Theorem: the sextic prefactor is P-constructible for P-constructible `p`.
@[pconstructible] theorem sexticPrefactor_Pconstructible {p : ℝ} (hp : PConstructible p) :
    PConstructible (sexticPrefactor p) := by
  unfold sexticPrefactor
  pconstructible

/-! #### The cubic signature, conditional on the RBBG transformation

`hCubic` is exactly Ramanujan's cubic transformation at the given `p` (see the module section
above). Everything else is unconditional: `γ p` and `α p` are P-constructible, and `α p` lies
in the unit disc, so `hyp_half_half_one_Pconstructible` applies to it. -/

-- Theorem (L9 cubic, conditional on the Ramanujan/BBG cubic transformation): if
-- `₂F₁(1/3,2/3;1;β p) = γ p · ₂F₁(1/2,1/2;1;α p)`, then the cubic signature is P-constructible
-- for P-constructible `0 ≤ p < 1`. Deliberately *not* tagged `@[pconstructible_cond]`:
-- `hCubic` is an unproved transcendental identity, not a side condition.
theorem hyp_one_third_two_thirds_Pconstructible {p : ℝ} (hp : PConstructible p)
    (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hCubic : hyp (1 / 3) (2 / 3) 1 (β p) = γ p * hyp (1 / 2) (1 / 2) 1 (α p)) :
    PConstructible (hyp (1 / 3) (2 / 3) 1 (β p)) := by
  rw [hCubic]
  exact PConstructible.mul (γ_Pconstructible hp)
    (hyp_half_half_one_Pconstructible (α_Pconstructible hp) (abs_α_lt_one hp0 hp1))

/-! #### The sextic signature, conditional on the Shen/Robinson transformation

The same shape, with the argument `x p` in place of `α p` and the square-root prefactor
`√(1+p+p²)/√(1+2p) = (1−x+x²)^{1/4}` in place of `γ p`. -/

-- Theorem (L9 sextic, conditional on the Shen/Robinson sextic transformation): if
-- `₂F₁(1/6,5/6;1;ξ p) = (√(1+p+p²)/√(1+2p)) · ₂F₁(1/2,1/2;1;x p)`, then the sextic signature
-- is P-constructible for P-constructible `0 ≤ p < 1`. Deliberately *not* tagged
-- `@[pconstructible_cond]`: `hSextic` is an unproved transcendental identity.
theorem hyp_one_sixth_five_sixths_Pconstructible {p : ℝ} (hp : PConstructible p)
    (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hSextic : hyp (1 / 6) (5 / 6) 1 (ξ p)
      = sexticPrefactor p * hyp (1 / 2) (1 / 2) 1 (x p)) :
    PConstructible (hyp (1 / 6) (5 / 6) 1 (ξ p)) := by
  rw [hSextic]
  exact PConstructible.mul (sexticPrefactor_Pconstructible hp)
    (hyp_half_half_one_Pconstructible (x_Pconstructible hp) (abs_x_lt_one hp0 hp1))

/-! #### The special values at `z = 1/2` (R2 §2.2, §3.4)

At `p = (√3-1)/2` both signature arguments `β` and `ξ` equal `1/2` (the cubic argument is
`α = (2-√3)/4`, the sextic argument `x = 1/2`), and the two prefactors collapse to
`3^(3/4)/2` and `(3/4)^(1/4)`. These are exactly the values B1 (`PLAN` §4) consumes, so they
are recorded from the same reduction hypotheses. The algebra below is unconditional; only the
final rewrites use the assumed transformation at the special parameter. -/

/-- The parameter giving `β(p) = ξ(p) = 1/2`: `p = (√3 - 1)/2`. -/
noncomputable def pHalf : ℝ := (Real.sqrt 3 - 1) / 2

/-! ##### The algebra at `p = (√3-1)/2`

The rational identities follow from `√3² = 3` by `nlinarith`. The two fourth-root prefactors
are reduced to `Real.rpow` identities: `√√x = x^(1/4)` (`sqrt_sqrt_eq_rpow_quarter`), then
`Real.rpow_mul`, `Real.rpow_add` and `Real.rpow_sub`. -/

-- Theorem: `√√x = x^(1/4)` for `x ≥ 0`.
theorem sqrt_sqrt_eq_rpow_quarter {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx (1 / 2 : ℝ) (1 / 2 : ℝ)]
  norm_num

-- Theorem: `(3/2)/3^(1/4) = 3^(3/4)/2`.
theorem three_div_fourth_root_eq :
    (3 / 2 : ℝ) / 3 ^ (1 / 4 : ℝ) = 3 ^ (3 / 4 : ℝ) / 2 := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [div_eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos h3 (1 / 4))) (by norm_num)]
  rw [← Real.rpow_add h3 (3 / 4 : ℝ) (1 / 4 : ℝ),
    show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one]
  norm_num

-- Theorem: `√(3/2)/√√3 = (3/4)^(1/4)`.
theorem sqrt_three_halves_div_sqrt_sqrt_three :
    Real.sqrt (3 / 2) / Real.sqrt (Real.sqrt 3) = (3 / 4 : ℝ) ^ (1 / 4 : ℝ) := by
  rw [sqrt_sqrt_eq_rpow_quarter (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_eq_rpow,
    div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (1 / 4)))]
  rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (0 : ℝ) ≤ 3),
    show (3 / 4 : ℝ) * 3 = (3 / 2) ^ 2 by norm_num]
  rw [← Real.rpow_natCast (3 / 2) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3 / 2) ((2 : ℕ) : ℝ) (1 / 4 : ℝ)]
  norm_num

-- Theorem: `β((√3-1)/2) = 1/2`.
theorem β_pHalf : β pHalf = 1 / 2 := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hu : pHalf * (1 + pHalf) = 1 / 2 := by unfold pHalf; nlinarith [hsq]
  have hq : 1 + pHalf + pHalf ^ 2 = 3 / 2 := by unfold pHalf; nlinarith [hsq]
  have hnum : 27 * pHalf ^ 2 * (1 + pHalf) ^ 2 = 27 / 4 := by
    rw [show 27 * pHalf ^ 2 * (1 + pHalf) ^ 2
        = 27 * (pHalf * (1 + pHalf)) ^ 2 by ring, hu]
    norm_num
  unfold β
  rw [hq, hnum]
  norm_num

-- Theorem: `ξ((√3-1)/2) = 1/2`.
theorem ξ_pHalf : ξ pHalf = 1 / 2 := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hu : pHalf * (1 + pHalf) = 1 / 2 := by unfold pHalf; nlinarith [hsq]
  have hq : 1 + pHalf + pHalf ^ 2 = 3 / 2 := by unfold pHalf; nlinarith [hsq]
  have hnum : 27 / 4 * pHalf ^ 2 * (1 + pHalf) ^ 2 = 27 / 16 := by
    rw [show 27 / 4 * pHalf ^ 2 * (1 + pHalf) ^ 2
        = 27 / 4 * (pHalf * (1 + pHalf)) ^ 2 by ring, hu]
    norm_num
  unfold ξ
  rw [hq, hnum]
  norm_num

-- Theorem: `x((√3-1)/2) = 1/2`.
theorem x_pHalf : x pHalf = 1 / 2 := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hl : 1 + 2 * pHalf = Real.sqrt 3 := by unfold pHalf; ring
  unfold x
  rw [hl, div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))]
  unfold pHalf
  nlinarith [hsq]

-- Theorem: `α((√3-1)/2) = (2-√3)/4`.
theorem α_pHalf : α pHalf = (2 - Real.sqrt 3) / 4 := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hl : 1 + 2 * pHalf = Real.sqrt 3 := by unfold pHalf; ring
  unfold α
  rw [hl, div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))]
  unfold pHalf
  nlinarith [hsq]

-- Theorem: `γ((√3-1)/2) = 3^(3/4)/2`.
theorem γ_pHalf : γ pHalf = (3 : ℝ) ^ (3 / 4 : ℝ) / 2 := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : 1 + pHalf + pHalf ^ 2 = 3 / 2 := by unfold pHalf; nlinarith [hsq]
  have hl : 1 + 2 * pHalf = Real.sqrt 3 := by unfold pHalf; ring
  unfold γ
  rw [hq, hl, sqrt_sqrt_eq_rpow_quarter (by norm_num : (0 : ℝ) ≤ 3)]
  exact three_div_fourth_root_eq

-- Theorem: `sexticPrefactor((√3-1)/2) = (3/4)^(1/4)`.
theorem sexticPrefactor_pHalf : sexticPrefactor pHalf = (3 / 4 : ℝ) ^ (1 / 4 : ℝ) := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : 1 + pHalf + pHalf ^ 2 = 3 / 2 := by unfold pHalf; nlinarith [hsq]
  have hl : 1 + 2 * pHalf = Real.sqrt 3 := by unfold pHalf; ring
  unfold sexticPrefactor
  rw [hq, hl]
  exact sqrt_three_halves_div_sqrt_sqrt_three

/-! ##### The special values `(★)` and `(★★)`

Both follow from the reduction hypothesis by rewriting the general left/right sides at the
special parameter with the algebra above; the transformation itself remains assumed. -/

-- Theorem ((★), R2 §2.2): from the cubic reduction at `p = (√3-1)/2`,
-- `₂F₁(1/3,2/3;1;1/2) = (3^{3/4}/2)·₂F₁(1/2,1/2;1;(2-√3)/4)`.
theorem hyp_one_third_two_thirds_half_of_reduction
    (hCubic : hyp (1 / 3) (2 / 3) 1 (β pHalf)
      = γ pHalf * hyp (1 / 2) (1 / 2) 1 (α pHalf)) :
    hyp (1 / 3) (2 / 3) 1 (1 / 2)
      = (3 : ℝ) ^ (3 / 4 : ℝ) / 2 * hyp (1 / 2) (1 / 2) 1 ((2 - Real.sqrt 3) / 4) := by
  have h := hCubic
  rw [β_pHalf, α_pHalf, γ_pHalf] at h
  exact h

-- Theorem ((★★), R2 §3.4): from the sextic reduction at `p = (√3-1)/2`,
-- `₂F₁(1/6,5/6;1;1/2) = (3/4)^{1/4}·₂F₁(1/2,1/2;1;1/2)`.
theorem hyp_one_sixth_five_sixths_half_of_reduction
    (hSextic : hyp (1 / 6) (5 / 6) 1 (ξ pHalf)
      = sexticPrefactor pHalf * hyp (1 / 2) (1 / 2) 1 (x pHalf)) :
    hyp (1 / 6) (5 / 6) 1 (1 / 2)
      = (3 / 4 : ℝ) ^ (1 / 4 : ℝ) * hyp (1 / 2) (1 / 2) 1 (1 / 2) := by
  have h := hSextic
  rw [ξ_pHalf, x_pHalf, sexticPrefactor_pHalf] at h
  exact h

end

end Pconstructible
