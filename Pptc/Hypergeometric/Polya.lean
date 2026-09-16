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
-- `Pptc.Gamma` supplies the four level-`24` Gamma values, and it is heavy — the whole
-- `Γ(1/24), Γ(5/24), Γ(7/24), Γ(11/24)` package lives there; that cost is expected.
import Pptc.Basic
import Pptc.Gamma

/-! # Pptc.Hypergeometric.Polya

Pólya's cubic-lattice constant `u(3)` and the return probability `p(3)` of the simple
cubic random walk, together with the classical K-form of the same number.

## The two shapes of the same number

The literature (Glasser–Zucker 1977) records two closed forms for the cubic-lattice
constant, agreeing to 67 digits:

* the Gamma product
  `u(3) = (√6 / (32 π³)) · Γ(1/24) Γ(5/24) Γ(7/24) Γ(11/24)`, and
* the complete-elliptic-integral form
  `u(3) = (12 / π²)(18 + 12√2 − 10√3 − 7√6) · K(k₆)²`,
  where `k₆ = (2 − √3)(√3 − √2)` is the root of `x⁴ + 12x³ + 2x² − 12x + 1` lying in
  `(0, 1)`.

The two definitions `polyaReturn3` and `polyaReturn3K` below encode these two expressions
*independently*. Their equality is a classical identity (Glasser–Zucker) that is not in
Mathlib; we deliberately do **not** assert it and introduce no axiom for it. What is
proved here is only that each expression is `PConstructible`, which the two separate
theorems `polyaReturn3_Pconstructible` and `polyaReturn3K_Pconstructible` record. The
docstrings name the classical result so a reader knows the two definitions denote the
same real number.

The Gamma product is reached through the level-`24` Gamma package in `Pptc.Gamma`; the
K-form through `ellipticF_pi_div_two_Pconstructible` for the complete integral, with the
side condition `k₆² < 1` discharged below by elementary estimates on `√2`, `√3`.

The same reduction gives the bcc and fcc lattice return numbers through Watson's first
and second triple integrals (Glasser–Zucker; see `NOTES-hypergeometric-R3`). The bcc
return number is `u_bcc = Γ(1/4)⁴/(4π³)`, Watson's `I₁`; the fcc return number is
`u_fcc = 9 Γ(1/3)⁶/(2^{14/3} π⁴) = 3 I₂`, where Watson's second integral
`I₂ = 3 Γ(1/3)⁶/(2^{14/3} π⁴)` is `watsonI2` below. By the classical Watson /
Glasser–Zucker evaluations these Γ expressions and the triple integrals denote the same
real numbers; that identity is named but not asserted, and only `PConstructible` of each
closed form is proved.
-/

namespace Pconstructible

noncomputable section

/-! ### The Gamma-product form of `u(3)` -/

/-- Pólya's cubic-lattice constant, in the Gamma-product form
`u(3) = (√6 / (32 π³)) · Γ(1/24) Γ(5/24) Γ(7/24) Γ(11/24)`.

By the classical Glasser–Zucker identity this equals `polyaReturn3K`; see the module
docstring. It is the expected number of visits to the origin; its reciprocal is the
*escape* probability, so the return probability is `polyaReturnProb3 = 1 - 1/u(3)`. -/
noncomputable def polyaReturn3 : ℝ :=
  Real.sqrt 6 / (32 * Real.pi ^ 3) *
    (Real.Gamma (1 / 24) * Real.Gamma (5 / 24) * Real.Gamma (7 / 24) *
      Real.Gamma (11 / 24))

-- Theorem: the cubic-lattice constant `u(3)` is P-constructible.
theorem polyaReturn3_Pconstructible : PConstructible polyaReturn3 := by
  unfold polyaReturn3
  pconstructible

/-- The return probability of the simple cubic random walk,
`p(3) = 1 − 1/u(3)`. -/
noncomputable def polyaReturnProb3 : ℝ := 1 - (polyaReturn3)⁻¹

-- Theorem: the cubic-lattice return probability `p(3)` is P-constructible.
theorem polyaReturnProb3_Pconstructible : PConstructible polyaReturnProb3 := by
  unfold polyaReturnProb3
  refine PConstructible.sub PConstructible.base_one ?_
  rw [inv_eq_one_div]
  exact PConstructible.div PConstructible.base_one polyaReturn3_Pconstructible

/-! ### The K-form of `u(3)`

`k₆ = (2 − √3)(√3 − √2)` is the small positive root of the quartic
`x⁴ + 12x³ + 2x² − 12x + 1`; being in `(0, 1)` it makes `k₆² < 1`, exactly the domain
condition of `ellipticF_pi_div_two_Pconstructible`. -/

/-- The auxiliary modulus `k₆ = (2 − √3)(√3 − √2)`, the root in `(0, 1)` of
`x⁴ + 12x³ + 2x² − 12x + 1` (see `k6_quartic`). -/
noncomputable def k6 : ℝ := (2 - Real.sqrt 3) * (Real.sqrt 3 - Real.sqrt 2)

-- Theorem: the modulus `k₆` is P-constructible.
theorem k6_Pconstructible : PConstructible k6 := by
  unfold k6
  pconstructible

-- Theorem: `k₆ ∈ (0, 1)`, hence `k₆² < 1`. `2 − √3` and `√3 − √2` both lie in `(0, 1)`
-- (`√3 ∈ (1, 2)`, `√2 > 1`), so their product does too.
theorem k6_sq_lt_one : k6 ^ 2 < 1 := by
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs3lt2 : Real.sqrt 3 < 2 := by nlinarith
  have hs2gt1 : 1 < Real.sqrt 2 := by nlinarith
  have hs3gt1 : 1 < Real.sqrt 3 := by nlinarith
  have hs23 : Real.sqrt 2 < Real.sqrt 3 := by nlinarith
  have hA : 2 - Real.sqrt 3 < 1 := by linarith
  have hB : Real.sqrt 3 - Real.sqrt 2 < 1 := by nlinarith
  have hpA : 0 < 2 - Real.sqrt 3 := by linarith
  have hpB : 0 < Real.sqrt 3 - Real.sqrt 2 := by linarith
  unfold k6
  have hk6pos : 0 < (2 - Real.sqrt 3) * (Real.sqrt 3 - Real.sqrt 2) := mul_pos hpA hpB
  have hk6lt1 : (2 - Real.sqrt 3) * (Real.sqrt 3 - Real.sqrt 2) < 1 := by
    calc (2 - Real.sqrt 3) * (Real.sqrt 3 - Real.sqrt 2)
        < 1 * (Real.sqrt 3 - Real.sqrt 2) := mul_lt_mul_of_pos_right hA hpB
      _ < 1 * 1 := mul_lt_mul_of_pos_left hB (by norm_num)
      _ = 1 := by ring
  have h1mk : 0 < 1 - (2 - Real.sqrt 3) * (Real.sqrt 3 - Real.sqrt 2) := by linarith
  have hmul := mul_pos hk6pos h1mk
  nlinarith [hmul, hk6lt1]

-- Theorem: `k₆` satisfies its defining quartic `x⁴ + 12x³ + 2x² − 12x + 1 = 0`.
--
-- The quartic factors as `(x² + (6 + 4√2)x − 1)(x² + (6 − 4√2)x − 1)`; the root `k₆`
-- satisfies the first quadratic factor (the local `hq`). Multiplying that quadratic by
-- `x²` and by `x`, and using `(6 + 4√2)² − 12(6 + 4√2) + 4 = 0`, recovers the quartic.
theorem k6_quartic : k6 ^ 4 + 12 * k6 ^ 3 + 2 * k6 ^ 2 - 12 * k6 + 1 = 0 := by
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : k6 ^ 2 + (6 + 4 * Real.sqrt 2) * k6 - 1 = 0 := by
    unfold k6
    linear_combination (Real.sqrt 3 ^ 2 - 4) * hs2sq
      + (3 + 4 * Real.sqrt 2 - 4 * Real.sqrt 3 - 2 * Real.sqrt 2 * Real.sqrt 3
          + Real.sqrt 3 ^ 2) * hs3sq
  have hb : k6 ^ 3 + (6 + 4 * Real.sqrt 2) * k6 ^ 2 - k6 = 0 := by
    linear_combination k6 * hq
  have ha : k6 ^ 4 + (6 + 4 * Real.sqrt 2) * k6 ^ 3 - k6 ^ 2 = 0 := by
    linear_combination k6 ^ 2 * hq
  have hc : (6 + 4 * Real.sqrt 2) ^ 2 - 12 * (6 + 4 * Real.sqrt 2) + 4 = 0 := by
    nlinarith [hs2sq]
  linear_combination ha + (12 - (6 + 4 * Real.sqrt 2)) * hb - hq + k6 ^ 2 * hc

/-- Pólya's cubic-lattice constant in the complete-elliptic-integral form
`u(3) = (12 / π²)(18 + 12√2 − 10√3 − 7√6) · K(k₆)²`, with `K = ellipticF k₆² (π/2)`.

By the classical Glasser–Zucker identity this equals `polyaReturn3`; see the module
docstring. The definition is kept separate from `polyaReturn3` on purpose — the equality
is a classical theorem not available in Mathlib. -/
noncomputable def polyaReturn3K : ℝ :=
  12 / Real.pi ^ 2 * (18 + 12 * Real.sqrt 2 - 10 * Real.sqrt 3 - 7 * Real.sqrt 6) *
    (ellipticF (k6 ^ 2) (Real.pi / 2)) ^ 2

-- Theorem: the K-form of the cubic-lattice constant `u(3)` is P-constructible.
theorem polyaReturn3K_Pconstructible : PConstructible polyaReturn3K := by
  have hF : PConstructible (ellipticF (k6 ^ 2) (Real.pi / 2)) :=
    ellipticF_pi_div_two_Pconstructible (sq_Pconstructible k6_Pconstructible) k6_sq_lt_one
  unfold polyaReturn3K
  exact PConstructible.mul
    (PConstructible.mul
      (PConstructible.div (by pconstructible) (sq_Pconstructible pi_Pconstructible))
      (by pconstructible))
    (sq_Pconstructible hF)

/-! ### The bcc and fcc Watson constants

The bcc and fcc return numbers are the Γ forms of Watson's first and second triple
integrals; see the module docstring. The factor of three between `watsonI2` and
`fccReturn3` is the `1/(1/3)` coming from the fcc structure factor. -/

/-- The bcc-lattice return number `u_bcc = Γ(1/4)⁴/(4 π³)`, which is Watson's first
triple integral `I₁` (Glasser–Zucker; OEIS A091670). -/
noncomputable def bccReturn3 : ℝ := Real.Gamma (1 / 4) ^ 4 / (4 * Real.pi ^ 3)

-- Theorem: the bcc-lattice return number `u_bcc` is P-constructible.
theorem bccReturn3_Pconstructible : PConstructible bccReturn3 := by
  unfold bccReturn3
  pconstructible

/-- The return probability of the bcc random walk, `p_bcc = 1 − 1/u_bcc`. -/
noncomputable def bccReturnProb3 : ℝ := 1 - (bccReturn3)⁻¹

-- Theorem: the bcc return probability `p_bcc` is P-constructible.
theorem bccReturnProb3_Pconstructible : PConstructible bccReturnProb3 := by
  unfold bccReturnProb3
  refine PConstructible.sub PConstructible.base_one ?_
  rw [inv_eq_one_div]
  exact PConstructible.div PConstructible.base_one bccReturn3_Pconstructible

/-- Watson's second triple integral `I₂ = 3 Γ(1/3)⁶/(2^{14/3} π⁴)` (OEIS A091671).
It is *not* the fcc return number: `fccReturn3 = 3 I₂`. -/
noncomputable def watsonI2 : ℝ :=
  3 * Real.Gamma (1 / 3) ^ 6 / (2 ^ (14 / 3 : ℝ) * Real.pi ^ 4)

-- Theorem: Watson's second triple integral `I₂` is P-constructible.
theorem watsonI2_Pconstructible : PConstructible watsonI2 := by
  unfold watsonI2
  pconstructible

/-- The fcc-lattice return number `u_fcc = 9 Γ(1/3)⁶/(2^{14/3} π⁴) = 3 I₂` (Watson;
escape probability OEIS A293237). -/
noncomputable def fccReturn3 : ℝ :=
  9 * Real.Gamma (1 / 3) ^ 6 / (2 ^ (14 / 3 : ℝ) * Real.pi ^ 4)

-- Theorem: the fcc-lattice return number `u_fcc` is P-constructible.
theorem fccReturn3_Pconstructible : PConstructible fccReturn3 := by
  unfold fccReturn3
  pconstructible

/-- The return probability of the fcc random walk, `p_fcc = 1 − 1/u_fcc`. -/
noncomputable def fccReturnProb3 : ℝ := 1 - (fccReturn3)⁻¹

-- Theorem: the fcc return probability `p_fcc` is P-constructible.
theorem fccReturnProb3_Pconstructible : PConstructible fccReturnProb3 := by
  unfold fccReturnProb3
  refine PConstructible.sub PConstructible.base_one ?_
  rw [inv_eq_one_div]
  exact PConstructible.div PConstructible.base_one fccReturn3_Pconstructible

end

end Pconstructible
