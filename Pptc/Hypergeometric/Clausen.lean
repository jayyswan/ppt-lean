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
-- `Quadratic` supplies the quadratic transformation `hyp_quadratic` (V6) and the power-series
-- machinery (`hypSeries`, `hypSeries_quarter_ode`) that a proof of Clausen would build on;
-- `Elliptic` supplies `hyp_half_half_one_Pconstructible`; `Pptc.Basic` supplies
-- `sqrt_Pconstructible` and `sq_Pconstructible`.
import Pptc.Hypergeometric.Quadratic
import Pptc.Hypergeometric.Elliptic
import Pptc.Basic
import Mathlib.Analysis.Real.Sqrt

/-! # Pptc.Hypergeometric.Clausen

The Clausen `₃F₂` value (B3 of `PLAN-hypergeometric-00-overview.md`, §5), the flagship
*outbound* theorem of the hypergeometric programme. Mathlib has no `₃F₂`, so the object is
stated as an explicit `tsum`:

`Σₙ C(2n,n)³ (x/64)ⁿ`,  for `x` P-constructible with `0 ≤ x < 1`.

## Why it is P-constructible

Clausen's identity writes the series as the square of the fourth Ramanujan signature,

`Σₙ C(2n,n)³ (x/64)ⁿ = ₂F₁(1/4, 1/4; 1; x)²`,

equivalently (with `z = (1 − √(1−x))/2`, so `x = 4z(1−z)`) as `(2K(z)/π)²`. The right-hand
side is P-constructible once the *fourth signature* `₂F₁(1/4,1/4;1;x)` is: the quadratic
transformation `hyp_quadratic` (V6) gives `₂F₁(1/4,1/4;1;x) = ₂F₁(1/2,1/2;1;z)` on
`0 ≤ z < 1/2`, and the elliptic corollary `hyp_half_half_one_Pconstructible` makes the latter
P-constructible. Squaring is free, because `PConstructible` is closed under multiplication.

## What is landed

The fourth Ramanujan signature — `hyp_one_fourth_one_Pconstructible` — and its square —
`hyp_one_fourth_squared_Pconstructible` — are proved P-constructible (the last piece of H5
that `Quadratic.lean` unlocked).

Clausen's identity itself is proved here unconditionally, by the ODE route. The symmetric
square `G = F²` of `F = ₂F₁(1/4,1/4;1;·)` satisfies the third-order equation
`8X²(1−X)G''' + (24X − 36X²)G'' + (8 − 26X)G' − G = 0` (`qG_ode`), and reading off the
coefficient of `X^(k+3)` gives the recurrence `8(k+4)³ g_{k+4} = (2k+7)³ g_{k+3}`, i.e.
`8(n+1)³ g_{n+1} = (2n+1)³ g_n` (`qG_coeff_rec_all`). The solution with `g₀ = 1` is
`dₙ = (C(2n,n)/4ⁿ)³ = C(2n,n)³/64ⁿ`, which has the same recurrence by the central-binomial
formula; hence `clausenCoeff_eq_coeff_qG` identifies the coefficients of `qF²` with
Clausen's `₃F₂(1/2,1/2,1/2;1,1;·)` coefficients. The analytic transfer then evaluates the
formal identity at real `|x| < 1` through the absolutely convergent Cauchy product of two
`hasSum_hyp` series (`clausen_hasSum`, `clausen_tsum_eq`), and the headline
`clausen_tsum_Pconstructible` is unconditional. -/

open scoped Topology

namespace Pconstructible

noncomputable section

/-! ### The fourth Ramanujan signature

`₂F₁(1/4,1/4;1;·)` is reached from the elliptic family by the quadratic transformation.
For `0 ≤ x < 1` the substitution `z = (1 − √(1−x))/2` is the increasing bijection
`[0,1) → [0,1/2)`, and `4z(1−z) = 1 − √(1−x)² = x`. So `hyp_quadratic` at `z` reads
`₂F₁(1/2,1/2;1;z) = ₂F₁(1/4,1/4;1;x)`, and the left side is P-constructible because
`|z| < 1`. -/

-- Theorem: `4 * ((1 - √(1-x))/2) * (1 - (1 - √(1-x))/2) = x` for `0 ≤ x ≤ 1`.
theorem four_mul_half_sub_sqrt_one_sub {x : ℝ} (hx : x ≤ 1) :
    4 * ((1 - Real.sqrt (1 - x)) / 2) * (1 - (1 - Real.sqrt (1 - x)) / 2) = x := by
  have hs2 : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  rw [show 1 - (1 - Real.sqrt (1 - x)) / 2 = (1 + Real.sqrt (1 - x)) / 2 by ring]
  rw [show 4 * ((1 - Real.sqrt (1 - x)) / 2) * ((1 + Real.sqrt (1 - x)) / 2)
      = (1 - Real.sqrt (1 - x)) * (1 + Real.sqrt (1 - x)) by ring]
  rw [show (1 - Real.sqrt (1 - x)) * (1 + Real.sqrt (1 - x))
      = 1 - Real.sqrt (1 - x) ^ 2 by ring]
  rw [hs2]
  ring

-- Theorem: `0 ≤ (1 - √(1-x))/2 ≤ 1/2` for `0 ≤ x < 1`, with the second inequality strict.
theorem half_sub_sqrt_one_sub_mem {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ (1 - Real.sqrt (1 - x)) / 2 ∧ (1 - Real.sqrt (1 - x)) / 2 < 1 / 2 := by
  have hs2 : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  have hsn : 0 ≤ Real.sqrt (1 - x) := Real.sqrt_nonneg _
  have hsle : Real.sqrt (1 - x) ≤ 1 := by nlinarith [hsn, hs2, hx0]
  have hslt : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr (by linarith)
  constructor <;> linarith

-- Theorem: `₂F₁(1/4,1/4;1;x)` is P-constructible for P-constructible `0 ≤ x < 1`
-- (the fourth Ramanujan signature).
theorem hyp_one_fourth_one_Pconstructible {x : ℝ} (hx : PConstructible x)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    PConstructible (hyp (1 / 4) (1 / 4) 1 x) := by
  obtain ⟨hz0, hz1⟩ := half_sub_sqrt_one_sub_mem hx0 hx1
  have hzP : PConstructible ((1 - Real.sqrt (1 - x)) / 2) := by pconstructible
  have hzabs : |(1 - Real.sqrt (1 - x)) / 2| < 1 := by
    rw [abs_of_nonneg hz0]
    linarith
  have hthis := hyp_half_half_one_Pconstructible hzP hzabs
  rw [hyp_quadratic hz0 hz1, four_mul_half_sub_sqrt_one_sub (le_of_lt hx1)] at hthis
  exact hthis

-- Theorem: the fourth Ramanujan signature and its square are P-constructible for
-- P-constructible `0 ≤ x < 1`.
theorem hyp_one_fourth_squared_Pconstructible {x : ℝ} (hx : PConstructible x)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    PConstructible (hyp (1 / 4) (1 / 4) 1 x)
      ∧ PConstructible ((hyp (1 / 4) (1 / 4) 1 x) ^ 2) :=
  ⟨hyp_one_fourth_one_Pconstructible hx hx0 hx1,
    sq_Pconstructible (hyp_one_fourth_one_Pconstructible hx hx0 hx1)⟩

/-! ### Route 1: the third-order equation for the symmetric square

The formal power series `F = ₂F₁(1/4,1/4;1;·)` satisfies its hypergeometric equation
`X(1−X)F'' + (1 − 3X/2)F' − F/16 = 0` (`hypSeries_quarter_ode`, rescaled). Differentiating
and eliminating `F'''` and `F''` from `G = F²` gives the third-order equation

`8X²(1−X)G''' + (24X − 36X²)G'' + (8 − 26X)G' − G = 0`.

The elimination is the integral-coefficient identity
`E₈ = X·(F·hqd) + 3X·(F'·hq) + F·hq`, where `hq` and `hqd` are the left sides of the
second-order equation and its derivative. Reading off the coefficient of `X^(k+3)` gives the
recurrence `8(k+4)³ gₖ₊₄ = (2k+7)³ gₖ₊₃`, i.e. `(n+1)³ gₙ₊₁ = (n + 1/2)³ gₙ`, whose solution
with `g₀ = 1` is `gₙ = (C(2n,n)/4ⁿ)³ = C(2n,n)³/64ⁿ`. -/

/-- The formal power series of the fourth Ramanujan signature. -/
noncomputable def qF : PowerSeries ℝ := hypSeries (1 / 4) (1 / 4) 1

/-- First derivative of `qF`. -/
noncomputable def qF1 : PowerSeries ℝ := PowerSeries.derivative ℝ qF

/-- Second derivative of `qF`. -/
noncomputable def qF2 : PowerSeries ℝ := PowerSeries.derivative ℝ qF1

/-- Third derivative of `qF`. -/
noncomputable def qF3 : PowerSeries ℝ := PowerSeries.derivative ℝ qF2

/-- The symmetric square `qF²`. -/
noncomputable def qG : PowerSeries ℝ := qF * qF

/-- First derivative of `qG`. -/
noncomputable def qG1 : PowerSeries ℝ := PowerSeries.derivative ℝ qG

/-- Second derivative of `qG`. -/
noncomputable def qG2 : PowerSeries ℝ := PowerSeries.derivative ℝ qG1

/-- Third derivative of `qG`. -/
noncomputable def qG3 : PowerSeries ℝ := PowerSeries.derivative ℝ qG2

-- Theorem: the rescaled hypergeometric equation of `₂F₁(1/4,1/4;1;·)` in the `qF` notation.
theorem qF_ode :
    16 * (PowerSeries.X * (1 - PowerSeries.X)) * qF2
      + (16 - 24 * PowerSeries.X) * qF1 - qF = 0 := by
  simpa only [qF, qF1, qF2] using hypSeries_quarter_ode

-- Theorem: the derivative of `qF_ode`, the relation `16X(1-X)F''' + (32-56X)F'' - 25F' = 0`.
theorem qF_ode_deriv :
    16 * (PowerSeries.X * (1 - PowerSeries.X)) * qF3
      + (32 - 56 * PowerSeries.X) * qF2 - 25 * qF1 = 0 := by
  have hd16 : (PowerSeries.derivative ℝ) (16 : PowerSeries ℝ) = 0 := by
    rw [show (16 : PowerSeries ℝ) = PowerSeries.C 16 from rfl, PowerSeries.derivative_C]
  have hd24 : (PowerSeries.derivative ℝ) (24 : PowerSeries ℝ) = 0 := by
    rw [show (24 : PowerSeries ℝ) = PowerSeries.C 24 from rfl, PowerSeries.derivative_C]
  have h := congrArg (PowerSeries.derivative ℝ) qF_ode
  rw [map_zero] at h
  have hexp : PowerSeries.derivative ℝ
      (16 * (PowerSeries.X * (1 - PowerSeries.X)) * qF2
        + (16 - 24 * PowerSeries.X) * qF1 - qF)
      = 16 * (PowerSeries.X * (1 - PowerSeries.X)) * qF3
        + (32 - 56 * PowerSeries.X) * qF2 - 25 * qF1 := by
    simp only [qF1, qF2, qF3, map_sub, map_add, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_X, Derivation.map_one_eq_zero, hd16, hd24]
    ring
  rw [hexp] at h
  exact h

-- Theorem: `qG1 = 2 qF qF'`.
theorem qG1_eq : qG1 = 2 * qF * qF1 := by
  simp only [qG1, qG, qF1, Derivation.leibniz, smul_eq_mul]
  ring

-- Theorem: `qG2 = 2 (qF')² + 2 qF qF''`.
theorem qG2_eq : qG2 = 2 * qF1 * qF1 + 2 * qF * qF2 := by
  have hd2 : (PowerSeries.derivative ℝ) (2 : PowerSeries ℝ) = 0 := by
    rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, PowerSeries.derivative_C]
  have h1 : qG1 = 2 * qF * qF1 := qG1_eq
  rw [qG2, h1]
  simp only [qF1, qF2, Derivation.leibniz, smul_eq_mul, hd2]
  ring

-- Theorem: `qG3 = 6 qF' qF'' + 2 qF qF'''`.
theorem qG3_eq : qG3 = 6 * qF1 * qF2 + 2 * qF * qF3 := by
  have hd2 : (PowerSeries.derivative ℝ) (2 : PowerSeries ℝ) = 0 := by
    rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, PowerSeries.derivative_C]
  have h2 : qG2 = 2 * qF1 * qF1 + 2 * qF * qF2 := qG2_eq
  rw [qG3, h2]
  simp only [qF1, qF2, qF3, map_add, Derivation.leibniz, smul_eq_mul, hd2]
  ring

-- Theorem: the third-order equation of the symmetric square,
-- `8X²(1-X)G''' + (24X - 36X²)G'' + (8 - 26X)G' - G = 0`.
theorem qG_ode :
    8 * PowerSeries.X ^ 2 * (1 - PowerSeries.X) * qG3
      + (24 * PowerSeries.X - 36 * PowerSeries.X ^ 2) * qG2
      + (8 - 26 * PowerSeries.X) * qG1 - qG = 0 := by
  have hE : 8 * PowerSeries.X ^ 2 * (1 - PowerSeries.X) * qG3
      + (24 * PowerSeries.X - 36 * PowerSeries.X ^ 2) * qG2
      + (8 - 26 * PowerSeries.X) * qG1 - qG
      = PowerSeries.X * (qF * (16 * (PowerSeries.X * (1 - PowerSeries.X)) * qF3
            + (32 - 56 * PowerSeries.X) * qF2 - 25 * qF1))
        + 3 * PowerSeries.X * (qF1 * (16 * (PowerSeries.X * (1 - PowerSeries.X)) * qF2
            + (16 - 24 * PowerSeries.X) * qF1 - qF))
        + qF * (16 * (PowerSeries.X * (1 - PowerSeries.X)) * qF2
            + (16 - 24 * PowerSeries.X) * qF1 - qF) := by
    rw [qG1_eq, qG2_eq, qG3_eq, qG]
    ring
  rw [hE, qF_ode, qF_ode_deriv]
  ring

-- Theorem: the expanded form of `qG_ode`, with the powers of `X` separated so that
-- coefficient extraction can use the shift lemmas for `X` and `X²`.
theorem qG_ode_expand :
    8 * (PowerSeries.X ^ 2 * qG3) - 8 * (PowerSeries.X ^ 3 * qG3)
      + 24 * (PowerSeries.X * qG2) - 36 * (PowerSeries.X ^ 2 * qG2)
      + 8 * qG1 - 26 * (PowerSeries.X * qG1) - qG = 0 := by
  rw [← qG_ode]
  ring

/-! ### The coefficient recurrence of the symmetric square

Reading off the coefficient of `X^(k+3)` in `qG_ode_expand` gives the first-order recurrence

`8 (k+4)³ [X^(k+4)]G = (2k+7)³ [X^(k+3)]G`,

i.e. `8 (n+1)³ g_{n+1} = (2n+1)³ g_n`. Its solution with `g₀ = 1` is `g_n = C(2n,n)³/64ⁿ`,
which is exactly the coefficient of Clausen's `₃F₂(1/2,1/2,1/2;1,1;·)`. The three base cases
`n = 0, 1, 2` are read off separately, since the general extraction needs the shift to stay
nonnegative. -/

-- Theorem: the constant coefficient of `qG_ode_expand` gives `8 g₁ = g₀`.
theorem qG_coeff_rec_zero : 8 * PowerSeries.coeff 1 qG = PowerSeries.coeff 0 qG := by
  have h := congrArg (PowerSeries.coeff 0) qG_ode_expand
  simp only [map_sub, map_add, map_zero, PowerSeries.coeff_C_mul,
    show (8 : PowerSeries ℝ) = PowerSeries.C 8 from rfl,
    show (24 : PowerSeries ℝ) = PowerSeries.C 24 from rfl,
    show (36 : PowerSeries ℝ) = PowerSeries.C 36 from rfl,
    show (26 : PowerSeries ℝ) = PowerSeries.C 26 from rfl,
    qG1, qG2, qG3,
    PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_derivative] at h
  norm_num at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  linarith

-- Theorem: the first coefficient of `qG_ode_expand` gives `64 g₂ = 27 g₁`.
theorem qG_coeff_rec_one : 64 * PowerSeries.coeff 2 qG = 27 * PowerSeries.coeff 1 qG := by
  have h := congrArg (PowerSeries.coeff 1) qG_ode_expand
  simp only [map_sub, map_add, map_zero, PowerSeries.coeff_C_mul,
    show (8 : PowerSeries ℝ) = PowerSeries.C 8 from rfl,
    show (24 : PowerSeries ℝ) = PowerSeries.C 24 from rfl,
    show (36 : PowerSeries ℝ) = PowerSeries.C 36 from rfl,
    show (26 : PowerSeries ℝ) = PowerSeries.C 26 from rfl,
    qG1, qG2, qG3,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_derivative] at h
  norm_num at h
  linarith

-- Theorem: the second coefficient of `qG_ode_expand` gives `216 g₃ = 125 g₂`.
theorem qG_coeff_rec_two : 216 * PowerSeries.coeff 3 qG = 125 * PowerSeries.coeff 2 qG := by
  have h := congrArg (PowerSeries.coeff 2) qG_ode_expand
  simp only [map_sub, map_add, map_zero, PowerSeries.coeff_C_mul,
    show (8 : PowerSeries ℝ) = PowerSeries.C 8 from rfl,
    show (24 : PowerSeries ℝ) = PowerSeries.C 24 from rfl,
    show (36 : PowerSeries ℝ) = PowerSeries.C 36 from rfl,
    show (26 : PowerSeries ℝ) = PowerSeries.C 26 from rfl,
    qG1, qG2, qG3,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_derivative] at h
  norm_num at h
  linarith

-- Theorem: `[X^(k+3)](X² p) = [X^(k+1)]p`, the shift needed by the coefficient extraction
-- (the generic `coeff_X_pow_mul` only matches `X³` at the index `k + 3`).
theorem coeff_X_sq_mul_add_three (p : PowerSeries ℝ) (k : ℕ) :
    PowerSeries.coeff (k + 3) (PowerSeries.X ^ 2 * p)
      = PowerSeries.coeff (k + 1) p := by
  rw [show k + 3 = (k + 1) + 2 by omega]
  exact PowerSeries.coeff_X_pow_mul p 2 (k + 1)

-- Theorem: the coefficient of `X^(k+3)` in `qG_ode_expand`, the recurrence
-- `8 (k+4)^3 g_{k+4} = (2k+7)^3 g_{k+3}`.
theorem qG_coeff_rec (k : ℕ) :
    8 * ((k : ℝ) + 4) ^ 3 * PowerSeries.coeff (k + 4) qG
      = (2 * (k : ℝ) + 7) ^ 3 * PowerSeries.coeff (k + 3) qG := by
  have h := congrArg (PowerSeries.coeff (k + 3)) qG_ode_expand
  simp only [map_sub, map_add, map_zero, PowerSeries.coeff_C_mul,
    show (8 : PowerSeries ℝ) = PowerSeries.C 8 from rfl,
    show (24 : PowerSeries ℝ) = PowerSeries.C 24 from rfl,
    show (36 : PowerSeries ℝ) = PowerSeries.C 36 from rfl,
    show (26 : PowerSeries ℝ) = PowerSeries.C 26 from rfl,
    qG1, qG2, qG3,
    coeff_X_sq_mul_add_three, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul,
    PowerSeries.coeff_derivative] at h
  push_cast at h
  linear_combination h

-- Theorem: the full recurrence `8 (n+1)^3 [X^(n+1)]G = (2n+1)^3 [X^n]G` for every `n`.
theorem qG_coeff_rec_all (n : ℕ) :
    8 * ((n : ℝ) + 1) ^ 3 * PowerSeries.coeff (n + 1) qG
      = (2 * (n : ℝ) + 1) ^ 3 * PowerSeries.coeff n qG := by
  rcases n with _ | _ | _ | k
  · simpa using qG_coeff_rec_zero
  · norm_num
    exact qG_coeff_rec_one
  · norm_num
    exact qG_coeff_rec_two
  · have h := qG_coeff_rec k
    rw [show k + 3 + 1 = k + 4 by omega] at h ⊢
    push_cast at h ⊢
    linear_combination h

/-! ### The coefficients of the symmetric square are Clausen's coefficients

The recurrence of the previous section determines `[Xⁿ]G` from `g₀ = 1`, so comparing with
`dₙ = C(2n,n)³/64ⁿ` (which satisfies the same recurrence by the central-binomial formula
`(n+1) C(2n+2,n+1) = 2(2n+1) C(2n,n)`) identifies the two: `[Xⁿ](qF²) = dₙ`. -/

/-- The Clausen coefficient `C(2n,n)³/64ⁿ`, the `n`-th coefficient of
`₃F₂(1/2,1/2,1/2;1,1;·)`. -/
def clausenCoeff (n : ℕ) : ℝ := (Nat.choose (2 * n) n : ℝ) ^ 3 / 64 ^ n

-- Theorem: `clausenCoeff 0 = 1`.
theorem clausenCoeff_zero : clausenCoeff 0 = 1 := by
  norm_num [clausenCoeff]

-- Theorem: `d` satisfies the recurrence `8 (n+1)³ d_{n+1} = (2n+1)³ dₙ`.
theorem clausenCoeff_succ (n : ℕ) :
    8 * ((n : ℝ) + 1) ^ 3 * clausenCoeff (n + 1)
      = (2 * (n : ℝ) + 1) ^ 3 * clausenCoeff n := by
  unfold clausenCoeff
  have hrec := Nat.succ_mul_centralBinom_succ n
  simp only [Nat.centralBinom_eq_two_mul_choose] at hrec
  have hcast : ((n : ℝ) + 1) * (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) := by
    exact_mod_cast hrec
  have hC : (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]
    nlinarith [hcast]
  rw [hC, show (64 : ℝ) ^ (n + 1) = 64 ^ n * 64 by rw [pow_succ]]
  field_simp
  ring

-- Theorem: the constant coefficient of `qF²` is `1`.
theorem coeff_zero_qG : PowerSeries.coeff 0 qG = 1 := by
  rw [qG, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, qF, coeff_hypSeries]
  norm_num [hypCoeff, ordinaryHypergeometricCoefficient]

-- Theorem: `clausenCoeff n = [Xⁿ](qF²)`, i.e. the two sequences agree.
theorem clausenCoeff_eq_coeff_qG (n : ℕ) :
    clausenCoeff n = PowerSeries.coeff n qG := by
  induction n with
  | zero => rw [clausenCoeff_zero, coeff_zero_qG]
  | succ n ih =>
    have h1 := qG_coeff_rec_all n
    have h2 := clausenCoeff_succ n
    rw [ih] at h2
    have h3 : 8 * ((n : ℝ) + 1) ^ 3 * clausenCoeff (n + 1)
        = 8 * ((n : ℝ) + 1) ^ 3 * PowerSeries.coeff (n + 1) qG := by
      rw [h2, h1]
    exact mul_left_cancel₀ (by positivity : (8 : ℝ) * ((n : ℝ) + 1) ^ 3 ≠ 0) h3

/-! ### The analytic transfer

`qG = qF²` gives the coefficient convolution `[Xⁿ]G = Σ_{k≤n} c_k c_{n-k}` formally, while
`hasSum_hyp` gives the absolutely convergent series of the `c_k xᵏ` at `|x| < 1`. The Cauchy
product `hasSum_sum_range_mul_of_summable_norm` then identifies the real series with
`(₂F₁(1/4,1/4;1;x))²`, and `clausenCoeff_eq_coeff_qG` rewrites its terms as `dₙ xⁿ`.

Absolute convergence is the geometric bound `c_n ≤ 1` (the ratio `((4n+1)/(4n+4))² ≤ 1`
keeps `[0,1]` invariant) together with `|x| < 1`. -/

-- Theorem: every coefficient of `₂F₁(1/4,1/4;1;·)` lies in `[0,1]`.
theorem hypCoeff_quarter_quarter_one_mem_Icc (n : ℕ) :
    0 ≤ hypCoeff (1 / 4) (1 / 4) 1 n ∧ hypCoeff (1 / 4) (1 / 4) 1 n ≤ 1 := by
  induction n with
  | zero => norm_num [hypCoeff, ordinaryHypergeometricCoefficient]
  | succ n ih =>
    rw [hypCoeff_quarter_quarter_one_succ]
    obtain ⟨h0, h1⟩ := ih
    set r : ℝ := (4 * (n : ℝ) + 1) / (4 * ((n : ℝ) + 1)) with hr
    have hr0 : 0 ≤ r := by rw [hr]; positivity
    have hrle : r ≤ 1 := by
      rw [hr, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((n : ℝ) + 1))]
      linarith
    have hr2 : r ^ 2 ≤ 1 := by nlinarith [hr0, hrle]
    constructor
    · exact mul_nonneg h0 (sq_nonneg r)
    · calc hypCoeff (1 / 4) (1 / 4) 1 n * r ^ 2
          ≤ 1 * 1 := mul_le_mul h1 hr2 (sq_nonneg r) (by norm_num)
        _ = 1 := by norm_num

-- Theorem: for `|x| < 1`, `Σₙ dₙ xⁿ = (₂F₁(1/4,1/4;1;x))²` at the `HasSum` level.
theorem clausen_hasSum {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => clausenCoeff n * x ^ n) ((hyp (1 / 4) (1 / 4) 1 x) ^ 2) := by
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n h
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1 := hasSum_hyp (a := 1 / 4) (b := 1 / 4) (c := 1) hx hc
  have hmem := hypCoeff_quarter_quarter_one_mem_Icc
  have hs : Summable fun n : ℕ => ‖hypCoeff (1 / 4) (1 / 4) 1 n * x ^ n‖ := by
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => |x| ^ n) (fun n => norm_nonneg _) ?_ ?_
    · intro n
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hmem n).1]
      nlinarith [(hmem n).2, pow_nonneg (abs_nonneg x) n]
    · exact summable_geometric_of_norm_lt_one (x := |x|)
        (by rwa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg x)])
  have h2 := hasSum_sum_range_mul_of_summable_norm
    (f := fun n : ℕ => hypCoeff (1 / 4) (1 / 4) 1 n * x ^ n) hs hs
  rw [h1.tsum_eq] at h2
  have hterm : ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1),
        (hypCoeff (1 / 4) (1 / 4) 1 k * x ^ k)
          * (hypCoeff (1 / 4) (1 / 4) 1 (n - k) * x ^ (n - k)))
        = clausenCoeff n * x ^ n := by
    intro n
    have hxpow : ∀ k ∈ Finset.range (n + 1), x ^ k * x ^ (n - k) = x ^ n := by
      intro k hk
      rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    calc (∑ k ∈ Finset.range (n + 1),
          (hypCoeff (1 / 4) (1 / 4) 1 k * x ^ k)
            * (hypCoeff (1 / 4) (1 / 4) 1 (n - k) * x ^ (n - k)))
        = ∑ k ∈ Finset.range (n + 1),
            (hypCoeff (1 / 4) (1 / 4) 1 k
              * hypCoeff (1 / 4) (1 / 4) 1 (n - k)) * x ^ n := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [← hxpow k hk]
          ring
      _ = (∑ k ∈ Finset.range (n + 1),
            hypCoeff (1 / 4) (1 / 4) 1 k * hypCoeff (1 / 4) (1 / 4) 1 (n - k)) * x ^ n := by
          rw [Finset.sum_mul]
      _ = PowerSeries.coeff n qG * x ^ n := by
          congr 1
          rw [qG, qF, PowerSeries.coeff_mul]
          simp only [coeff_hypSeries]
          exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => hypCoeff (1 / 4) (1 / 4) 1 i
              * hypCoeff (1 / 4) (1 / 4) 1 j) n).symm
      _ = clausenCoeff n * x ^ n := by rw [clausenCoeff_eq_coeff_qG]
  simpa only [hterm, pow_two] using h2

-- Theorem: Clausen's identity `Σₙ C(2n,n)³ (x/64)ⁿ = (₂F₁(1/4,1/4;1;x))²` for `|x| < 1`.
theorem clausen_tsum_eq {x : ℝ} (hx : |x| < 1) :
    (∑' n : ℕ, (Nat.choose (2 * n) n : ℝ) ^ 3 * (x / 64) ^ n)
      = (hyp (1 / 4) (1 / 4) 1 x) ^ 2 := by
  rw [← (clausen_hasSum hx).tsum_eq]
  refine tsum_congr fun n => ?_
  rw [clausenCoeff, div_pow]
  ring

-- Theorem: the `₃F₂(1/2,1/2,1/2;1,1;·)` `tsum` is P-constructible for P-constructible
-- `0 ≤ x < 1`; this is Clausen's identity, and it is now unconditional.
theorem clausen_tsum_Pconstructible {x : ℝ} (hx : PConstructible x)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    PConstructible (∑' n : ℕ, (Nat.choose (2 * n) n : ℝ) ^ 3 * (x / 64) ^ n) := by
  rw [clausen_tsum_eq (by rw [abs_of_nonneg hx0]; exact hx1)]
  exact (hyp_one_fourth_squared_Pconstructible hx hx0 hx1).2

end

end Pconstructible
