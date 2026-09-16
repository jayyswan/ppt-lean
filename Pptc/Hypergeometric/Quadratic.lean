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
-- `Basic` supplies the `hyp`/`hypCoeff` API; `Pochhammer` the lemma `(1)ₙ = n!`.
import Pptc.Hypergeometric.Basic
import Pptc.Hypergeometric.Contiguous
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Pptc.Hypergeometric.Quadratic

The quadratic transformation of the Gauss hypergeometric function (V6 of
`PLAN-hypergeometric-00-overview.md`):

`₂F₁(1/2, 1/2; 1; z) = ₂F₁(1/4, 1/4; 1; 4 z (1 - z))` for `0 ≤ z < 1/2`.

This is the `a = b = 1/4` case of Goursat's symmetric quadratic transformation
`₂F₁(2a, 2b; a+b+1/2; z) = ₂F₁(a, b; a+b+1/2; 4z(1-z))`, and it is the gateway to the
Clausen identity (L6b) and to the arithmetic-geometric mean (L6c).

## Status: proved

The proof has two parts.

* **Formal coefficient identity.** `hypSeriesQuad_eq_hypSeries_half` shows
  `(hypSeries (1/4) (1/4) 1).subst (4 * X * (1 - X)) = hypSeries (1/2) (1/2) 1` in `ℝ⟦X⟧`:
  the hypergeometric equation of `(1/4, 1/4; 1)` pulls back along `w = 4X(1-X)` to that of
  `(1/2, 1/2; 1)`, and the first-order coefficient recurrence identifies the two series.

* **Analytic transfer.** This is done at the level of `HasSum`, because this Mathlib has no
  `PowerSeries` evaluation API (`PowerSeries.sum` does not exist and `ℝ` carries no
  `IsLinearTopology` instance). Expanding `(4z(1-z))^m` binomially turns the re-expansion of
  `₂F₁(1/4,1/4;1;4z(1-z))` into the double series `quadFamily z`; the coefficient bound
  `|[Xⁿ]((4X(1-X))^m)| ≤ 4^m C(m, n-m)` gives the geometric majorant `(4|z|(1+|z|))^m`, so
  `quadFamily z` is summable on `4|z|(1+|z|) < 1`. `HasSum.tsum_fiberwise` re-sums by fibres,
  and the coefficient identity identifies the fibre sums with `hypCoeff (1/2) (1/2) 1`, giving
  V6 on that disc (`hyp_quadratic_small`). Both sides are analytic on the Cassini interval
  `((1-√2)/2, 1/2)` (where `|z| < 1` and `|4z(1-z)| < 1`), so
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` extends V6 to all of `0 ≤ z < 1/2`,
  which is `hyp_quadratic`.

## The ODE route (verified algebraically)

The substitution is genuinely quadratic: `w' = 4(1 - 2z)` and, with `w = 4z - 4z²`,
`w'² = 16(1 - w)`. If `g z = ∑_m c_m (w z)^m` with `c_m = ((1/4)_m/m!)²`, then

`z(1-z) g'' + (1-2z) g' - g/4 = (1/4) ∑_m c_m w^{m-1} [16 m² (1-w) - 8 m w - w]`,

and `c_m m² = c_{m-1} (m - 3/4)²` telescopes the bracket to zero. So `g` satisfies the
`₂F₁(1/2, 1/2; 1; ·)` equation `z(1-z) g'' + (1-2z) g' - g/4 = 0`. The coefficient
recurrence of that equation, `(n+1)² b_{n+1} = (n + 1/2)² b_n`, is the uniqueness
statement that would finish the proof once `g` is known to be analytic with `b` as its
Taylor coefficients. -/

open scoped Topology ENNReal

namespace Pconstructible

noncomputable section

/-! ### Coefficients of `₂F₁(1/2, 1/2; 1; ·)` and `₂F₁(1/4, 1/4; 1; ·)`

The two coefficient families that the quadratic transformation identifies. For `c = 1`
and `a = b = 1/2` the two factors `(1/2)ₙ` are central-binomial coefficients, and for
`a = b = 1/4` the coefficient is the square of the Pochhammer ratio `(1/4)ₙ/n!`. -/

/-- The `n`-th coefficient of `₂F₁(1/2, 1/2; 1; ·)` is the square of
`C(2n,n)/4ⁿ = (1/2)ₙ/n!`, the central-binomial probability.

This is the coefficient form of the elliptic-integral identity
`₂F₁(1/2, 1/2; 1; z) = (2/π) K(z)`, and it is the `a = b = 1/2` case of the coefficient
of the elliptic class. -/
-- Theorem: `hypCoeff (1/2) (1/2) 1 n = (C(2n,n) / 4^n)^2`.
theorem hypCoeff_half_half_one (n : ℕ) :
    hypCoeff (1 / 2) (1 / 2) 1 n = ((Nat.choose (2 * n) n : ℝ) / 4 ^ n) ^ 2 := by
  induction n with
  | zero => norm_num [hypCoeff, ordinaryHypergeometricCoefficient]
  | succ n ih =>
    rw [hypCoeff_succ, ih]
    have hrec := Nat.succ_mul_centralBinom_succ n
    simp only [Nat.centralBinom_eq_two_mul_choose] at hrec
    have hcast : ((n : ℝ) + 1) * (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
        = 2 * (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) := by
      exact_mod_cast hrec
    have hC : (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
        = 2 * (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) := by
      rw [eq_div_iff (by positivity)]
      nlinarith [hcast]
    rw [hC, pow_succ]
    have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- The ratio of consecutive coefficients of `₂F₁(1/2, 1/2; 1; ·)`:
`a_{n+1} = a_n ((2n+1)/(2n+2))²`. This is the first-order recurrence that uniquely
determines the coefficients, i.e. the power-series form of the hypergeometric equation
`z(1-z) a'' + (1-2z) a' - a/4 = 0` at `a = b = 1/2`, `c = 1`. -/
-- Theorem: `hypCoeff (1/2)(1/2)1 (n+1) = hypCoeff (1/2)(1/2)1 n * ((2n+1)/(2(n+1)))²`.
theorem hypCoeff_half_half_one_succ (n : ℕ) :
    hypCoeff (1 / 2) (1 / 2) 1 (n + 1) =
      hypCoeff (1 / 2) (1 / 2) 1 n * ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) ^ 2 := by
  rw [hypCoeff_half_half_one (n + 1), hypCoeff_half_half_one n]
  have hrec := Nat.succ_mul_centralBinom_succ n
  simp only [Nat.centralBinom_eq_two_mul_choose] at hrec
  have hcast : ((n : ℝ) + 1) * (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) := by
    exact_mod_cast hrec
  have hC : (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]
    nlinarith [hcast]
  rw [hC, pow_succ]
  field_simp
  ring

/-! ### Reductions

The coefficient recurrence of `₂F₁(1/2,1/2;1;·)` is first order, so it has a one-dimensional
solution space: a sequence `u` with `u 0 = 1` and the same recurrence is *identically*
`hypCoeff (1/2) (1/2) 1`. This is the uniqueness statement that turns a proof that the
Taylor coefficients of `z ↦ hyp (1/4) (1/4) 1 (4 z (1 - z))` satisfy the recurrence into the
quadratic transformation. -/

/-- A sequence with `u 0 = 1` satisfying the first-order coefficient recurrence of
`₂F₁(1/2, 1/2; 1; ·)` coincides with `hypCoeff (1/2) (1/2) 1`. -/
-- Theorem: `u 0 = 1` and `u (n+1) = u n ((2n+1)/(2(n+1)))²` imply `u n = hypCoeff (1/2)(1/2)1 n`.
theorem eq_hypCoeff_half_half_one_of_ratio {u : ℕ → ℝ} (h0 : u 0 = 1)
    (hu : ∀ n : ℕ, u (n + 1) = u n * ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) ^ 2) :
    ∀ n : ℕ, u n = hypCoeff (1 / 2) (1 / 2) 1 n := by
  intro n
  induction n with
  | zero => rw [h0, hypCoeff_half_half_one]; norm_num
  | succ n ih => rw [hu n, ih, hypCoeff_half_half_one_succ]

/-! ### Coefficients of the substituted series

The same recurrence for the `(1/4, 1/4; 1)` coefficients, which is what the re-expansion of
`₂F₁(1/4,1/4;1;4z(1-z))` propagates through the binomial expansion
`pow_four_mul_one_sub_pow`. -/

/-- The ratio of consecutive coefficients of `₂F₁(1/4, 1/4; 1; ·)`:
`c_{n+1} = c_n ((4n+1)/(4n+4))²`. -/
-- Theorem: `hypCoeff (1/4)(1/4)1 (n+1) = hypCoeff (1/4)(1/4)1 n * ((4n+1)/(4(n+1)))²`.
theorem hypCoeff_quarter_quarter_one_succ (n : ℕ) :
    hypCoeff (1 / 4) (1 / 4) 1 (n + 1) =
      hypCoeff (1 / 4) (1 / 4) 1 n * ((4 * (n : ℝ) + 1) / (4 * ((n : ℝ) + 1))) ^ 2 := by
  rw [hypCoeff_succ]
  generalize hypCoeff (1 / 4) (1 / 4) 1 n = q
  have h1 : (1 + (n : ℝ) * 2 + (n : ℝ) ^ 2) ≠ 0 := by positivity
  have h2 : (4 + (n : ℝ) * 4) ≠ 0 := by positivity
  field_simp
  ring

/-- The `n`-th coefficient of `₂F₁(1/4, 1/4; 1; ·)` is `((1/4)ₙ/n!)²`: with `c = 1` the
factor `(1)ₙ = n!` cancels one `n!`, and the two `(1/4)ₙ` factors remain. -/
-- Theorem: `hypCoeff (1/4) (1/4) 1 n = ((1/4)_n / n!)^2`.
theorem hypCoeff_quarter_quarter_one (n : ℕ) :
    hypCoeff (1 / 4) (1 / 4) 1 n =
      ((ascPochhammer ℝ n).eval (1 / 4) / (n.factorial : ℝ)) ^ 2 := by
  rw [hypCoeff, ordinaryHypergeometricCoefficient, ascPochhammer_eval_one]
  ring

/-! ### The substitution `w = 4 z (1 - z)`

The quadratic map sends the monomial `w^m` to a sum of monomials `z^{m+j}`. This
expansion is what makes the re-expansion of `₂F₁(1/4,1/4;1;4z(1-z))` a power series in
`z`, and it is a purely algebraic (binomial-theorem) fact, independent of convergence. -/

/-- The substitution `w = 4 z (1 - z)` applied to `w^m`, expanded in powers of `z`:
`(4 z (1 - z))^m = ∑_{j=0}^m 4^m C(m,j) (-1)^j z^{m+j}`. -/
-- Theorem: `(4 z (1 - z))^m = ∑_{j ≤ m} 4^m * C(m,j) * (-1)^j * z^(m+j)`.
theorem pow_four_mul_one_sub_pow (m : ℕ) (z : ℝ) :
    (4 * z * (1 - z)) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        4 ^ m * (Nat.choose m j : ℝ) * (-1) ^ j * z ^ (m + j) := by
  have h1 : (1 - z : ℝ) ^ m = ∑ j ∈ Finset.range (m + 1),
      (Nat.choose m j : ℝ) * (-z) ^ j := by
    rw [show (1 - z : ℝ) = -z + 1 by ring, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : (4 * z * (1 - z)) ^ m = 4 ^ m * z ^ m * (1 - z) ^ m := by
    rw [mul_pow, mul_pow]
  rw [h2, h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_pow]
  ring

/-! ### The transformation at the origin

`₂F₁` is `1` at `z = 0`, so V6 holds there; this is the base case of every route to the
full identity. The full statement on `[0, 1/2)` remains the target of L6a; see the module
docstring and `HANDOFF-hypergeometric-L6a.md`. -/

/-- V6 at the origin: both sides equal `1`. -/
-- Theorem: `hyp (1/2)(1/2)1 0 = hyp (1/4)(1/4)1 (4 * 0 * (1 - 0))`.
theorem hyp_quadratic_zero :
    hyp (1 / 2) (1 / 2) 1 0 = hyp (1 / 4) (1 / 4) 1 (4 * 0 * (1 - 0)) := by
  simp [hyp, ordinaryHypergeometric_zero]

/-! ### The re-expansion of `₂F₁(1/4,1/4;1;4z(1-z))` and its creative telescoping

Expanding `(4 z (1 - z))^k` by `pow_four_mul_one_sub_pow` and collecting the coefficient of
`z^n` gives the sequence

`b n = ∑_{k ≤ n} c_k 4^k (-1)^{n-k} C(k, n-k)`, `c_k = hypCoeff (1/4) (1/4) 1 k`,

whose terms are `quadTerm`. The quadratic transformation is the statement `b n =
hypCoeff (1/2) (1/2) 1 n`; the sequence satisfies the same first-order recurrence, and the
route below is the *creative telescoping* certificate that proves it.

Writing `A(n,k) = d_{n+1,k}/d_{n,k}` and `r(n,k) = d_{n,k+1}/d_{n,k}` for the summand
`d_{n,k} = quadTerm n k`, the certificate is the rational-function identity

`quadTelescope n (k+1) * r(n,k) - quadTelescope n k = (2n+2)² A(n,k) - (2n+1)²`

with `quadTelescope n k = -4k(2k-n)(2k-n-1)/(k-n-1)`. Summing over `k ≤ n-1` telescopes the
right-hand side, and the four boundary terms cancel, giving `b (n+1) = b n ((2n+1)/(2n+2))²`. -/

/-- The `(n,k)` summand of the re-expansion of `₂F₁(1/4,1/4;1;4z(1-z))`,
`c_k 4^k (-1)^(n-k) C(k, n-k)` with `c_k = hypCoeff (1/4) (1/4) 1 k`. -/
def quadTerm (n k : ℕ) : ℝ :=
  hypCoeff (1 / 4) (1 / 4) 1 k * 4 ^ k * (-1 : ℝ) ^ (n - k) * (k.choose (n - k) : ℝ)

/-- The `n`-th coefficient of the re-expansion of `₂F₁(1/4,1/4;1;4z(1-z))` in powers of `z`:
`quadCoeff n = ∑_{k ≤ n} c_k 4^k (-1)^{n-k} C(k, n-k)`. This is the sequence that V6
identifies with `hypCoeff (1/2) (1/2) 1 n`. -/
def quadCoeff (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), quadTerm n k

-- Theorem: for `k ≤ n`, `(n+1-k) d_{n+1,k} = (n - 2k) d_{n,k}`.
theorem quadTerm_succ_n {n k : ℕ} (hk : k ≤ n) :
    ((n : ℝ) + 1 - (k : ℝ)) * quadTerm (n + 1) k
      = ((n : ℝ) - 2 * (k : ℝ)) * quadTerm n k := by
  have hchoose : (k.choose (n - k + 1) : ℝ) * ((n : ℝ) + 1 - (k : ℝ))
      = (k.choose (n - k) : ℝ) * (2 * (k : ℝ) - (n : ℝ)) := by
    rcases lt_or_ge (2 * k) n with h2k | h2k
    · have hz : k.choose (n - k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have hz2 : k.choose (n - k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz, hz2]
      ring
    · have h1 : (k.choose ((n - k) + 1) : ℝ) * (((n - k) + 1 : ℕ) : ℝ)
          = (k.choose (n - k) : ℝ) * ((k - (n - k) : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq k (n - k)
      have c1 : (((n - k) + 1 : ℕ) : ℝ) = (n : ℝ) + 1 - (k : ℝ) := by
        push_cast
        rw [Nat.cast_sub hk]
        ring
      have c2 : ((k - (n - k) : ℕ) : ℝ) = 2 * (k : ℝ) - (n : ℝ) := by
        rw [show k - (n - k) = 2 * k - n by omega,
          Nat.cast_sub (show n ≤ 2 * k by omega)]
        push_cast
        ring
      rw [c1, c2] at h1
      exact h1
  calc ((n : ℝ) + 1 - (k : ℝ)) * quadTerm (n + 1) k
      = -((hypCoeff (1 / 4) (1 / 4) 1 k * 4 ^ k * (-1 : ℝ) ^ (n - k)))
          * ((k.choose (n - k + 1) : ℝ) * ((n : ℝ) + 1 - (k : ℝ))) := by
        unfold quadTerm
        rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
        ring
    _ = -((hypCoeff (1 / 4) (1 / 4) 1 k * 4 ^ k * (-1 : ℝ) ^ (n - k)))
          * ((k.choose (n - k) : ℝ) * (2 * (k : ℝ) - (n : ℝ))) := by
        rw [hchoose]
    _ = ((n : ℝ) - 2 * (k : ℝ)) * quadTerm n k := by
        unfold quadTerm
        ring

-- (The `k`-shift ratio `d_{n,k+1}/d_{n,k}` was attempted here as part of a creative-telescoping
-- proof of the coefficient identity; the case analysis needed for the truncated `Nat`
-- subtraction is delicate, and that route was abandoned in favour of the formal-power-series
-- argument in the final section below.)

/-- The creative-telescoping certificate `R(n,k) = -4k(2k-n)(2k-n-1)/(k-n-1)`. -/
def quadTelescope (n k : ℕ) : ℝ :=
  -4 * (k : ℝ) * (2 * (k : ℝ) - (n : ℝ)) * (2 * (k : ℝ) - (n : ℝ) - 1) /
    ((k : ℝ) - (n : ℝ) - 1)

/-- The ratio `d_{n+1,k}/d_{n,k} = -(2k-n)/(n+1-k)` of consecutive `n`. -/
def quadRatioN (n k : ℕ) : ℝ :=
  -(2 * (k : ℝ) - (n : ℝ)) / ((n : ℝ) + 1 - (k : ℝ))

/-- The ratio `d_{n,k+1}/d_{n,k} = -(4k+1)²(n-k)/(4(k+1)(2k+1-n)(2k+2-n))` of consecutive `k`. -/
def quadRatioK (n k : ℕ) : ℝ :=
  -((4 * (k : ℝ) + 1) ^ 2 * ((n : ℝ) - (k : ℝ))) /
    (4 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1 - (n : ℝ)) * (2 * (k : ℝ) + 2 - (n : ℝ)))

-- (The rational-function identity `quadTelescope n (k+1) r(n,k) - quadTelescope n k =
-- (2n+2)² A(n,k) - (2n+1)²` was the goal of the abandoned creative-telescoping route.)

/-! ### The formal-power-series proof of the coefficient identity

The Taylor coefficients of `z ↦ ₂F₁(1/4,1/4;1;4z(1-z))` are the coefficients of the formal
substitution `H.subst w`, `w = 4X(1-X)`, `H = ∑ₙ hypCoeff (1/4)(1/4)1 n Xⁿ`. Working in
`ℝ⟦X⟧` lets us prove the coefficient identity `b n = hypCoeff (1/2)(1/2)1 n` without any
convergence input: `H` satisfies its own hypergeometric ODE, the chain rule
`PowerSeries.derivative_subst` transports it to the substituted series, and reading off
coefficients of the resulting second-order ODE gives the recurrence
`(n+1)² b_{n+1} = (n+1/2)² b_n`, whose solution with `b 0 = 1` is `hypCoeff (1/2)(1/2)1`. -/

open scoped PowerSeries

/-- The formal power series `∑ₙ cₙ Xⁿ` attached to a hypergeometric coefficient family. -/
def hypSeries (a b c : ℝ) : PowerSeries ℝ := PowerSeries.mk (hypCoeff a b c)

@[simp] theorem coeff_hypSeries (a b c : ℝ) (n : ℕ) :
    PowerSeries.coeff n (hypSeries a b c) = hypCoeff a b c n :=
  PowerSeries.coeff_mk n (hypCoeff a b c)

/-- The `(1/4,1/4;1)` hypergeometric series satisfies its (formal) hypergeometric equation
`16 X (1-X) H'' + (16 - 24 X) H' - H = 0`. -/
theorem hypSeries_quarter_ode :
    (16 : PowerSeries ℝ) * (PowerSeries.X * (1 - PowerSeries.X))
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1))
      + (16 - 24 * PowerSeries.X) * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)
      - hypSeries (1 / 4) (1 / 4) 1 = 0 := by
  ext m
  rcases m with _ | _ | n
  · -- `m = 0`
    rw [map_zero]
    have h16 : (16 : PowerSeries ℝ) = PowerSeries.C 16 := rfl
    have h24 : (24 : PowerSeries ℝ) = PowerSeries.C 24 := rfl
    have e1 : (16 : PowerSeries ℝ) * (PowerSeries.X * (1 - PowerSeries.X))
          * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1))
        = PowerSeries.C 16 * (PowerSeries.X * ((1 - PowerSeries.X)
            * PowerSeries.derivative ℝ
              (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)))) := by
      rw [h16]; ring
    have e2 : (16 - 24 * PowerSeries.X) * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)
        = PowerSeries.C 16 * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)
          - PowerSeries.C 24
            * (PowerSeries.X * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)) := by
      rw [h16, h24]; ring
    rw [e1, e2]
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_derivative, coeff_hypSeries]
    rw [hypCoeff_quarter_quarter_one_succ 0]
    ring
  · -- `m = 1`
    rw [map_zero]
    have h16 : (16 : PowerSeries ℝ) = PowerSeries.C 16 := rfl
    have h24 : (24 : PowerSeries ℝ) = PowerSeries.C 24 := rfl
    have e1 : (16 : PowerSeries ℝ) * (PowerSeries.X * (1 - PowerSeries.X))
          * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1))
        = PowerSeries.C 16
          * (PowerSeries.X * PowerSeries.derivative ℝ
              (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)))
          - PowerSeries.C 16
            * (PowerSeries.X ^ 2 * PowerSeries.derivative ℝ
                (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1))) := by
      rw [h16]; ring
    have e2 : (16 - 24 * PowerSeries.X) * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)
        = PowerSeries.C 16 * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)
          - PowerSeries.C 24
            * (PowerSeries.X * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)) := by
      rw [h16, h24]; ring
    rw [e1, e2, show PowerSeries.X ^ 2 = PowerSeries.X * PowerSeries.X by ring]
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, mul_assoc,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_derivative]
    repeat rw [coeff_hypSeries]
    rw [hypCoeff_quarter_quarter_one_succ 1, hypCoeff_quarter_quarter_one_succ 0]
    ring
  · -- `m = n + 1 + 1`
    rw [map_zero]
    have h16 : (16 : PowerSeries ℝ) = PowerSeries.C 16 := rfl
    have h24 : (24 : PowerSeries ℝ) = PowerSeries.C 24 := rfl
    have e1 : (16 : PowerSeries ℝ) * (PowerSeries.X * (1 - PowerSeries.X))
          * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1))
        = PowerSeries.C 16
          * (PowerSeries.X * PowerSeries.derivative ℝ
              (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)))
          - PowerSeries.C 16
            * (PowerSeries.X ^ 2 * PowerSeries.derivative ℝ
                (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1))) := by
      rw [h16]; ring
    have e2 : (16 - 24 * PowerSeries.X) * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)
        = PowerSeries.C 16 * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)
          - PowerSeries.C 24
            * (PowerSeries.X * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)) := by
      rw [h16, h24]; ring
    rw [e1, e2, show PowerSeries.X ^ 2 = PowerSeries.X * PowerSeries.X by ring]
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, mul_assoc,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    repeat rw [coeff_hypSeries]
    rw [show n + 1 + 1 + 1 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega]
    rw [hypCoeff_quarter_quarter_one_succ (n + 2)]
    set c : ℝ := hypCoeff (1 / 4) (1 / 4) 1 (n + 2) with hc
    field_simp
    push_cast
    ring

/-- The quadratic substitution `w = 4 X (1 - X)` whose pullback of the
`₂F₁(1/4,1/4;1;·)` equation is the `₂F₁(1/2,1/2;1;·)` equation. -/
def quadSubst : PowerSeries ℝ := 4 * PowerSeries.X * (1 - PowerSeries.X)

/-- `quadSubst` has zero constant coefficient, so it can be substituted into a power series. -/
theorem hasSubst_quadSubst : PowerSeries.HasSubst quadSubst :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [quadSubst])

/-- The derivative of the quadratic substitution: `w' = 4 (1 - 2X)`. -/
theorem derivative_quadSubst :
    PowerSeries.derivative ℝ quadSubst = 4 * (1 - 2 * PowerSeries.X) := by
  rw [quadSubst]
  simp only [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
    zero_sub, smul_eq_mul, mul_neg, mul_one]
  rw [show (4 : PowerSeries ℝ) = PowerSeries.C 4 from rfl, PowerSeries.derivative_C]
  ring

/-- The second derivative of the quadratic substitution: `w'' = -8`. -/
theorem derivative_derivative_quadSubst :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ quadSubst) = -8 := by
  rw [derivative_quadSubst]
  simp only [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
    zero_sub, smul_eq_mul, mul_neg, mul_one]
  rw [show (4 : PowerSeries ℝ) = PowerSeries.C 4 from rfl, PowerSeries.derivative_C,
    show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, PowerSeries.derivative_C]
  simp only [map_ofNat]
  norm_num

/-- The pullback of the `₂F₁(1/4,1/4;1;·)` equation along `w = 4X(1-X)`: the substituted
series `H (4X(1-X))` satisfies the `₂F₁(1/2,1/2;1;·)` equation
`4X(1-X) B'' + 4(1-2X) B' - B = 0`. This is the formal chain rule applied to
`hypSeries_quarter_ode`: `w w'² = 16 w (1-w)` and `w w'' + w'² = 16 - 24 w`. -/
theorem hypSeries_quarter_subst_ode :
    4 * PowerSeries.X * (1 - PowerSeries.X)
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ
            (PowerSeries.subst quadSubst (hypSeries (1 / 4) (1 / 4) 1)))
      + 4 * (1 - 2 * PowerSeries.X)
        * PowerSeries.derivative ℝ
            (PowerSeries.subst quadSubst (hypSeries (1 / 4) (1 / 4) 1))
      - PowerSeries.subst quadSubst (hypSeries (1 / 4) (1 / 4) 1) = 0 := by
  have hsub : PowerSeries.HasSubst quadSubst := hasSubst_quadSubst
  have hzero : PowerSeries.subst quadSubst (0 : PowerSeries ℝ) = 0 := by
    simp only [← PowerSeries.coe_substAlgHom hsub, map_zero]
  have hsubst : PowerSeries.subst quadSubst
      ((16 : PowerSeries ℝ) * (PowerSeries.X * (1 - PowerSeries.X))
          * PowerSeries.derivative ℝ
              (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1))
        + (16 - 24 * PowerSeries.X)
          * PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)
        - hypSeries (1 / 4) (1 / 4) 1) = 0 := by
    rw [hypSeries_quarter_ode, hzero]
  have key : 16 * (quadSubst * (1 - quadSubst))
        * PowerSeries.subst quadSubst
            (PowerSeries.derivative ℝ
              (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)))
      + (16 - 24 * quadSubst)
        * PowerSeries.subst quadSubst
            (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1))
      - PowerSeries.subst quadSubst (hypSeries (1 / 4) (1 / 4) 1) = 0 := by
    rw [← hsubst]
    simp only [← PowerSeries.coe_substAlgHom hsub, map_add, map_sub, map_mul, map_ofNat,
      map_one, PowerSeries.substAlgHom_X hsub]
  have hB1 : PowerSeries.derivative ℝ
        (PowerSeries.subst quadSubst (hypSeries (1 / 4) (1 / 4) 1))
      = PowerSeries.subst quadSubst
            (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1))
        * PowerSeries.derivative ℝ quadSubst :=
    PowerSeries.derivative_subst hsub
  have hB2 : PowerSeries.derivative ℝ (PowerSeries.derivative ℝ
        (PowerSeries.subst quadSubst (hypSeries (1 / 4) (1 / 4) 1)))
      = (PowerSeries.subst quadSubst
              (PowerSeries.derivative ℝ
                (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1)))
            * PowerSeries.derivative ℝ quadSubst) * PowerSeries.derivative ℝ quadSubst
        + PowerSeries.subst quadSubst
              (PowerSeries.derivative ℝ (hypSeries (1 / 4) (1 / 4) 1))
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ quadSubst) := by
    rw [hB1, Derivation.leibniz, PowerSeries.derivative_subst hsub, smul_eq_mul, smul_eq_mul]
    ring
  rw [hB2, hB1, derivative_derivative_quadSubst, derivative_quadSubst]
  unfold quadSubst at *
  linear_combination key

/-! ### The coefficient recurrence of the substituted series

Reading off coefficients of `hypSeriesQuad_ode` gives the same first-order recurrence as
`₂F₁(1/2,1/2;1;·)`, so `hypSeries_quarter_subst_ode` is the uniqueness statement that
identifies `₂F₁(1/4,1/4;1;4X(1-X))` with `₂F₁(1/2,1/2;1;X)` at the level of formal power
series. -/

/-- The substituted series `H(4X(1-X))` with `H = ₂F₁(1/4,1/4;1;·)`, whose coefficients are
the left-hand side of the quadratic transformation. -/
def hypSeriesQuad : PowerSeries ℝ :=
  PowerSeries.subst quadSubst (hypSeries (1 / 4) (1 / 4) 1)

/-- `hypSeriesQuad` satisfies the `₂F₁(1/2,1/2;1;·)` equation. -/
theorem hypSeriesQuad_ode :
    4 * PowerSeries.X * (1 - PowerSeries.X)
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ hypSeriesQuad)
      + 4 * (1 - 2 * PowerSeries.X) * PowerSeries.derivative ℝ hypSeriesQuad
      - hypSeriesQuad = 0 :=
  hypSeries_quarter_subst_ode

/-- The expanded form of `hypSeriesQuad_ode`, with the powers of `X` separated so that the
coefficient extraction can use the shift lemmas for `X` and `X²`. -/
theorem hypSeriesQuad_ode_expand :
    4 * (PowerSeries.X
          * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ hypSeriesQuad))
      - 4 * (PowerSeries.X ^ 2
          * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ hypSeriesQuad))
      + 4 * PowerSeries.derivative ℝ hypSeriesQuad
      - 8 * (PowerSeries.X * PowerSeries.derivative ℝ hypSeriesQuad)
      - hypSeriesQuad = 0 := by
  rw [← hypSeriesQuad_ode]
  ring

/-- The constant term of `hypSeriesQuad` is `1`: substituting a series with zero constant
term does not change the constant term. -/
theorem coeff_zero_hypSeriesQuad : PowerSeries.coeff 0 hypSeriesQuad = 1 := by
  rw [hypSeriesQuad, PowerSeries.coeff_subst' hasSubst_quadSubst]
  rw [finsum_eq_single _ 0]
  · simp only [pow_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one,
      smul_eq_mul, mul_one]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_hypSeries]
    norm_num [hypCoeff, ordinaryHypergeometricCoefficient]
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
      show PowerSeries.constantCoeff quadSubst = 0 from by simp [quadSubst],
      zero_pow hd, smul_zero]

/-- The coefficient recurrence at `k + 2`, from the `(k+2)`-nd coefficient of
`hypSeriesQuad_ode`: `4 (k+3)² b(k+3) = (2(k+2)+1)² b(k+2)`. -/
theorem hypSeriesQuad_coeff_rec (k : ℕ) :
    4 * ((k : ℝ) + 3) ^ 2 * PowerSeries.coeff (k + 3) hypSeriesQuad
      = (2 * ((k : ℝ) + 2) + 1) ^ 2 * PowerSeries.coeff (k + 2) hypSeriesQuad := by
  have h := congrArg (PowerSeries.coeff (k + 2)) hypSeriesQuad_ode_expand
  simp only [map_sub, map_add, map_zero, PowerSeries.coeff_C_mul,
    show (4 : PowerSeries ℝ) = PowerSeries.C 4 from rfl,
    show (8 : PowerSeries ℝ) = PowerSeries.C 8 from rfl,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul,
    PowerSeries.coeff_derivative] at h
  rw [show k + 1 + 1 + 1 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega,
    show k + 2 + 1 = k + 3 by omega] at h
  push_cast at h
  linear_combination h

/-- The base case `4 b₁ = b₀`, from the constant coefficient of `hypSeriesQuad_ode`. -/
theorem hypSeriesQuad_coeff_rec_zero :
    4 * PowerSeries.coeff 1 hypSeriesQuad = PowerSeries.coeff 0 hypSeriesQuad := by
  have h := congrArg (PowerSeries.coeff 0) hypSeriesQuad_ode_expand
  simp only [map_sub, map_add, map_zero, PowerSeries.coeff_C_mul,
    show (4 : PowerSeries ℝ) = PowerSeries.C 4 from rfl,
    show (8 : PowerSeries ℝ) = PowerSeries.C 8 from rfl,
    PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_derivative] at h
  norm_num at h
  have hconst : PowerSeries.constantCoeff hypSeriesQuad = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact coeff_zero_hypSeriesQuad
  rw [hconst] at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hconst]
  linarith

/-- The base case `16 b₂ = 9 b₁`, from the first coefficient of `hypSeriesQuad_ode`. -/
theorem hypSeriesQuad_coeff_rec_one :
    16 * PowerSeries.coeff 2 hypSeriesQuad = 9 * PowerSeries.coeff 1 hypSeriesQuad := by
  have h := congrArg (PowerSeries.coeff 1) hypSeriesQuad_ode_expand
  simp only [map_sub, map_add, map_zero, PowerSeries.coeff_C_mul,
    show (4 : PowerSeries ℝ) = PowerSeries.C 4 from rfl,
    show (8 : PowerSeries ℝ) = PowerSeries.C 8 from rfl,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_derivative] at h
  norm_num at h
  linarith

/-- The full coefficient recurrence of `hypSeriesQuad`, in the form consumed by
`eq_hypCoeff_half_half_one_of_ratio`. -/
theorem hypSeriesQuad_coeff_rec_all (n : ℕ) :
    4 * ((n : ℝ) + 1) ^ 2 * PowerSeries.coeff (n + 1) hypSeriesQuad
      = (2 * (n : ℝ) + 1) ^ 2 * PowerSeries.coeff n hypSeriesQuad := by
  rcases n with _ | _ | k
  · simpa using hypSeriesQuad_coeff_rec_zero
  · have h := hypSeriesQuad_coeff_rec_one
    norm_num at h ⊢
    exact h
  · have h := hypSeriesQuad_coeff_rec k
    push_cast at h ⊢
    convert h using 2 <;> ring

/-- The quadratic transformation in formal power series:
`₂F₁(1/4,1/4;1;4X(1-X)) = ₂F₁(1/2,1/2;1;X)`. -/
theorem hypSeriesQuad_eq_hypSeries_half :
    hypSeriesQuad = hypSeries (1 / 2) (1 / 2) 1 := by
  have hratio : ∀ n : ℕ, PowerSeries.coeff (n + 1) hypSeriesQuad
      = PowerSeries.coeff n hypSeriesQuad
        * ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) ^ 2 := by
    intro n
    have h := hypSeriesQuad_coeff_rec_all n
    field_simp
    linear_combination h
  ext n
  rw [eq_hypCoeff_half_half_one_of_ratio
    (u := fun n => PowerSeries.coeff n hypSeriesQuad) coeff_zero_hypSeriesQuad hratio n,
    coeff_hypSeries]

/-- The `m`-th power of the quadratic substitution, evaluated at `z`:
`∑ₙ [Xⁿ]((4X(1-X))^m) · zⁿ = (4z(1-z))^m`. This is the inner sum in the re-expansion of
`₂F₁(1/4,1/4;1;4z(1-z))` in powers of `z`; it is a formal polynomial identity, and it holds
without any convergence hypothesis on `z`. -/
-- Theorem: `∑' n, coeff n (quadSubst^m) * z^n = (4*z*(1-z))^m`.
theorem tsum_coeff_quadSubst_pow (m : ℕ) (z : ℝ) :
    (∑' n : ℕ, PowerSeries.coeff n (quadSubst ^ m) * z ^ n) = (4 * z * (1 - z)) ^ m := by
  set q : Polynomial ℝ := 4 * Polynomial.X * (1 - Polynomial.X) with hq
  have hcoeq : quadSubst = (q : PowerSeries ℝ) := by
    have h4 : ((4 : Polynomial ℝ) : PowerSeries ℝ) = (4 : PowerSeries ℝ) := by
      rw [show (4 : Polynomial ℝ) = Polynomial.C 4 from rfl, Polynomial.coe_C]
      rfl
    rw [hq, quadSubst]
    push_cast
    rw [h4]
  have hpow : quadSubst ^ m = ((q ^ m : Polynomial ℝ) : PowerSeries ℝ) := by
    rw [hcoeq]
    exact (map_pow (Polynomial.coeToPowerSeries.ringHom) q m).symm
  rw [hpow]
  simp only [Polynomial.coeff_coe]
  rw [tsum_eq_sum (s := Finset.range ((q ^ m).natDegree + 1)) ?_]
  · rw [← Polynomial.eval_eq_sum_range, Polynomial.eval_pow]
    have hqeval : q.eval z = 4 * z * (1 - z) := by
      rw [hq]
      simp
    rw [hqeval]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

/-- `quadSubst = 4X(1-X)` has zero constant term, so its `m`-th power has order at least
`m`; in particular its coefficients of degree below `m` vanish. This is what makes the
re-expansion of `₂F₁(1/4,1/4;1;4z(1-z))` finitely supported in each degree. -/
-- Theorem: if `n < m` then `coeff n (quadSubst^m) = 0`.
theorem coeff_quadSubst_pow_eq_zero_of_lt {m n : ℕ} (h : n < m) :
    PowerSeries.coeff n (quadSubst ^ m) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  have hconst : PowerSeries.constantCoeff quadSubst = 0 := by simp [quadSubst]
  have hle : m ≤ (quadSubst ^ m).order :=
    PowerSeries.le_order_pow_of_constantCoeff_eq_zero m hconst
  exact lt_of_lt_of_le (by exact_mod_cast h) hle

/-! ### The coefficient formula for `quadSubst^m`

The re-expansion of `(4z(1-z))^m` has the explicit coefficients
`[X^(m+j)]((4X(1-X))^m) = 4^m (-1)^j C(m,j)`, so the power `quadSubst^m` is dominated at
`|z| ≤ 1` by the geometric quantity `(4|z|(1+|z|))^m`. This is the majorant that makes the
double sum `c_m · [Xⁿ](quadSubst^m) · zⁿ` summable on a disc around the origin, which is what
the analytic transfer of V6 needs. -/

/-- The polynomial `4X(1-X)` behind the quadratic substitution. -/
def quadPoly : Polynomial ℝ := Polynomial.C 4 * Polynomial.X * (1 - Polynomial.X)

/-- `quadSubst` is the power-series coercion of `quadPoly`. -/
-- Theorem: quadSubst is the power-series coercion of quadPoly.
theorem quadSubst_eq_quadPoly : quadSubst = (quadPoly : PowerSeries ℝ) := by
  rw [quadPoly, quadSubst]
  push_cast
  rfl

/-- The power-series power `quadSubst^m` is the coercion of the polynomial power. -/
-- Theorem: quadSubst^m = ((quadPoly^m : Polynomial ℝ) : PowerSeries ℝ).
theorem quadSubst_pow_eq_quadPoly (m : ℕ) :
    quadSubst ^ m = ((quadPoly ^ m : Polynomial ℝ) : PowerSeries ℝ) := by
  rw [quadSubst_eq_quadPoly]
  exact (map_pow (Polynomial.coeToPowerSeries.ringHom) quadPoly m).symm

/-- The binomial expansion of `(4X(1-X))^m` as a polynomial. -/
-- Theorem: quadPoly^m = ∑_{j ≤ m} C(4^m C(m,j) (-1)^j) X^(m+j).
theorem quadPoly_pow_eq (m : ℕ) :
    quadPoly ^ m = ∑ j ∈ Finset.range (m + 1),
      Polynomial.C (4 ^ m * (Nat.choose m j : ℝ) * (-1) ^ j) * Polynomial.X ^ (m + j) := by
  apply Polynomial.funext
  intro z
  simp only [quadPoly, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_finsetSum]
  exact pow_four_mul_one_sub_pow m z

/-- The coefficients of `quadSubst^m`: `[Xⁿ]((4X(1-X))^m) = 4^m (-1)^(n-m) C(m, n-m)` for
`m ≤ n` (the binomial coefficient vanishing covers `n > 2m`). -/
-- Theorem: for m ≤ n, coeff n (quadSubst^m) = 4^m (-1)^(n-m) C(m, n-m).
theorem coeff_quadSubst_pow_eq {m n : ℕ} (hmn : m ≤ n) :
    PowerSeries.coeff n (quadSubst ^ m) =
      4 ^ m * (-1 : ℝ) ^ (n - m) * (m.choose (n - m) : ℝ) := by
  rw [quadSubst_pow_eq_quadPoly, Polynomial.coeff_coe, quadPoly_pow_eq,
    Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (n - m)]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos (show n = m + (n - m) by omega)]
    ring
  · intro b hb hne
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (by
      intro hcon
      exact hne (by omega))]
  · intro hmem
    rw [Polynomial.coeff_C_mul_X_pow, if_pos (show n = m + (n - m) by omega)]
    have hlt : m < n - m := by
      rw [Finset.mem_range, not_lt] at hmem
      omega
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp

/-- The geometric majorant: `∑ₙ |[Xⁿ](quadSubst^m)| |z|ⁿ = (4|z|(1+|z|))^m`. -/
-- Theorem: ∑' n, ‖coeff n (quadSubst^m)‖ |z|^n = (4|z|(1+|z|))^m.
theorem tsum_abs_coeff_quadSubst_pow (m : ℕ) (z : ℝ) :
    (∑' n : ℕ, ‖PowerSeries.coeff n (quadSubst ^ m)‖ * |z| ^ n) =
      (4 * |z| * (1 + |z|)) ^ m := by
  have hterm : ∀ n : ℕ, ‖PowerSeries.coeff n (quadSubst ^ m)‖ * |z| ^ n
      = (-1 : ℝ) ^ m * (PowerSeries.coeff n (quadSubst ^ m) * (-|z|) ^ n) := by
    intro n
    rcases lt_or_ge n m with hlt | hmn
    · rw [coeff_quadSubst_pow_eq_zero_of_lt hlt]
      simp
    · rw [coeff_quadSubst_pow_eq hmn]
      have habs : ‖4 ^ m * (-1 : ℝ) ^ (n - m) * (m.choose (n - m) : ℝ)‖
          = 4 ^ m * (m.choose (n - m) : ℝ) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ m)]
        rw [abs_pow, abs_neg, abs_one]
        rw [abs_of_nonneg (Nat.cast_nonneg (m.choose (n - m)))]
        simp
      rw [habs, show (-|z|) = (-1) * |z| by ring, mul_pow]
      have hsign : (-1 : ℝ) ^ m * (-1) ^ (n - m) * (-1) ^ n = 1 := by
        rw [← pow_add, ← pow_add, show m + (n - m) + n = 2 * n by omega]
        exact Even.neg_one_pow (even_two_mul n)
      calc 4 ^ m * (m.choose (n - m) : ℝ) * |z| ^ n
          = 4 ^ m * (m.choose (n - m) : ℝ) * |z| ^ n
              * ((-1) ^ m * (-1) ^ (n - m) * (-1) ^ n) := by rw [hsign, mul_one]
        _ = (-1) ^ m * ((4 ^ m * (-1) ^ (n - m) * (m.choose (n - m) : ℝ))
              * ((-1) ^ n * |z| ^ n)) := by ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_coeff_quadSubst_pow m (-|z|)]
  rw [show (4 : ℝ) * (-|z|) * (1 - (-|z|)) = (-1) * (4 * |z| * (1 + |z|)) by ring, mul_pow]
  have hsq : (-1 : ℝ) ^ m * (-1) ^ m = 1 := by
    rw [← pow_add, show m + m = 2 * m by ring]
    exact Even.neg_one_pow (even_two_mul m)
  rw [← mul_assoc, hsq, one_mul]

/-- `quadSubst^m` has degree at most `2m`, so its coefficients vanish beyond `2m`. -/
-- Theorem: 2m < n → coeff n (quadSubst^m) = 0.
theorem coeff_quadSubst_pow_eq_zero_of_gt {m n : ℕ} (h : 2 * m < n) :
    PowerSeries.coeff n (quadSubst ^ m) = 0 := by
  rw [coeff_quadSubst_pow_eq (m := m) (n := n) (by omega),
    Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

/-- The double family `c_m · [Xⁿ](quadSubst^m) · zⁿ` of the re-expansion is summable on the
disc `4|z|(1+|z|) < 1`. Its rows are finite sums (`[Xⁿ](quadSubst^m) = 0` for `n > 2m`) and
its iterated sum is `∑_m ‖c_m‖ (4|z|(1+|z|))ᵐ`, summable by `hasSum_hyp`. -/
-- Theorem: the double family of the re-expansion is summable on 4|z|(1+|z|) < 1.
theorem summable_quadFamily {z : ℝ} (hz : 4 * |z| * (1 + |z|) < 1) :
    Summable (fun p : ℕ × ℕ =>
      hypCoeff (1 / 4) (1 / 4) 1 p.1 * PowerSeries.coeff p.2 (quadSubst ^ p.1) * z ^ p.2) := by
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hBnn : 0 ≤ 4 * |z| * (1 + |z|) :=
    mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg z)) (by linarith [abs_nonneg z])
  have hB : |4 * |z| * (1 + |z|)| < 1 := by rwa [abs_of_nonneg hBnn]
  apply Summable.of_norm
  rw [summable_prod_of_nonneg (f := fun p : ℕ × ℕ =>
    ‖hypCoeff (1 / 4) (1 / 4) 1 p.1 * PowerSeries.coeff p.2 (quadSubst ^ p.1) * z ^ p.2‖)
    (fun p => norm_nonneg _)]
  constructor
  · intro m
    apply summable_of_ne_finset_zero (s := Finset.range (2 * m + 1))
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have h0 : PowerSeries.coeff n (quadSubst ^ m) = 0 :=
      coeff_quadSubst_pow_eq_zero_of_gt (m := m) (n := n) (by omega)
    rw [h0]
    simp
  · have hsum : ∀ m : ℕ, (∑' n : ℕ,
        ‖hypCoeff (1 / 4) (1 / 4) 1 m * PowerSeries.coeff n (quadSubst ^ m) * z ^ n‖)
        = ‖hypCoeff (1 / 4) (1 / 4) 1 m‖ * (4 * |z| * (1 + |z|)) ^ m := by
      intro m
      rw [show (fun n : ℕ => ‖hypCoeff (1 / 4) (1 / 4) 1 m
            * PowerSeries.coeff n (quadSubst ^ m) * z ^ n‖)
          = fun n : ℕ => ‖hypCoeff (1 / 4) (1 / 4) 1 m‖
            * (‖PowerSeries.coeff n (quadSubst ^ m)‖ * |z| ^ n) by
        funext n
        simp only [norm_mul, norm_pow, Real.norm_eq_abs]
        ring]
      rw [tsum_mul_left, tsum_abs_coeff_quadSubst_pow]
    simp_rw [hsum]
    refine ((hasSum_hyp (a := (1 : ℝ) / 4) (b := (1 : ℝ) / 4) (c := (1 : ℝ))
      (z := 4 * |z| * (1 + |z|)) hB hc).summable.abs).congr fun m => ?_
    calc ‖hypCoeff (1 / 4) (1 / 4) 1 m * (4 * |z| * (1 + |z|)) ^ m‖
        = ‖hypCoeff (1 / 4) (1 / 4) 1 m‖ * ‖(4 * |z| * (1 + |z|)) ^ m‖ := norm_mul _ _
      _ = ‖hypCoeff (1 / 4) (1 / 4) 1 m‖ * ‖4 * |z| * (1 + |z|)‖ ^ m := by rw [norm_pow]
      _ = ‖hypCoeff (1 / 4) (1 / 4) 1 m‖ * (4 * |z| * (1 + |z|)) ^ m := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hBnn]

/-- The double family whose summation is the re-expansion of `₂F₁(1/4,1/4;1;4z(1-z))` in
powers of `z`: the `(m,n)` term is `c_m · [Xⁿ]((4X(1-X))^m) · zⁿ`. -/
def quadFamily (z : ℝ) : ℕ × ℕ → ℝ := fun p =>
  hypCoeff (1 / 4) (1 / 4) 1 p.1 * PowerSeries.coeff p.2 (quadSubst ^ p.1) * z ^ p.2

/-- The `n`-th coefficient of the re-expanded series, read off the formal identity
`H(4X(1-X)) = ₂F₁(1/2,1/2;1;X)`: `∑_d [Xᵈ]H · [Xⁿ]((4X(1-X))ᵈ) = hypCoeff (1/2)(1/2)1 n`.
The `d`-sum is finite because `[Xⁿ]((4X(1-X))ᵈ) = 0` for `d > n`. -/
-- Theorem: ∑' d, c_d [Xⁿ]((4X(1-X))^d) = hypCoeff (1/2) (1/2) 1 n.
theorem tsum_hypCoeff_mul_coeff_quadSubst (n : ℕ) :
    (∑' d : ℕ, hypCoeff (1 / 4) (1 / 4) 1 d * PowerSeries.coeff n (quadSubst ^ d))
      = hypCoeff (1 / 2) (1 / 2) 1 n := by
  have hsupp : ∀ d ∉ Finset.range (n + 1),
      hypCoeff (1 / 4) (1 / 4) 1 d * PowerSeries.coeff n (quadSubst ^ d) = 0 := by
    intro d hd
    rw [Finset.mem_range, not_lt] at hd
    rw [coeff_quadSubst_pow_eq_zero_of_lt (by omega), mul_zero]
  have hsupp' : Function.support (fun d : ℕ =>
      hypCoeff (1 / 4) (1 / 4) 1 d • PowerSeries.coeff n (quadSubst ^ d))
      ⊆ ↑(Finset.range (n + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    by_contra hcon
    exact hd (by rw [smul_eq_mul]; exact hsupp d hcon)
  have hsub := PowerSeries.coeff_subst' hasSubst_quadSubst (hypSeries (1 / 4) (1 / 4) 1) n
  rw [show PowerSeries.subst quadSubst (hypSeries (1 / 4) (1 / 4) 1)
      = hypSeries (1 / 2) (1 / 2) 1 from hypSeriesQuad_eq_hypSeries_half] at hsub
  simp only [coeff_hypSeries] at hsub
  rw [hsub, tsum_eq_sum hsupp, finsum_eq_sum_of_support_subset _ hsupp']
  simp only [smul_eq_mul]

/-- The re-expansion of `₂F₁(1/4,1/4;1;4z(1-z))` as a power series in `z` converges to it on
the disc `4|z|(1+|z|) < 1`: the double family `quadFamily z` is summable, its iterated sum is
`₂F₁(1/4,1/4;1;4z(1-z))`, and its fibre sums are the coefficients of `₂F₁(1/2,1/2;1;·)`. -/
-- Theorem: the re-expansion converges to `hyp (1/4)(1/4)1 (4z(1-z))` on 4|z|(1+|z|) < 1.
theorem hasSum_quadFamily {z : ℝ} (hz : 4 * |z| * (1 + |z|) < 1) :
    HasSum (fun n : ℕ => hypCoeff (1 / 2) (1 / 2) 1 n * z ^ n)
      (hyp (1 / 4) (1 / 4) 1 (4 * z * (1 - z))) := by
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hzB : |4 * z * (1 - z)| < 1 := by
    have h1z : |1 - z| ≤ 1 + |z| := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [neg_abs_le z, le_abs_self z]
    calc |4 * z * (1 - z)| = 4 * |z| * |1 - z| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      _ ≤ 4 * |z| * (1 + |z|) :=
          mul_le_mul_of_nonneg_left h1z (mul_nonneg (by norm_num) (abs_nonneg z))
      _ < 1 := hz
  have hg : Summable (quadFamily z) := summable_quadFamily hz
  have hrow : ∀ m : ℕ, (∑' n : ℕ, quadFamily z (m, n))
      = hypCoeff (1 / 4) (1 / 4) 1 m * (4 * z * (1 - z)) ^ m := by
    intro m
    change (∑' n : ℕ, hypCoeff (1 / 4) (1 / 4) 1 m * PowerSeries.coeff n (quadSubst ^ m)
        * z ^ n) = hypCoeff (1 / 4) (1 / 4) 1 m * (4 * z * (1 - z)) ^ m
    rw [show (fun n : ℕ => hypCoeff (1 / 4) (1 / 4) 1 m * PowerSeries.coeff n (quadSubst ^ m)
          * z ^ n) = fun n : ℕ => hypCoeff (1 / 4) (1 / 4) 1 m
          * (PowerSeries.coeff n (quadSubst ^ m) * z ^ n) by
      funext n; ring]
    rw [tsum_mul_left, tsum_coeff_quadSubst_pow]
  have hcol : ∀ n : ℕ, (∑' m : ℕ, quadFamily z (m, n))
      = hypCoeff (1 / 2) (1 / 2) 1 n * z ^ n := by
    intro n
    change (∑' m : ℕ, hypCoeff (1 / 4) (1 / 4) 1 m * PowerSeries.coeff n (quadSubst ^ m)
        * z ^ n) = hypCoeff (1 / 2) (1 / 2) 1 n * z ^ n
    rw [show (fun m : ℕ => hypCoeff (1 / 4) (1 / 4) 1 m * PowerSeries.coeff n (quadSubst ^ m)
          * z ^ n) = fun m : ℕ => (hypCoeff (1 / 4) (1 / 4) 1 m
          * PowerSeries.coeff n (quadSubst ^ m)) * z ^ n by
      funext m; ring]
    rw [tsum_mul_right, tsum_hypCoeff_mul_coeff_quadSubst]
  have hfiber : ∀ n : ℕ, (∑' p : {p : ℕ × ℕ // p.2 = n}, quadFamily z p.val)
      = ∑' m : ℕ, quadFamily z (m, n) := by
    intro n
    let e : ℕ ≃ {p : ℕ × ℕ // p.2 = n} :=
      { toFun := fun m => ⟨(m, n), rfl⟩
        invFun := fun p => p.val.1
        left_inv := fun m => rfl
        right_inv := fun p => by
          obtain ⟨⟨a, b⟩, hb⟩ := p
          change b = n at hb
          subst hb
          rfl }
    rw [← Equiv.tsum_eq e (fun p : {p : ℕ × ℕ // p.2 = n} => quadFamily z p.val)]
    exact tsum_congr fun m => rfl
  have ha : (∑' p : ℕ × ℕ, quadFamily z p) = hyp (1 / 4) (1 / 4) 1 (4 * z * (1 - z)) := by
    rw [hg.tsum_prod]
    rw [show (fun m : ℕ => ∑' n : ℕ, quadFamily z (m, n))
        = fun m : ℕ => hypCoeff (1 / 4) (1 / 4) 1 m * (4 * z * (1 - z)) ^ m by
      funext m; exact hrow m]
    exact (hasSum_hyp hzB hc).tsum_eq
  have hfib := hg.hasSum.tsum_fiberwise (Prod.snd : ℕ × ℕ → ℕ)
  rw [ha] at hfib
  exact hfib.congr_fun fun n => by
    change hypCoeff (1 / 2) (1 / 2) 1 n * z ^ n
      = ∑' (p : {p : ℕ × ℕ // p.2 = n}), quadFamily z p.val
    rw [hfiber n, hcol n]

/-- V6 on the small disc `4|z|(1+|z|) < 1` (which contains `|z| < (√2-1)/2 ≈ 0.207`): the
quadratic transformation follows from the two `HasSum`s and uniqueness of sums. -/
-- Theorem: V6 on the disc 4|z|(1+|z|) < 1.
theorem hyp_quadratic_small {z : ℝ} (hz : 4 * |z| * (1 + |z|) < 1) :
    hyp (1 / 2) (1 / 2) 1 z = hyp (1 / 4) (1 / 4) 1 (4 * z * (1 - z)) := by
  have hz1 : |z| < 1 := by
    have h4 : 4 * |z| ≤ 4 * |z| * (1 + |z|) := by nlinarith [abs_nonneg z]
    linarith
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact (hasSum_hyp hz1 hc).unique (hasSum_quadFamily hz)

/-- V6, the symmetric quadratic transformation of the Gauss hypergeometric function:
`₂F₁(1/2,1/2;1;z) = ₂F₁(1/4,1/4;1;4z(1-z))` for `0 ≤ z < 1/2`.

The small-disc identity `hyp_quadratic_small` is extended to `[0, 1/2)` by analytic
continuation on the Cassini interval `((1-√2)/2, 1/2)`, where `|z| < 1` and `|4z(1-z)| < 1`
so both sides are analytic (`hyp` is the sum of its power series on the unit disc) and they
agree near the origin. -/
-- Theorem: V6, `hyp (1/2)(1/2)1 z = hyp (1/4)(1/4)1 (4z(1-z))` for `0 ≤ z < 1/2`.
theorem hyp_quadratic {z : ℝ} (hz0 : 0 ≤ z) (hz : z < 1 / 2) :
    hyp (1 / 2) (1 / 2) 1 z = hyp (1 / 4) (1 / 4) 1 (4 * z * (1 - z)) := by
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n h
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hzlt : ∀ w ∈ Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2), |w| < 1 := by
    intro w hw
    rw [Set.mem_Ioo] at hw
    obtain ⟨hwl, hwr⟩ := hw
    rw [abs_lt]
    constructor <;> nlinarith [hr, hrnn]
  have hwlt : ∀ w ∈ Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2), |4 * w * (1 - w)| < 1 := by
    intro w hw
    rw [Set.mem_Ioo] at hw
    obtain ⟨hwl, hwr⟩ := hw
    rw [abs_lt]
    constructor
    · have hneg : (w - (1 - Real.sqrt 2) / 2) * (w - (1 + Real.sqrt 2) / 2) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by linarith)
      nlinarith [hneg, hr]
    · nlinarith [sq_pos_of_ne_zero (show 2 * w - 1 ≠ 0 by linarith)]
  have hF : AnalyticOnNhd ℝ (fun w : ℝ => hyp (1 / 2) (1 / 2) 1 w)
      (Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2)) := by
    let S : FormalMultilinearSeries ℝ ℝ ℝ :=
      ordinaryHypergeometricSeries ℝ ((1 : ℝ) / 2) ((1 : ℝ) / 2) (1 : ℝ)
    have hrad : (1 : ℝ≥0∞) ≤ S.radius :=
      one_le_hypergeometric_radius (a := (1 : ℝ) / 2) (b := (1 : ℝ) / 2) (c := (1 : ℝ)) hc
    have hpos : 0 < S.radius := lt_of_lt_of_le (by norm_num) hrad
    refine ((S.hasFPowerSeriesOnBall hpos).analyticOnNhd).mono fun w hw => ?_
    have hw1 : (‖w‖ₑ : ℝ≥0∞) < 1 := by
      rw [enorm_eq_nnnorm]
      simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
      exact hzlt w hw
    rw [mem_eball_zero_iff]
    exact lt_of_lt_of_le hw1 hrad
  have hG : AnalyticOnNhd ℝ (fun w : ℝ => hyp (1 / 4) (1 / 4) 1 (4 * w * (1 - w)))
      (Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2)) := by
    let S : FormalMultilinearSeries ℝ ℝ ℝ :=
      ordinaryHypergeometricSeries ℝ ((1 : ℝ) / 4) ((1 : ℝ) / 4) (1 : ℝ)
    have hrad : (1 : ℝ≥0∞) ≤ S.radius :=
      one_le_hypergeometric_radius (a := (1 : ℝ) / 4) (b := (1 : ℝ) / 4) (c := (1 : ℝ)) hc
    have hpos : 0 < S.radius := lt_of_lt_of_le (by norm_num) hrad
    have houter : AnalyticOnNhd ℝ (fun w : ℝ => hyp (1 / 4) (1 / 4) 1 w)
        (Metric.eball 0 (1 : ℝ≥0∞)) :=
      ((S.hasFPowerSeriesOnBall hpos).analyticOnNhd).mono (Metric.eball_subset_eball hrad)
    have hinner : AnalyticOnNhd ℝ (fun w : ℝ => 4 * w * (1 - w))
        (Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2)) :=
      ((analyticOnNhd_const (v := (4 : ℝ))).mul analyticOnNhd_id).mul
        ((analyticOnNhd_const (v := (1 : ℝ))).sub analyticOnNhd_id)
    have hmaps : Set.MapsTo (fun w : ℝ => 4 * w * (1 - w))
        (Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2)) (Metric.eball 0 (1 : ℝ≥0∞)) := by
      intro w hw
      have hw1 : (‖4 * w * (1 - w)‖ₑ : ℝ≥0∞) < 1 := by
        rw [enorm_eq_nnnorm]
        simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
        exact hwlt w hw
      rw [mem_eball_zero_iff]
      exact hw1
    exact houter.comp hinner hmaps
  have hev : (fun w : ℝ => hyp (1 / 2) (1 / 2) 1 w) =ᶠ[𝓝 0]
      fun w : ℝ => hyp (1 / 4) (1 / 4) 1 (4 * w * (1 - w)) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 8))
      fun w hw => ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hw
    exact hyp_quadratic_small (by nlinarith [abs_nonneg w, hw])
  have h0 : (0 : ℝ) ∈ Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2) := by
    rw [Set.mem_Ioo]
    exact ⟨by nlinarith [hr, hrnn], by norm_num⟩
  have hzmem : z ∈ Set.Ioo ((1 - Real.sqrt 2) / 2) (1 / 2) := by
    rw [Set.mem_Ioo]
    exact ⟨by nlinarith [hr, hrnn, hz0], hz⟩
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hG isPreconnected_Ioo h0 hev hzmem

end

end Pconstructible
