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

-- Reference (empirical, not formalized in Lean): Wolfram Monte Carlo for Kac
-- septics (iid N(0,1) coeffs, `CountRoots`): 25,000 trials give ~54.8% one,
-- ~43.3% three, ~1.9% five, ~0.004% seven real roots; mean ~1.94, matching
-- the Kac integral E_7 ~ 1.9457. Uniform [-1,1] coeffs (20,000 trials):
-- ~57.6% / ~41.1% / ~1.3% / 0% with mean ~1.87. Odd counts only, as expected.

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
import Pptc.Basic
import Pptc.ScratchD
import Pptc.ScratchN
import Pptc.ScratchS
import Pptc.ScratchSep
import Mathlib.Data.Complex.Basic

open Polynomial Matrix

/-! # Pptc.DegreeSeven — investigation for issue #6

Issue #6 asks for the half of the degree-7 problem that survives #4:

> every real root of a degree-`7` polynomial with P-constructible coefficients that has at
> least one non-real root is P-constructible.

The plan of #4 is a degree-`≤ 6` Tschirnhaus map `y = φ x`. Writing `xᵢ` for the seven
roots of the septic and `yᵢ = φ xᵢ`, the resolvent `∏ (y - yᵢ)` has no `y⁶`, `y⁵`, `y⁴`
term exactly when the first three power sums vanish:

    p₁ = ∑ yᵢ = 0,   p₂ = ∑ yᵢ² = 0,   p₃ = ∑ yᵢ³ = 0.

The whole difficulty is *existence and constructibility* of such a `φ` over `ℝ`; the
engine `powerLaw_cubic_root_Pconstructible` and the recovery step
`root_Pconstructible_le_six_coeffs` are already in place.

This file records two things about that reduction.

## 1. The one-conjugate-pair case is not "a cubic form on a light cone"

The issue observes that for a septic with `s` conjugate pairs, `p₂` restricted to
`{p₁ = 0}` is a real quadratic form of negative index `s`, and proposes:

* `s ≥ 2`: the isotropic cone contains a projective line, restrict `p₃` to it, and a binary
  cubic always has a real root;
* `s = 1`: the cone is a light cone with no projective lines, so "a cubic form on the
  projectivised light cone of a signature-`(5,1)` form has a real zero" is needed.

That last general statement is **false**, and `lightCone_cubic_no_projective_zero` below is
a counterexample. On `ℝ⁶` with `Q = x₁² + ⋯ + x₅² - x₆²` (signature `(5,1)`) and the cubic
form `C = x₆³ - 2 x₆ (x₁² + ⋯ + x₅²)`, the only common real zero of `Q` and `C` is the
origin; on the null cone `C` collapses to `-x₆³`, which vanishes only at the origin. So no
argument of the form "any cubic form on the cone must vanish" can settle `s = 1`. The
obstruction is real: over the so-called "light cone" of `Q`, the real line bundle of cubic
forms has a nowhere-vanishing section (namely `x₆³`).

## 2. Why `s = 1` nevertheless works: `p₃` is an odd form in the real values

Write the roots as `u₁, …, u₅ : ℝ` together with a conjugate pair `a ± bi`, and let
`S = ∑ uᵢ`, `T = ∑ uᵢ²`. Then

    p₁ = S + 2a,     p₂ = T + 2(a² - b²),     p₃ = ∑ uᵢ³ + 2(a³ - 3 a b²).

Once `p₁ = p₂ = 0` are solved — `a = -S/2` and `b² = T/2 + S²/4` — the third power sum
becomes

    p₃ = (∑ uᵢ³) + S³/2 + (3/2) S T,

which is a homogeneous **cubic** in the five real values. Because the conjugate pair only
enters through `b²`, the `b` direction has dropped out of `p₃` entirely. An odd form in five
variables always has a nonzero zero (the sphere `S⁴` is connected, so an odd continuous
function on it changes sign), and here one zero is explicitly `u = (1, -1, 0, 0, 0)`:
`septic_one_pair_p3_eq` is the reduction identity, `septic_one_pair_Q_zero` checks that zero,
and `septic_one_pair_powerSums_zero` records the resulting value pattern
`1, -1, 0, 0, 0, i, -i` with all three power sums zero. So the `s = 1` case is algebraically
fine, and the numerics of #4 are explained.

## What is *not* settled here

Everything about producing `φ` — or, equivalently, the resolvent `R y = ∏ (y - yᵢ)` — from
the coefficients of the septic with P-constructible operations.

It is worth separating the two halves of that gap, because they have different characters.

* *Existence.* The value-level analysis above gives a real solution of `p₁ = p₂ = p₃ = 0`
  in which the conjugate pair enters only through `b²`; this is robust. It shows that the
  obstruction to `s = 1` is not an algebraic nonexistence and that the numerics are sound.
* *Constructibility.* The values `(1, -1, 0, 0, 0, i, -i)` sit at the seven roots, so the
  interpolation polynomial through them is `φ = V⁻¹ (values)`, and the entries of `V⁻¹`
  depend on the roots. Its coefficients are therefore not visibly P-constructible, and this
  is where the issue's "isotropic-vector" step (checklist item two) really lives: a
  *constructive* diagonalisation of `p₂` whose isotropic vectors are expressed in `φ`'s
  own coordinates, not in terms of the roots.

The `s = 1` cubic is genuinely more than a generic cubic form on the cone (that is the point
of part 1), and it is genuinely solvable (part 2), but the two uses of the word "genuinely"
do not meet in the current argument. That meeting is the open problem.

## 3. The classical context, and the exact open sub-problem

Killing the top three coefficients of the resolvent is the *Bring–Jerrard step*. The
classical account of it is geometric and is exactly the argument sketched in the issue: a
point `P` on `p₂ = 0` is found with a square root; a tangent space at `P` is taken, its
intersection with the quadric is a degree-`2` surface, a second square root selects one of
the two generators through `P`, and intersecting that generator with `p₃ = 0` is a cubic.
The 2021 translation, "On the Application of Tschirnhaus Transformations to the Reduction
of Algebraic Equations" (arXiv:2106.09247), records the point that matters here:

> Although only one pair of imaginary roots need to occur in the real equations
> `C₁ = C₂ = C₃ = 0`, at least two pairs of imaginary roots must exist to actually execute
> this transformation. Otherwise, there is no real line at `C₂ = 0`.

`C₂ = 0` is `p₂ = 0` on `{p₁ = 0}`, and "a real line" is a real projective line in that
quadric. That object exists precisely when the negative index is at least `2`, which is
precisely `s ≥ 2`. So the classical method is available exactly when `s ≥ 2` and genuinely
unavailable at `s = 1`, which is the same sharp edge that part 1 records. Part 2 shows the
equations are still *solvable* at `s = 1`; the classical paragraph says only that their
method is not the way.

The exact open sub-problem is therefore:

> Construct, from the coefficients of a real septic with `s = 1` conjugate pair and using
> only P-constructible operations, a degree-`≤ 6` polynomial `φ` whose resolvent has
> vanishing `y⁶`, `y⁵`, `y⁴` coefficients.

Equivalently, in the coefficient space `{p₁ = 0}` (dimension six) of the trace form `p₂`,
which has signature `(5,1)`: produce a P-constructible nonzero point of the light cone
`p₂ = 0` at which the reduced cubic `p₃` vanishes, without appealing to the intermediate
value theorem or to the topological `S⁴` argument, which establish existence but not
P-constructibility. Part 2 pins the value-level solution down; this is the same point
carried into `φ`'s own coordinates, which is where it stops being visible.

The `s ≥ 2` case is the one the classical method settles, and the pieces below
(`eval_root_Pconstructible`, `root_Pconstructible_of_powerLaw`) are the unconditional tail
of either case: once a suitable `φ` is in hand, the power-law engine and the sextic recover
`β`.
-/

namespace Pconstructible

/-! ### The one-conjugate-pair reduction -/

-- Theorem: the first three power sums of the seven values `1, -1, 0, 0, 0, i, -i` all
-- vanish. This is the explicit `s = 1` solution: five real roots carrying the values
-- `1, -1, 0, 0, 0` and one conjugate pair carrying `± i`.
theorem septic_one_pair_powerSums_zero :
    ((1 : ℂ) + (-1) + 0 + 0 + 0 + Complex.I + (-Complex.I) = 0) ∧
    ((1 : ℂ) ^ 2 + (-1) ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2
        + Complex.I ^ 2 + (-Complex.I) ^ 2 = 0) ∧
    ((1 : ℂ) ^ 3 + (-1) ^ 3 + 0 ^ 3 + 0 ^ 3 + 0 ^ 3
        + Complex.I ^ 3 + (-Complex.I) ^ 3 = 0) := by
  have hmI2 : (-Complex.I) ^ 2 = -1 := by
    rw [show (-Complex.I) ^ 2 = Complex.I ^ 2 by ring, Complex.I_sq]
  have hmI3 : (-Complex.I) ^ 3 = Complex.I := by
    rw [show (-Complex.I) ^ 3 = -(Complex.I ^ 3) by ring, Complex.I_pow_three]
    ring
  refine ⟨?_, ?_, ?_⟩
  · ring
  · rw [Complex.I_sq, hmI2]; ring
  · rw [Complex.I_pow_three, hmI3]; ring

-- Theorem: with `p₁ = 0` (`a = -S/2`) and `p₂ = 0` (`b² = T/2 + S²/4`) imposed, the third
-- power sum `p₃ = ∑ uᵢ³ + 2 (a³ - 3 a b²)` is the homogeneous cubic `∑ uᵢ³ + S³/2 + 3ST/2`
-- in the five real values. The conjugate pair survives only through `b²`, so the `b`
-- direction has disappeared from `p₃`.
theorem septic_one_pair_p3_eq (u₁ u₂ u₃ u₄ u₅ a b : ℝ)
    (ha : a = -(u₁ + u₂ + u₃ + u₄ + u₅) / 2)
    (hb : b ^ 2 = (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 + u₄ ^ 2 + u₅ ^ 2) / 2
      + (u₁ + u₂ + u₃ + u₄ + u₅) ^ 2 / 4) :
    (u₁ ^ 3 + u₂ ^ 3 + u₃ ^ 3 + u₄ ^ 3 + u₅ ^ 3) + 2 * (a ^ 3 - 3 * a * b ^ 2)
      = (u₁ ^ 3 + u₂ ^ 3 + u₃ ^ 3 + u₄ ^ 3 + u₅ ^ 3)
        + (u₁ + u₂ + u₃ + u₄ + u₅) ^ 3 / 2
        + (3 / 2) * (u₁ + u₂ + u₃ + u₄ + u₅)
          * (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 + u₄ ^ 2 + u₅ ^ 2) := by
  subst ha
  rw [hb]
  ring

-- Theorem: the reduced cubic `Q u = ∑ uᵢ³ + S³/2 + 3ST/2` vanishes at `u = (1, -1, 0, 0, 0)`.
-- This is the value-level witness that `p₁ = p₂ = p₃ = 0` is solvable with one conjugate
-- pair; the corresponding pair is `a = 0`, `b = 1`, i.e. the complex roots `± i`.
theorem septic_one_pair_Q_zero :
    (1 ^ 3 + (-1) ^ 3 + 0 ^ 3 + 0 ^ 3 + 0 ^ 3)
        + (1 + (-1) + 0 + 0 + 0) ^ 3 / 2
        + (3 / 2) * (1 + (-1) + 0 + 0 + 0)
          * (1 ^ 2 + (-1) ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2) = 0 := by
  norm_num

/-! ### The stated general lemma is false

The issue asks for "a cubic form on the projectivised light cone of a signature-`(5,1)`
form has a real zero". The form `Q` below has signature `(5,1)`, the form `C` is a nonzero
cubic, and yet `Q = C = 0` forces the point to be the origin: there is no projective zero.
-/

-- Theorem: the quadratic form `Q = ∑ xᵢ² - x₆²` (signature `(5,1)`) and the cubic form
-- `C = x₆³ - 2 x₆ ∑ xᵢ²` (sums over `i = 1, …, 5`) have no common nonzero real zero.
theorem lightCone_cubic_no_projective_zero
    {x₁ x₂ x₃ x₄ x₅ x₆ : ℝ}
    (hQ : x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2 - x₆ ^ 2 = 0)
    (hC : x₆ ^ 3 - 2 * x₆ * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2) = 0) :
    x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0 ∧ x₅ = 0 ∧ x₆ = 0 := by
  have hsum : x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2 = x₆ ^ 2 := by linarith
  have hx₆ : x₆ = 0 := by
    rw [hsum] at hC
    ring_nf at hC
    exact eq_zero_of_pow_eq_zero (show x₆ ^ 3 = 0 by linarith)
  have hsum0 : x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2 = 0 := by
    rw [hx₆] at hsum
    simpa using hsum
  have h1 : x₁ ^ 2 = 0 := by
    nlinarith [hsum0, sq_nonneg x₂, sq_nonneg x₃, sq_nonneg x₄, sq_nonneg x₅]
  have h2 : x₂ ^ 2 = 0 := by
    nlinarith [hsum0, sq_nonneg x₁, sq_nonneg x₃, sq_nonneg x₄, sq_nonneg x₅]
  have h3 : x₃ ^ 2 = 0 := by
    nlinarith [hsum0, sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₄, sq_nonneg x₅]
  have h4 : x₄ ^ 2 = 0 := by
    nlinarith [hsum0, sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃, sq_nonneg x₅]
  have h5 : x₅ ^ 2 = 0 := by
    nlinarith [hsum0, sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃, sq_nonneg x₄]
  exact ⟨sq_eq_zero_iff.mp h1, sq_eq_zero_iff.mp h2, sq_eq_zero_iff.mp h3,
    sq_eq_zero_iff.mp h4, sq_eq_zero_iff.mp h5, hx₆⟩

/-! ### The recovery step, isolated

Whatever eventually produces the value `y = φ β` of a degree-`≤ 6` Tschirnhaus map `φ`,
recovering `β` from it is always degree `≤ 6`: `β` is a root of `φ - C y`, which has the
same coefficients as `φ` except at `X ^ 0` and so is still P-constructible whenever `φ`
is. This is the last row of the issue's table, and it is unconditional. -/

-- Theorem: a nonconstant polynomial `φ` of degree at most 6 with P-constructible
-- coefficients has P-constructible roots over P-constructible values: if `φ β = y` and
-- `y` is P-constructible, then `β` is P-constructible.
theorem eval_root_Pconstructible {φ : Polynomial ℝ}
    (hcoeff : ∀ i, PConstructible (φ.coeff i)) (hdeg : φ.natDegree ≤ 6)
    (hne : φ.natDegree ≠ 0) {β y : ℝ} (hy : PConstructible y)
    (h : φ.eval β = y) :
    PConstructible β := by
  set ψ : Polynomial ℝ := φ - Polynomial.C y with hψ
  have hψcoeff : ∀ i, PConstructible (ψ.coeff i) := by
    intro i
    rw [hψ, Polynomial.coeff_sub]
    by_cases hi : i = 0
    · subst hi
      simp only [Polynomial.coeff_C, if_pos]
      exact PConstructible.sub (hcoeff 0) hy
    · simp only [Polynomial.coeff_C, if_neg hi, sub_zero]
      exact hcoeff i
  have hψdeg : ψ.natDegree ≤ 6 := by
    rw [hψ]
    refine le_trans (Polynomial.natDegree_sub_le φ (Polynomial.C y)) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hdeg
  have hψne : ψ ≠ 0 := by
    intro h0
    have hC : φ = Polynomial.C y := by rw [hψ, sub_eq_zero] at h0; exact h0
    rw [hC, Polynomial.natDegree_C] at hne
    exact hne rfl
  have hψroot : ψ.eval β = 0 := by
    rw [hψ, Polynomial.eval_sub, Polynomial.eval_C, h, sub_self]
  exact root_Pconstructible_le_six_coeffs hψne hψdeg hψcoeff hψroot

-- Theorem: the two steps that finish a degree-7 reduction once the Tschirnhaus map `φ`
-- and its power-law relation are in hand. If `φ` has P-constructible coefficients and
-- degree between `1` and `6`, and `y = φ β` satisfies `y ^ 7 = cubicVal c₀ c₁ c₂ c₃ y`
-- with P-constructible cubic coefficients, then `β` is P-constructible: first the
-- power-law engine makes `y` P-constructible, then `eval_root_Pconstructible` recovers
-- `β` from `φ - C y`.
theorem root_Pconstructible_of_powerLaw {φ : Polynomial ℝ}
    (hcoeff : ∀ i, PConstructible (φ.coeff i)) (hdeg : φ.natDegree ≤ 6)
    (hne : φ.natDegree ≠ 0) {β c₀ c₁ c₂ c₃ : ℝ}
    (h₀ : PConstructible c₀) (h₁ : PConstructible c₁) (h₂ : PConstructible c₂)
    (h₃ : PConstructible c₃)
    (h : (φ.eval β) ^ 7 = cubicVal c₀ c₁ c₂ c₃ (φ.eval β)) :
    PConstructible β :=
  eval_root_Pconstructible hcoeff hdeg hne
    (powerLaw_cubic_root_Pconstructible (by norm_num) h₀ h₁ h₂ h₃ h) rfl

/-! ### One P-constructible root yields all of them

A useful structural remark for the whole problem: the hypothesis "every real root is
P-constructible" collapses to "some real root is", because once one root `d` is in hand,
`q / (X - d)` has degree at most six and still kills every other root. The quotient is
built here by shifting `d` to the origin (bringing the root to `0`), dividing by `X`
(`Polynomial.divX`), and shifting back; both operations are `taylor`, whose coefficients
stay P-constructible by `taylor_coeff_Pconstructible`. -/

-- Theorem: if a nonzero polynomial `q` of degree at most 7 with P-constructible
-- coefficients has a P-constructible root `d`, then every other root `β` of `q` is
-- P-constructible. (`q / (X - d)` is a degree-`≤ 6` P-constructible polynomial killing `β`.)
theorem root_Pconstructible_of_other_root {q : Polynomial ℝ}
    (hq : ∀ i, PConstructible (q.coeff i)) (hqne : q ≠ 0) (hdeg : q.natDegree ≤ 7)
    {d β : ℝ} (hd : PConstructible d) (hdroot : q.eval d = 0) (hneq : β ≠ d)
    (hβ : q.eval β = 0) :
    PConstructible β := by
  set r : Polynomial ℝ := Polynomial.taylor d q with hrdef
  have hrcoeff : ∀ i, PConstructible (r.coeff i) := by
    intro i
    rw [hrdef]
    exact taylor_coeff_Pconstructible hq hd i
  have hr0 : r.coeff 0 = 0 := by
    rw [hrdef, Polynomial.taylor_coeff_zero, hdroot]
  set s : Polynomial ℝ := r.divX with hsdef
  have hsc : ∀ i, PConstructible (s.coeff i) := by
    intro i
    rw [hsdef, Polynomial.coeff_divX]
    exact hrcoeff (i + 1)
  have hs_eq : Polynomial.X * s = r := by
    have h := Polynomial.X_mul_divX_add r
    rw [hr0, Polynomial.C_0, add_zero] at h
    rw [hsdef]
    exact h
  set φ : Polynomial ℝ := Polynomial.taylor (-d) s with hφdef
  have hφc : ∀ i, PConstructible (φ.coeff i) := by
    intro i
    rw [hφdef]
    exact taylor_coeff_Pconstructible hsc (neg_Pconstructible hd) i
  have hq_eq : q = (Polynomial.X - Polynomial.C d) * φ := by
    calc q = Polynomial.taylor (-d) r := by
            rw [hrdef, Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
      _ = Polynomial.taylor (-d) (Polynomial.X * s) := by rw [hs_eq]
      _ = Polynomial.taylor (-d) Polynomial.X * Polynomial.taylor (-d) s := by
            rw [Polynomial.taylor_mul]
      _ = (Polynomial.X - Polynomial.C d) * φ := by
            rw [hφdef, Polynomial.taylor_X, Polynomial.C_neg]
            ring
  have hφne : φ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq_eq
    exact hqne hq_eq
  have hφdeg : φ.natDegree ≤ 6 := by
    have hmul := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero d) hφne
    rw [hq_eq, hmul, Polynomial.natDegree_X_sub_C] at hdeg
    omega
  have hφβ : φ.eval β = 0 := by
    have h : q.eval β = (β - d) * φ.eval β := by
      have := congrArg (fun p : Polynomial ℝ => p.eval β) hq_eq
      simpa using this
    rw [hβ] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr hneq)
  exact root_Pconstructible_le_six_coeffs hφne hφdeg hφc hφβ

/-! ### The isotropic-vector step, in the scalar form the construction uses

The constructive route the issue asks for works on the *line* joining a direction `v` on
which the trace form is negative to a direction `u` on which it is positive. Along
`v + t u` the form is the quadratic `a t² + 2 b t + c` with `a = p₂ u > 0` and `c = p₂ v <
0`, so it crosses zero at a positive `t` given by the quadratic formula. That root involves
only a square root of a rational function of `a, b, c`, and is therefore P-constructible as
soon as `a, b, c` are. This is the step labelled "diagonalise an indefinite real quadratic
form and read off an isotropic vector — square roots only" in the issue. -/

-- Theorem: a real quadratic `a t² + 2 b t + c` with positive leading coefficient `a` and
-- negative constant term `c` has a positive, P-constructible root whenever `a, b, c` are
-- P-constructible.
theorem exists_pos_quadratic_root {a b c : ℝ} (ha : PConstructible a)
    (hb : PConstructible b) (hc : PConstructible c) (hapos : 0 < a) (hcneg : c < 0) :
    ∃ t : ℝ, PConstructible t ∧ 0 < t ∧ a * t ^ 2 + 2 * b * t + c = 0 := by
  have hD : 0 < b ^ 2 - a * c := by nlinarith [sq_nonneg b, mul_pos hapos (neg_pos.mpr hcneg)]
  have hs : PConstructible (Real.sqrt (b ^ 2 - a * c)) :=
    sqrt_Pconstructible (PConstructible.sub (sq_Pconstructible hb) (PConstructible.mul ha hc))
  refine ⟨(-b + Real.sqrt (b ^ 2 - a * c)) / a, ?_, ?_, ?_⟩
  · exact PConstructible.div (PConstructible.add (neg_Pconstructible hb) hs) ha
  · have hb2 : b ^ 2 < b ^ 2 - a * c := by
      nlinarith [mul_pos hapos (neg_pos.mpr hcneg)]
    have habs : |b| < Real.sqrt (b ^ 2 - a * c) := by
      calc |b| = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
        _ < Real.sqrt (b ^ 2 - a * c) := Real.sqrt_lt_sqrt (sq_nonneg b) hb2
    have hnum : 0 < -b + Real.sqrt (b ^ 2 - a * c) := by
      have := (abs_lt.mp habs).2
      linarith
    exact div_pos hnum hapos
  · have hsq : Real.sqrt (b ^ 2 - a * c) ^ 2 = b ^ 2 - a * c := Real.sq_sqrt hD.le
    have hane : a ≠ 0 := ne_of_gt hapos
    field_simp
    linear_combination hsq

/-! ### The reduced cubic of the one-pair case

`septic_one_pair_p3_eq` gives the reduced third power sum as the cubic
`∑ uᵢ³ + S³ / 2 + 3 S T / 2` in the five real values `uᵢ`. It is worth naming it and
recording that it is homogeneous of degree three and odd, since that is exactly what
`septic_one_pair_powerSums_zero` exploits: on the sphere `S⁴` the odd function
`septicOnePairCubic` changes sign along any path from `u` to `-u`, so the circle of
values that the issue's "genuinely solvable" claim needs is not empty. -/

/-- The reduced cubic `∑ uᵢ³ + S³ / 2 + 3 S T / 2` in the five real values of the
one-conjugate-pair reduction. -/
noncomputable def septicOnePairCubic (u₁ u₂ u₃ u₄ u₅ : ℝ) : ℝ :=
  (u₁ ^ 3 + u₂ ^ 3 + u₃ ^ 3 + u₄ ^ 3 + u₅ ^ 3)
    + (u₁ + u₂ + u₃ + u₄ + u₅) ^ 3 / 2
    + (3 / 2) * (u₁ + u₂ + u₃ + u₄ + u₅)
      * (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 + u₄ ^ 2 + u₅ ^ 2)

-- Theorem: `septicOnePairCubic` is homogeneous of degree three.
theorem septicOnePairCubic_homogeneous (t u₁ u₂ u₃ u₄ u₅ : ℝ) :
    septicOnePairCubic (t * u₁) (t * u₂) (t * u₃) (t * u₄) (t * u₅)
      = t ^ 3 * septicOnePairCubic u₁ u₂ u₃ u₄ u₅ := by
  simp only [septicOnePairCubic]
  ring

-- Theorem: `septicOnePairCubic` is odd, so on the unit sphere in the five real values it
-- is an odd continuous function and vanishes along every path joining a point to its
-- antipode.
theorem septicOnePairCubic_neg (u₁ u₂ u₃ u₄ u₅ : ℝ) :
    septicOnePairCubic (-u₁) (-u₂) (-u₃) (-u₄) (-u₅)
      = -septicOnePairCubic u₁ u₂ u₃ u₄ u₅ := by
  simp only [septicOnePairCubic]
  ring

-- Theorem: the named cubic vanishes at the explicit nonzero values `(1, -1, 0, 0, 0)`.
theorem septicOnePairCubic_zero :
    septicOnePairCubic 1 (-1) 0 0 0 = 0 := by
  simp only [septicOnePairCubic]
  norm_num

/-! ### The `s ≥ 2` case: the Bring–Jerrard reduction is constructible

The algebraic engine is in `Pptc.ScratchS` (`exists_tschirnhaus_traces`) and
`Pptc.ScratchN` (`charpoly_aeval_coeff_6_5_4_eq_zero`): from two non-real roots in distinct
conjugate classes, a degree-`≤ 6` Tschirnhaus map `φ` with P-constructible coefficients and
vanishing first three trace power sums is produced, and its resolvent loses the `X⁶, X⁵, X⁴`
terms.  `resolvent_powerLaw` then gives the power-law relation `(φ β)⁷ = cubic…`, whose root
`φ β` is P-constructible by `powerLaw_cubic_root_Pconstructible`; `φ - C (φ β)` finally
recovers `β`. -/

-- Theorem: if a nonzero polynomial `φ` has `trace (aeval (companion7 q) φ) = 0`, then `φ` is
-- nonconstant. If `φ` were the nonzero constant `C c`, the trace would be `7 c ≠ 0`.
theorem natDegree_ne_zero_of_trace_zero {q φ : ℝ[X]}
    (hp1 : Matrix.trace (aeval (companion7 q) φ) = 0) (hφne : φ ≠ 0) :
    φ.natDegree ≠ 0 := by
  intro hdeg0
  obtain ⟨c, hc⟩ := (Polynomial.natDegree_eq_zero).mp hdeg0
  have htrace : Matrix.trace (aeval (companion7 q) φ) = 7 * c := by
    rw [← hc, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul,
      Matrix.trace_one, smul_eq_mul]
    norm_num
    ring
  rw [htrace] at hp1
  have hc0 : c = 0 := by linarith
  rw [hc0, Polynomial.C_0] at hc
  exact hφne hc.symm

-- Theorem: a real root `β` of a monic septic `q` with P-constructible coefficients and two
-- non-real roots `z, w` in distinct conjugate classes is P-constructible. This is the `s ≥ 2`
-- case of issue #6.  Separability is not assumed: if `q` is not separable, either the
-- normalised `gcd q q'` or the quotient of `q` by it has degree at most `6` and kills `β`,
-- and the sextic engine already recovers `β` (`ScratchSep`); only the separable case goes
-- through the Bring–Jerrard reduction.
theorem root_Pconstructible_of_two_conjugate_pairs_monic {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 7) (hq : ∀ k, PConstructible (q.coeff k))
    {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β := by
  by_cases hsep : q.Separable
  · obtain ⟨φ, hφc, hφdeg, hφne, hp1, hp2, hp3⟩ :=
      exists_tschirnhaus_traces q hmon hnat hsep hq hz hzim hw hwim hzw hzw'
    have hkill := charpoly_aeval_coeff_6_5_4_eq_zero hmon hnat hsep hp1 hp2 hp3
    have h7 : q.coeff 7 = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
    have hdeg : q.natDegree ≤ 7 := le_of_eq hnat
    obtain ⟨c₀, c₁, c₂, c₃, hc₀, hc₁, hc₂, hc₃, hpow⟩ :=
      resolvent_powerLaw hq hβ h7 hdeg hφc hkill
    exact root_Pconstructible_of_powerLaw hφc hφdeg
      (natDegree_ne_zero_of_trace_zero hp1 hφne) hc₀ hc₁ hc₂ hc₃ hpow
  · exact root_Pconstructible_of_nonSeparable hmon hq (le_of_eq hnat) hsep hβ

-- Theorem: a real root `β` of a septic `q` (not necessarily monic) with P-constructible
-- coefficients and two non-real roots `z, w` in distinct conjugate classes is P-constructible.
-- Dividing by the leading coefficient, itself a P-constructible coefficient of `q`, gives a
-- monic septic with the same complex roots, to which the monic case applies.
theorem root_Pconstructible_of_two_conjugate_pairs {q : ℝ[X]}
    (hnat : q.natDegree = 7) (hq : ∀ k, PConstructible (q.coeff k))
    {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β := by
  have hne : q ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  set q₀ : ℝ[X] := C q.leadingCoeff⁻¹ * q with hq₀
  have hmon : q₀.Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hnat₀ : q₀.natDegree = 7 := by
    rw [hq₀, Polynomial.natDegree_C_mul (inv_ne_zero hlc), hnat]
  have hq₀c : ∀ k, PConstructible (q₀.coeff k) :=
    C_mul_coeff_Pconstructible (inv_Pconstructible (hq q.natDegree)) hq
  have hroot : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 →
      (q₀.map (algebraMap ℝ ℂ)).eval x = 0 := by
    intro x hx
    simp [hq₀, Polynomial.map_mul, hx]
  exact root_Pconstructible_of_two_conjugate_pairs_monic hmon hnat₀ hq₀c (hroot z hz) hzim
    (hroot w hw) hwim hzw hzw' (by simp [hq₀, hβ])

end Pconstructible
