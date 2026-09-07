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

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`. This file is
-- deliberately independent of the rest of `Pptc`: it is pure Mathlib-style analysis, and
-- `Pptc.Gamma` imports it only for the statement at the bottom.
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Gauss's multiplication theorem at `k = 3`

Mathlib proves only the `k = 2` (Legendre) case of Gauss's multiplication theorem,
`Real.Gamma_mul_Gamma_add_half`. This file supplies the `k = 3` case,

`Γ(s) Γ(s + 1/3) Γ(s + 2/3) = 2π · 3 ^ (1/2 - 3s) · Γ(3s)`,

for every real `s`, by exactly the route Mathlib takes for duplication.

**Positive `s`, by Bohr–Mollerup.** The auxiliary function

`triplingGamma s = Γ(s/3) Γ(s/3 + 1/3) Γ(s/3 + 2/3) · 3 ^ (s - 1/2) / (2π)`

is positive and log-convex on `(0, ∞)`, satisfies `triplingGamma (s + 1) = s · triplingGamma s`
— the shift by `1` rotates the three arguments and turns the last one into `Γ(s/3 + 1)`, which
the recurrence converts back into `(s/3) Γ(s/3)`, while `3 ^ (s - 1/2)` gains the compensating
factor `3` — and takes the value `1` at `s = 1`, where reflection gives
`Γ(1/3) Γ(2/3) = π / sin(π/3) = 2π/√3` and the elementary factor is exactly `√3 / (2π)`.
Bohr–Mollerup (`Real.eq_Gamma_of_log_convex`) therefore identifies it with `Γ`, and
substituting `3s` for `s` is the theorem for `s > 0`.

**All `s`, by descent.** Both sides of the identity satisfy the *same* recurrence
`H (s + 1) = s (s + 1/3) (s + 2/3) · H s`: on the left because `Γ` does, on the right because
`Γ(3s + 3) = (3s)(3s + 1)(3s + 2) Γ(3s)` and `(3s)(3s+1)(3s+2)/27 = s(s+1/3)(s+2/3)`. So the
identity descends from `s + 1` to `s` whenever that common factor is nonzero, i.e. whenever
`s ∉ {0, -1/3, -2/3}`; and at those three points both sides vanish outright, since one of
`Γ(s)`, `Γ(s + 1/3)`, `Γ(s + 2/3)` is `Γ(0)` while `Γ(3s)` is `Γ(0)`, `Γ(-1)` or `Γ(-2)`.
Induction on the number of steps back to the positive half-line finishes it.
-/

open Set

namespace Real

/-- Auxiliary definition for the triplication formula: this will be shown to equal `Gamma s`,
by Bohr–Mollerup. -/
noncomputable def triplingGamma (s : ℝ) : ℝ :=
  Gamma (s / 3) * Gamma (s / 3 + 1 / 3) * Gamma (s / 3 + 2 / 3) * 3 ^ (s - 1 / 2) / (2 * π)

-- Theorem: `triplingGamma` satisfies the Gamma recurrence.
theorem triplingGamma_add_one (s : ℝ) (hs : s ≠ 0) :
    triplingGamma (s + 1) = s * triplingGamma s := by
  rw [triplingGamma, triplingGamma, show (s + 1) / 3 = s / 3 + 1 / 3 by ring,
    show s / 3 + 1 / 3 + 1 / 3 = s / 3 + 2 / 3 by ring,
    show s / 3 + 1 / 3 + 2 / 3 = s / 3 + 1 by ring,
    show s + 1 - 1 / 2 = s - 1 / 2 + 1 by ring,
    Gamma_add_one (div_ne_zero hs (by norm_num)),
    rpow_add (by norm_num : (0 : ℝ) < 3), rpow_one]
  ring

-- Theorem: `triplingGamma 1 = 1`; this is Euler's reflection formula at `1/3` together with
-- `sin (π/3) = √3/2`, and it is what pins down the constant `2π` in the theorem.
theorem triplingGamma_one : triplingGamma 1 = 1 := by
  have hrefl : Gamma (1 / 3 : ℝ) * Gamma (2 / 3) = 2 * π / √3 := by
    have h := Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
      show π * (1 / 3) = π / 3 by ring, sin_pi_div_three] at h
    rw [h]; ring
  have h3 : √(3 : ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr (by norm_num))
  rw [triplingGamma, show (1 : ℝ) / 3 + 1 / 3 = 2 / 3 by norm_num,
    show (1 : ℝ) / 3 + 2 / 3 = 1 by norm_num, Gamma_one, mul_one,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← sqrt_eq_rpow, hrefl]
  field_simp

-- Theorem: `log ∘ Gamma` stays convex after any order-preserving affine change of variable
-- `s ↦ s/3 + c` with `c ≥ 0`, since such a map sends `(0, ∞)` into `(0, ∞)`.
theorem convexOn_log_Gamma_div_three_add (c : ℝ) (hc : 0 ≤ c) :
    ConvexOn ℝ (Ioi (0 : ℝ)) fun s : ℝ => log (Gamma (s / 3 + c)) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [mem_Ioi] at hx hy
  have hx' : x / 3 + c ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
  have hy' : y / 3 + c ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
  have h := convexOn_log_Gamma.2 hx' hy' ha hb hab
  simp only [Function.comp_apply, smul_eq_mul] at h ⊢
  rw [show (a * x + b * y) / 3 + c = a * (x / 3 + c) + b * (y / 3 + c) by
    linear_combination (-c) * hab]
  exact h

-- Theorem: an affine function is convex on `(0, ∞)`; this covers the elementary factor
-- `3 ^ (s - 1/2) / (2π)`, whose logarithm is affine in `s`.
theorem convexOn_affine_Ioi (p q : ℝ) :
    ConvexOn ℝ (Ioi (0 : ℝ)) fun s : ℝ => s * p + q := by
  refine ⟨convex_Ioi 0, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩
  simp only [smul_eq_mul]
  linear_combination (-q) * hab

-- Theorem: `log ∘ triplingGamma` is convex on `(0, ∞)`, being a sum of three convex
-- reparametrizations of `log ∘ Gamma` and an affine term.
theorem triplingGamma_log_convex_Ioi : ConvexOn ℝ (Ioi (0 : ℝ)) (log ∘ triplingGamma) := by
  have h0 : ConvexOn ℝ (Ioi (0 : ℝ)) fun s : ℝ => log (Gamma (s / 3)) := by
    simpa using convexOn_log_Gamma_div_three_add 0 le_rfl
  have h1 := convexOn_log_Gamma_div_three_add (1 / 3) (by norm_num)
  have h2 := convexOn_log_Gamma_div_three_add (2 / 3) (by norm_num)
  have h3 := convexOn_affine_Ioi (log 3) (-(log 3 / 2 + log (2 * π)))
  refine (((h0.add h1).add h2).add h3).congr fun s hs => ?_
  simp only [mem_Ioi] at hs
  have g1 : Gamma (s / 3) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
  have g2 : Gamma (s / 3 + 1 / 3) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
  have g3 : Gamma (s / 3 + 2 / 3) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
  have g4 : (3 : ℝ) ^ (s - 1 / 2) ≠ 0 := (rpow_pos_of_pos (by norm_num) _).ne'
  have g5 : (2 : ℝ) * π ≠ 0 := by positivity
  simp only [Pi.add_apply, Function.comp_apply, triplingGamma]
  rw [log_div (mul_ne_zero (mul_ne_zero (mul_ne_zero g1 g2) g3) g4) g5,
    log_mul (mul_ne_zero (mul_ne_zero g1 g2) g3) g4, log_mul (mul_ne_zero g1 g2) g3,
    log_mul g1 g2, log_rpow (by norm_num)]
  ring

-- Theorem: `triplingGamma` is positive on `(0, ∞)`.
theorem triplingGamma_pos {s : ℝ} (hs : 0 < s) : 0 < triplingGamma s := by
  rw [triplingGamma]
  refine div_pos (mul_pos (mul_pos (mul_pos (Gamma_pos_of_pos (by linarith))
    (Gamma_pos_of_pos (by linarith))) (Gamma_pos_of_pos (by linarith)))
    (rpow_pos_of_pos (by norm_num) _)) (by positivity)

-- Theorem: Bohr–Mollerup identifies `triplingGamma` with `Gamma` on `(0, ∞)`.
theorem triplingGamma_eq_Gamma {s : ℝ} (hs : 0 < s) : triplingGamma s = Gamma s :=
  eq_Gamma_of_log_convex triplingGamma_log_convex_Ioi
    (fun {y} hy => triplingGamma_add_one y hy.ne') (fun {_y} hy => triplingGamma_pos hy)
    triplingGamma_one hs

-- Theorem: Gauss's multiplication theorem at `k = 3`, for positive real arguments.
theorem Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds_of_pos {s : ℝ} (hs : 0 < s) :
    Gamma s * Gamma (s + 1 / 3) * Gamma (s + 2 / 3)
      = 2 * π * (3 : ℝ) ^ ((1 : ℝ) / 2 - 3 * s) * Gamma (3 * s) := by
  have h := triplingGamma_eq_Gamma (show (0 : ℝ) < 3 * s by linarith)
  rw [triplingGamma, mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0)] at h
  have hp : (3 : ℝ) ^ (3 * s - 1 / 2) ≠ 0 := (rpow_pos_of_pos (by norm_num) _).ne'
  have hpi : π ≠ 0 := pi_ne_zero
  rw [← h, show (1 : ℝ) / 2 - 3 * s = -(3 * s - 1 / 2) by ring,
    rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  field_simp

-- Theorem: the descent step. Both sides of the identity obey the same recurrence, so knowing
-- it at `s + 1` gives it at `s` as soon as the common factor `s (s + 1/3) (s + 2/3)` is
-- nonzero.
theorem gauss_three_of_add_one {s : ℝ} (hs : s ≠ 0) (h1 : s + 1 / 3 ≠ 0)
    (h2 : s + 2 / 3 ≠ 0)
    (h : Gamma (s + 1) * Gamma (s + 1 + 1 / 3) * Gamma (s + 1 + 2 / 3)
      = 2 * π * (3 : ℝ) ^ ((1 : ℝ) / 2 - 3 * (s + 1)) * Gamma (3 * (s + 1))) :
    Gamma s * Gamma (s + 1 / 3) * Gamma (s + 2 / 3)
      = 2 * π * (3 : ℝ) ^ ((1 : ℝ) / 2 - 3 * s) * Gamma (3 * s) := by
  have n0 : (3 : ℝ) * s ≠ 0 := fun hc => hs (by linarith)
  have n1 : (3 : ℝ) * s + 1 ≠ 0 := fun hc => h1 (by linarith)
  have n2 : (3 : ℝ) * s + 1 + 1 ≠ 0 := fun hc => h2 (by linarith)
  rw [show s + 1 + 1 / 3 = s + 1 / 3 + 1 by ring, show s + 1 + 2 / 3 = s + 2 / 3 + 1 by ring,
    Gamma_add_one hs, Gamma_add_one h1, Gamma_add_one h2,
    show (1 : ℝ) / 2 - 3 * (s + 1) = (1 : ℝ) / 2 - 3 * s + -3 by ring,
    rpow_add (by norm_num : (0 : ℝ) < 3),
    show (3 : ℝ) ^ (-3 : ℝ) = 1 / 27 by
      rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, rpow_intCast]; norm_num,
    show 3 * (s + 1) = 3 * s + 1 + 1 + 1 by ring,
    Gamma_add_one n2, Gamma_add_one n1, Gamma_add_one n0] at h
  refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hs h1) h2) ?_
  linear_combination h

-- Theorem: the identity for every `s` lying at most `n` steps to the left of `(0, ∞)`.
theorem gauss_three_aux (n : ℕ) (s : ℝ) (hn : 0 < s + n) :
    Gamma s * Gamma (s + 1 / 3) * Gamma (s + 2 / 3)
      = 2 * π * (3 : ℝ) ^ ((1 : ℝ) / 2 - 3 * s) * Gamma (3 * s) := by
  have hm1 : Gamma (-1 : ℝ) = 0 := by simpa using Gamma_neg_nat_eq_zero 1
  have hm2 : Gamma (-2 : ℝ) = 0 := by simpa using Gamma_neg_nat_eq_zero 2
  induction n generalizing s with
  | zero =>
    exact Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds_of_pos (by simpa using hn)
  | succ n ih =>
    by_cases h0 : s = 0
    · subst h0; norm_num [Gamma_zero]
    by_cases h1 : s + 1 / 3 = 0
    · rw [show s = -(1 / 3 : ℝ) by linarith]
      norm_num [Gamma_zero, hm1]
    by_cases h2 : s + 2 / 3 = 0
    · rw [show s = -(2 / 3 : ℝ) by linarith]
      norm_num [Gamma_zero, hm2]
    refine gauss_three_of_add_one h0 h1 h2 (ih (s + 1) ?_)
    push_cast at hn
    linarith

end Real

/-- Gauss's multiplication theorem at `k = 3`:
`Γ(s) Γ(s + 1/3) Γ(s + 2/3) = 2π · 3 ^ (1/2 - 3s) · Γ(3s)`. Mathlib has only the `k = 2`
(Legendre) case, `Real.Gamma_mul_Gamma_add_half`. -/
theorem Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds (s : ℝ) :
    Real.Gamma s * Real.Gamma (s + 1 / 3) * Real.Gamma (s + 2 / 3)
      = 2 * Real.pi * (3 : ℝ) ^ ((1 : ℝ) / 2 - 3 * s) * Real.Gamma (3 * s) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-s)
  exact Real.gauss_three_aux n s (by linarith)
