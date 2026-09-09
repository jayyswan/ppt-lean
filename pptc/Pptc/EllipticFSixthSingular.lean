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
import Pptc.Basic
import Pptc.GaussMultiplicationK3
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # The sixth singular value of `K`

`K(k₆)² = Γ(1/24) Γ(5/24) Γ(7/24) Γ(11/24) / (384 π (√2 + 1) k₆)` at the sixth singular
modulus `k₆ = (2 - √3)(√3 - √2)`, the modulus at which `K'/K = √6`. This is Chowla-Selberg
at discriminant `-24`, for the field `ℚ(√-6)`, and it is the published evaluation: Borwein
and Borwein, *Pi and the AGM*, pp. 139 and 298; Borwein and Zucker, *Elliptic integral
evaluation of the Gamma function at rational values of small denominator*, IMA J. Numer.
Anal. **12** (1992), 519-526.

## What is proved here, and what is still assumed

`Pptc.EllipticFSecondSingular` evaluates `K(k₂)` outright, by a substitution that collapses
it into two Beta integrals. No analogue is available at `k₆`. The published derivations all
run through complex multiplication and the Kronecker limit formula, neither of which Mathlib
has; and a substitution of the second file's kind, if one exists, is not in the literature
and did not turn up in a direct search of the natural shapes it could take. What this file
does instead is split the statement into an elementary half and a transcendental half, and
prove the elementary half in full.

The four values `Γ(1/24), Γ(5/24), Γ(7/24), Γ(11/24)` satisfy three independent relations
coming from Gauss duplication, Gauss triplication and Euler reflection. Two of them are
proved below, and together they pin all four down in terms of a single one:

* `Gamma_twentyfourths_ratio`:
  `Γ(1/24) Γ(11/24) = (3√2 + √6)/2 · Γ(5/24) Γ(7/24)`, from triplication at
  `s = 1/24, 5/24, 7/24, 11/24` against reflection, whose sines collapse to
  `cot(π/12) = 2 + √3`. In the language of the level-`24` characters this is the `χ₁₂`
  part — the *real* quadratic field `ℚ(√3)`, whose fundamental unit `2 + √3` is
  elementary — and it is not what a singular value of `K` contributes.
* `Gamma_twentyfourths_reduce`:
  `Γ(5/24) Γ(7/24) Γ(11/24) Γ(1/12)² = 2 ^ (1/6) π √3 (√2 - 1)(√3 - √2)/3 · Γ(1/24)³`,
  from duplication at `s = 1/24, 5/24, 1/8`, triplication at `s = 1/24, 1/12` and
  reflection at `11/24, 7/24, 3/8, 1/4`. The `Γ(1/4)`s cancel in the product and
  triplication at `1/12` removes the last one.

Denominators `8` and `12` are already unconditional in `Pptc.Gamma`, so the second identity
says that exactly one number is missing at level `24`, namely `Γ(1/24)`; and the assumed
input `ellipticF_sixthSingular_beta` is precisely that number, in the shape Borwein and
Zucker give it. `ellipticF_sixthSingular` — the symmetric four-`Γ` form the rest of the
project wants — is then *derived*, not assumed.

Why no functional equation can close the gap: twist `Γ(a/24) ↦ t ^ χ(a) · Γ(a/24)` by the
quadratic character `χ` of discriminant `-24` (`+1` on `1, 5, 7, 11` and `-1` on
`13, 17, 19, 23`). The twist fixes `π`, every algebraic number, and every `Γ(a/n)` with
`n ∣ 8` or `n ∣ 12`; it preserves reflection and every Gauss multiplication relation at
level `24`, since `χ` sums to zero over each of the relevant residue sets — `{1, 13}` for
duplication, `{1, 9, 17}` for triplication, `{1, 7, 13, 19}` for `k = 4`; and it fixes both
identities above, since each is `χ`-balanced. But it multiplies `Γ(1/24)` by `t`. So the
functional equations fix the ratios and nothing more, and one genuinely new transcendental
input is needed. Chowla-Selberg at `-24` supplies exactly it.

Level `24` is where this circle of ideas ends. Every character of `(ℤ/24)ˣ` is quadratic —
`24` is the largest modulus for which that is true — so all four odd characters mod `24`
belong to imaginary quadratic fields (`ℚ(i)`, `ℚ(√-2)`, `ℚ(√-3)`, `ℚ(√-6)`), and
Chowla-Selberg has one CM period for each.
-/

namespace Pconstructible

/-! ### The modulus `k₆ = (2 - √3)(√3 - √2)` -/

/-- The sixth singular modulus `k₆ = (2 - √3)(√3 - √2)`, at which `K'/K = √6`. -/
noncomputable def sixthSingularMod : ℝ := (2 - Real.sqrt 3) * (Real.sqrt 3 - Real.sqrt 2)

-- Theorem: two nonnegative reals with equal squares are equal. The workhorse for turning
-- the squared ratio below into the ratio itself.
theorem eq_of_sq_eq_of_nonneg' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, h]

/-! ### Gauss triplication at level `24`

Triplication, `Γ(s) Γ(s + 1/3) Γ(s + 2/3) = 2π · 3 ^ (1/2 - 3s) · Γ(3s)`, sends each of the
four exponents `1/24, 5/24, 7/24, 11/24` to a triple whose other two members are again a
twenty-fourth and an eighth. At `s = 1/24` and `s = 11/24` the two powers of `3` multiply to
`3 ^ (-1/2)`, and at `s = 5/24` and `s = 7/24` they do the same, so the powers cancel between
the two pairs. So do the eighths, save for one factor: the upper pair overshoots `1` twice,
at `Γ(9/8) = Γ(1/8)/8` and `Γ(11/8) = 3 Γ(3/8)/8`, and the recurrence turns that mismatch
into the bare rational `(3/8)/(1/8) = 3` relating the two quadruple products. -/

-- Theorem: `Γ(9/8) = Γ(1/8)/8`, one of the two overshoots.
theorem Gamma_nine_eighths : Real.Gamma (9 / 8) = 1 / 8 * Real.Gamma (1 / 8) := by
  have h := Real.Gamma_add_one (s := (1 / 8 : ℝ)) (by norm_num)
  norm_num at h
  exact h

-- Theorem: `Γ(11/8) = 3 Γ(3/8)/8`, the other one.
theorem Gamma_eleven_eighths : Real.Gamma (11 / 8) = 3 / 8 * Real.Gamma (3 / 8) := by
  have h := Real.Gamma_add_one (s := (3 / 8 : ℝ)) (by norm_num)
  norm_num at h
  exact h

-- Theorem: the two level-`24` quadruple products that triplication pins down stand in the
-- ratio `3`. This is the whole arithmetic content the multiplication theorem contributes.
theorem Gamma_twentyfourths_triple :
    Real.Gamma (1 / 24) * Real.Gamma (11 / 24) * Real.Gamma (17 / 24) * Real.Gamma (19 / 24)
      = 3 * (Real.Gamma (5 / 24) * Real.Gamma (7 / 24) * Real.Gamma (13 / 24)
          * Real.Gamma (23 / 24)) := by
  have t1 := Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds (1 / 24 : ℝ)
  have t2 := Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds (11 / 24 : ℝ)
  have t3 := Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds (5 / 24 : ℝ)
  have t4 := Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds (7 / 24 : ℝ)
  norm_num at t1 t2 t3 t4
  rw [Gamma_nine_eighths] at t2
  rw [Gamma_eleven_eighths] at t2
  have h18 : (0 : ℝ) < Real.Gamma (1 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have h38 : (0 : ℝ) < Real.Gamma (3 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have h58 : (0 : ℝ) < Real.Gamma (5 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have h78 : (0 : ℝ) < Real.Gamma (7 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have hpow : (3 : ℝ) ^ ((3 : ℝ) / 8) * (3 : ℝ) ^ (-((7 : ℝ) / 8))
      = (3 : ℝ) ^ (-((1 : ℝ) / 8)) * (3 : ℝ) ^ (-((3 : ℝ) / 8)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hlow : Real.Gamma (5 / 24) * Real.Gamma (7 / 24) * Real.Gamma (13 / 24)
        * Real.Gamma (23 / 24)
      = 4 * Real.pi ^ 2 * ((3 : ℝ) ^ (-((1 : ℝ) / 8)) * (3 : ℝ) ^ (-((3 : ℝ) / 8))) := by
    refine mul_right_cancel₀ (b := Real.Gamma (5 / 8) * Real.Gamma (7 / 8)) (by positivity) ?_
    linear_combination (Real.Gamma (7 / 24) * Real.Gamma (5 / 8) * Real.Gamma (23 / 24)) * t3
      + (2 * Real.pi * (3 : ℝ) ^ (-((1 : ℝ) / 8)) * Real.Gamma (5 / 8)) * t4
  have hup : Real.Gamma (1 / 24) * Real.Gamma (11 / 24) * Real.Gamma (17 / 24)
        * Real.Gamma (19 / 24)
      = 12 * Real.pi ^ 2 * ((3 : ℝ) ^ ((3 : ℝ) / 8) * (3 : ℝ) ^ (-((7 : ℝ) / 8))) := by
    refine mul_right_cancel₀
      (b := 1 / 8 * (Real.Gamma (3 / 8) * Real.Gamma (1 / 8))) (by positivity) ?_
    linear_combination
      (Real.Gamma (11 / 24) * Real.Gamma (19 / 24) * (1 / 8 * Real.Gamma (1 / 8))) * t1
      + (2 * Real.pi * (3 : ℝ) ^ ((3 : ℝ) / 8) * Real.Gamma (1 / 8)) * t2
  rw [hup, hlow, hpow]
  ring

/-! ### Euler reflection at level `24`

The same eight `Γ`-values pair off under `x ↦ 1 - x` into `1/24 ↔ 23/24`, `5/24 ↔ 19/24`,
`7/24 ↔ 17/24`, `11/24 ↔ 13/24`, and reflection turns each pair into `π` over a sine of a
twenty-fourth of `π`. Two applications of `sin(π/2 - x) = cos x` and two of the double-angle
formula collapse the four sines into `sin(π/12)` and `cos(π/12)`, whose ratio is `cot(π/12)`;
that this equals `2 + √3` is the fundamental unit of `ℚ(√3)` showing up. -/

-- Theorem: `sin` is positive at every twenty-fourth of `π` used below.
theorem sin_pi_mul_pos {q : ℝ} (h0 : 0 < q) (h1 : q < 1) : 0 < Real.sin (Real.pi * q) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])

-- Theorem: reflection with its denominator cleared: `Γ(x) Γ(1 - x) sin(πx) = π`.
theorem Gamma_mul_Gamma_one_sub_mul_sin {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    Real.Gamma x * Real.Gamma (1 - x) * Real.sin (Real.pi * x) = Real.pi := by
  rw [Real.Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ (sin_pi_mul_pos h0 h1).ne']

/-! ### The ratio `Γ(1/24) Γ(11/24) / (Γ(5/24) Γ(7/24))` -/

-- Theorem: `((3√2 + √6)/2)² = 6 + 3√3`, the algebraic shape of the ratio's square.
theorem sq_three_sqrt_two_add_sqrt_six :
    ((3 * Real.sqrt 2 + Real.sqrt 6) / 2) ^ 2 = 6 + 3 * Real.sqrt 3 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h26 : Real.sqrt 2 * Real.sqrt 6 = 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), show (2 : ℝ) * 6 = 2 ^ 2 * 3 by norm_num,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [h2, h6, h26]

-- Theorem: **the elementary half of the sixth singular value.** The two `Γ`-products that a
-- Beta-integral evaluation of `K(k₆)` could produce differ by the algebraic factor
-- `(3√2 + √6)/2 = √(3(2 + √3))`. Triplication supplies the `3`, reflection the `2 + √3`.
theorem Gamma_twentyfourths_ratio :
    Real.Gamma (1 / 24) * Real.Gamma (11 / 24)
      = (3 * Real.sqrt 2 + Real.sqrt 6) / 2 * (Real.Gamma (5 / 24) * Real.Gamma (7 / 24)) := by
  have hA : (0 : ℝ) < Real.Gamma (1 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have hD : (0 : ℝ) < Real.Gamma (11 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have hB : (0 : ℝ) < Real.Gamma (5 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have hC : (0 : ℝ) < Real.Gamma (7 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have r1 := Gamma_mul_Gamma_one_sub_mul_sin (x := (1 : ℝ) / 24) (by norm_num) (by norm_num)
  have r2 := Gamma_mul_Gamma_one_sub_mul_sin (x := (11 : ℝ) / 24) (by norm_num) (by norm_num)
  have r3 := Gamma_mul_Gamma_one_sub_mul_sin (x := (5 : ℝ) / 24) (by norm_num) (by norm_num)
  have r4 := Gamma_mul_Gamma_one_sub_mul_sin (x := (7 : ℝ) / 24) (by norm_num) (by norm_num)
  norm_num at r1 r2 r3 r4
  -- the two `π²` groupings the triplication relation gets squeezed between
  have hAD : Real.Gamma (1 / 24) * Real.Gamma (23 / 24) * Real.sin (Real.pi * (1 / 24))
      * (Real.Gamma (11 / 24) * Real.Gamma (13 / 24) * Real.sin (Real.pi * (11 / 24)))
      = Real.pi ^ 2 := by rw [r1, r2]; ring
  have hBC : Real.Gamma (5 / 24) * Real.Gamma (19 / 24) * Real.sin (Real.pi * (5 / 24))
      * (Real.Gamma (7 / 24) * Real.Gamma (17 / 24) * Real.sin (Real.pi * (7 / 24)))
      = Real.pi ^ 2 := by rw [r3, r4]; ring
  -- multiplying the triplication relation by `Γ(1/24) Γ(11/24) Γ(5/24) Γ(7/24)` turns its
  -- four leftover `Γ`-values into exactly those two groupings
  have step : (Real.Gamma (1 / 24) * Real.Gamma (11 / 24)) ^ 2
        * (Real.sin (Real.pi * (1 / 24)) * Real.sin (Real.pi * (11 / 24))) * Real.pi ^ 2
      = 3 * (Real.Gamma (5 / 24) * Real.Gamma (7 / 24)) ^ 2
        * (Real.sin (Real.pi * (5 / 24)) * Real.sin (Real.pi * (7 / 24))) * Real.pi ^ 2 := by
    linear_combination
      (-((Real.Gamma (1 / 24) * Real.Gamma (11 / 24)) ^ 2
        * (Real.sin (Real.pi * (1 / 24)) * Real.sin (Real.pi * (11 / 24))))) * hBC
      + (3 * (Real.Gamma (5 / 24) * Real.Gamma (7 / 24)) ^ 2
        * (Real.sin (Real.pi * (5 / 24)) * Real.sin (Real.pi * (7 / 24)))) * hAD
      + (Real.sin (Real.pi * (1 / 24)) * Real.sin (Real.pi * (5 / 24))
        * Real.sin (Real.pi * (7 / 24)) * Real.sin (Real.pi * (11 / 24))
        * (Real.Gamma (1 / 24) * Real.Gamma (11 / 24) * Real.Gamma (5 / 24)
          * Real.Gamma (7 / 24))) * Gamma_twentyfourths_triple
  have step2 : (Real.Gamma (1 / 24) * Real.Gamma (11 / 24)) ^ 2
        * (Real.sin (Real.pi * (1 / 24)) * Real.sin (Real.pi * (11 / 24)))
      = 3 * (Real.Gamma (5 / 24) * Real.Gamma (7 / 24)) ^ 2
        * (Real.sin (Real.pi * (5 / 24)) * Real.sin (Real.pi * (7 / 24))) :=
    mul_right_cancel₀ (by positivity : (Real.pi : ℝ) ^ 2 ≠ 0) step
  -- the four sines collapse to `sin(π/12)` and `cos(π/12)`
  have c11 : Real.sin (Real.pi * (11 / 24)) = Real.cos (Real.pi * (1 / 24)) := by
    rw [show Real.pi * (11 / 24) = Real.pi / 2 - Real.pi * (1 / 24) by ring,
      Real.sin_pi_div_two_sub]
  have c7 : Real.sin (Real.pi * (7 / 24)) = Real.cos (Real.pi * (5 / 24)) := by
    rw [show Real.pi * (7 / 24) = Real.pi / 2 - Real.pi * (5 / 24) by ring,
      Real.sin_pi_div_two_sub]
  have d1 : Real.sin (Real.pi * (1 / 24)) * Real.cos (Real.pi * (1 / 24))
      = Real.sin (Real.pi / 12) / 2 := by
    have h := Real.sin_two_mul (Real.pi * (1 / 24))
    rw [show 2 * (Real.pi * (1 / 24)) = Real.pi / 12 by ring] at h
    linarith
  have d5 : Real.sin (Real.pi * (5 / 24)) * Real.cos (Real.pi * (5 / 24))
      = Real.cos (Real.pi / 12) / 2 := by
    have h := Real.sin_two_mul (Real.pi * (5 / 24))
    rw [show 2 * (Real.pi * (5 / 24)) = Real.pi / 2 - Real.pi / 12 by ring,
      Real.sin_pi_div_two_sub] at h
    linarith
  rw [c11, c7, d1, d5] at step2
  -- `sin(π/12) cos(π/12) = 1/4` and `sin²(π/12) = (2 - √3)/4`
  have half : Real.sin (Real.pi / 12) * Real.cos (Real.pi / 12) = 1 / 4 := by
    have h := Real.sin_two_mul (Real.pi / 12)
    rw [show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.sin_pi_div_six] at h
    linarith
  have hsq : Real.sin (Real.pi / 12) ^ 2 = (2 - Real.sqrt 3) / 4 := by
    have hc := Real.cos_sq (Real.pi / 12)
    rw [show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.cos_pi_div_six] at hc
    have hp := Real.sin_sq_add_cos_sq (Real.pi / 12)
    linarith
  -- multiplying by `4 sin(π/12)` turns the sines into the algebraic factor `2 - √3`
  have hmul : (Real.Gamma (1 / 24) * Real.Gamma (11 / 24)) ^ 2 * (2 - Real.sqrt 3)
      = 3 * (Real.Gamma (5 / 24) * Real.Gamma (7 / 24)) ^ 2 := by
    linear_combination (8 * Real.sin (Real.pi / 12)) * step2
      - 4 * (Real.Gamma (1 / 24) * Real.Gamma (11 / 24)) ^ 2 * hsq
      + 12 * (Real.Gamma (5 / 24) * Real.Gamma (7 / 24)) ^ 2 * half
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine eq_of_sq_eq_of_nonneg' (le_of_lt (mul_pos hA hD))
    (le_of_lt (mul_pos (by positivity) (mul_pos hB hC))) ?_
  linear_combination (2 + Real.sqrt 3) * hmul
    + (Real.Gamma (1 / 24) * Real.Gamma (11 / 24)) ^ 2 * h3
    - (Real.Gamma (5 / 24) * Real.Gamma (7 / 24)) ^ 2 * sq_three_sqrt_two_add_sqrt_six


/-! ### Reducing the whole of level `24` to `Γ(1/24)`

The ratio above is one relation among the four values; there are two more, and together they
leave exactly one unknown. Gauss duplication at `s = 1/24, 5/24, 1/8`, triplication at
`s = 1/24, 1/12`, and reflection at `11/24, 7/24, 3/8, 1/4` express each of `Γ(11/24)`,
`Γ(7/24)`, `Γ(5/24)` as `Γ(1/24)` times elementary factors, `Γ(1/12)` and `Γ(1/4)`. In the
product the `Γ(1/4)`s cancel against each other, and triplication at `1/12` — which reads
`Γ(1/12) Γ(5/12) = 2 √3 sin(π/4) Γ(1/4)²` — removes the last one, leaving `Γ(1/12)` alone.

All the powers of `2` that duplication throws off are twelfths and all the powers of `3`
from triplication are eighths, so both become integer powers of `tw = 2 ^ (1/12)` and
`th = 3 ^ (1/8)`; `ring` then does the exponent bookkeeping, with `tw ^ 12 = 2` and
`th ^ 8 = 3` supplied at the two points where a genuine reduction happens. -/

/-- `tw = 2 ^ (1/12)`, the common root of every power of `2` that duplication produces. -/
noncomputable def tw : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 12)

/-- `th = 3 ^ (1/8)`, likewise for triplication. -/
noncomputable def th : ℝ := (3 : ℝ) ^ ((1 : ℝ) / 8)

theorem tw_pos : 0 < tw := Real.rpow_pos_of_pos (by norm_num) _

theorem th_pos : 0 < th := Real.rpow_pos_of_pos (by norm_num) _

-- Theorem: `tw ^ 12 = 2`. One of the only two places an exponent genuinely collapses.
theorem tw_pow : tw ^ (12 : ℕ) = 2 := by
  rw [tw, ← Real.rpow_natCast _ 12, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

-- Theorem: `th ^ 8 = 3`, the other.
theorem th_pow : th ^ (8 : ℕ) = 3 := by
  rw [th, ← Real.rpow_natCast _ 8, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

-- Theorem: `th ^ 4 = √3`, the form in which `3 ^ (1/2)` appears at the end.
theorem th_four : th ^ (4 : ℕ) = Real.sqrt 3 := by
  refine eq_of_sq_eq_of_nonneg' (by positivity) (Real.sqrt_nonneg 3) ?_
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), ← pow_mul]
  exact th_pow

theorem two_rpow_eleven_twelfths : (2 : ℝ) ^ ((11 : ℝ) / 12) = tw ^ (11 : ℕ) := by
  rw [tw, ← Real.rpow_natCast _ 11, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem two_rpow_seven_twelfths : (2 : ℝ) ^ ((7 : ℝ) / 12) = tw ^ (7 : ℕ) := by
  rw [tw, ← Real.rpow_natCast _ 7, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem two_rpow_three_quarters : (2 : ℝ) ^ ((3 : ℝ) / 4) = tw ^ (9 : ℕ) := by
  rw [tw, ← Real.rpow_natCast _ 9, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem three_rpow_three_eighths : (3 : ℝ) ^ ((3 : ℝ) / 8) = th ^ (3 : ℕ) := by
  rw [th, ← Real.rpow_natCast _ 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem three_rpow_one_quarter : (3 : ℝ) ^ ((1 : ℝ) / 4) = th ^ (2 : ℕ) := by
  rw [th, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-! #### The three sines that survive -/

-- Theorem: `sin(π/4) = √2/2`.
theorem sin_pi_mul_one_quarter : Real.sin (Real.pi * (1 / 4)) = Real.sqrt 2 / 2 := by
  rw [show Real.pi * (1 / 4) = Real.pi / 4 by ring, Real.sin_pi_div_four]

-- Theorem: `sin²(3π/8) = (2 + √2)/4`, from the half-angle value of `cos(π/8)`.
theorem sin_pi_mul_three_eighths_sq :
    Real.sin (Real.pi * (3 / 8)) ^ 2 = (2 + Real.sqrt 2) / 4 := by
  rw [show Real.pi * (3 / 8) = Real.pi / 2 - Real.pi / 8 by ring, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_eight, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + Real.sqrt 2)]
  norm_num

-- Theorem: `sin(7π/24) sin(11π/24) = (√3 + √2)/4`. Product-to-sum turns the two
-- twenty-fourths into `cos(π/6)` and `cos(3π/4)`, both elementary.
theorem sin_seven_mul_sin_eleven :
    Real.sin (Real.pi * (7 / 24)) * Real.sin (Real.pi * (11 / 24))
      = (Real.sqrt 3 + Real.sqrt 2) / 4 := by
  have hsub := Real.cos_sub (Real.pi * (11 / 24)) (Real.pi * (7 / 24))
  have hadd := Real.cos_add (Real.pi * (11 / 24)) (Real.pi * (7 / 24))
  rw [show Real.pi * (11 / 24) - Real.pi * (7 / 24) = Real.pi / 6 by ring,
    Real.cos_pi_div_six] at hsub
  rw [show Real.pi * (11 / 24) + Real.pi * (7 / 24) = Real.pi - Real.pi / 4 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_four] at hadd
  linarith

theorem two_rpow_one_sixth : (2 : ℝ) ^ ((1 : ℝ) / 6) = tw ^ (2 : ℕ) := by
  rw [tw, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! #### The three solved forms -/

-- Theorem: `Γ(11/24)` against `Γ(1/24)`. Duplication at `s = 1/24` produces `Γ(1/12)` and
-- `Γ(13/24)`; reflection at `11/24` trades `Γ(13/24)` for `Γ(11/24)`.
theorem Gamma_eleven_twentyfourths_eq :
    Real.Gamma (11 / 24) * (Real.Gamma (1 / 12) * tw ^ (11 : ℕ)
        * Real.sin (Real.pi * (11 / 24)))
      = Real.Gamma (1 / 24) * Real.sqrt Real.pi := by
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have he : (0 : ℝ) < Real.Gamma (13 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have hD := Real.Gamma_mul_Gamma_add_half (1 / 24 : ℝ)
  norm_num at hD
  rw [two_rpow_eleven_twelfths] at hD
  have hR := Gamma_mul_Gamma_one_sub_mul_sin (x := (11 : ℝ) / 24) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 11 / 24 = 13 / 24 by norm_num] at hR
  refine mul_right_cancel₀ he.ne' ?_
  linear_combination (Real.Gamma (1 / 12) * tw ^ (11 : ℕ)) * hR - Real.sqrt Real.pi * hD
    - (Real.Gamma (1 / 12) * tw ^ (11 : ℕ)) * hsp

-- Theorem: `Γ(7/24)` against `Γ(1/24)`. Triplication at `s = 1/24` brings in `Γ(1/8)` and
-- `Γ(3/8)`, and duplication at `s = 1/8` converts their ratio into `Γ(1/4)`.
theorem Gamma_seven_twentyfourths_eq :
    Real.Gamma (7 / 24) * (tw ^ (21 : ℕ) * th ^ (3 : ℕ) * Real.Gamma (1 / 4)
        * Real.sin (Real.pi * (3 / 8)) * Real.sin (Real.pi * (7 / 24)))
      = Real.Gamma (1 / 24) * Real.sqrt Real.pi := by
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hq : (0 : ℝ) < Real.Gamma (3 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have hsq : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hD3 := Real.Gamma_mul_Gamma_add_half (1 / 8 : ℝ)
  norm_num at hD3
  rw [two_rpow_three_quarters] at hD3
  have hT1 := Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds (1 / 24 : ℝ)
  norm_num at hT1
  rw [three_rpow_three_eighths] at hT1
  have hR3 := Gamma_mul_Gamma_one_sub_mul_sin (x := (3 : ℝ) / 8) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 3 / 8 = 5 / 8 by norm_num] at hR3
  have hR2 := Gamma_mul_Gamma_one_sub_mul_sin (x := (7 : ℝ) / 24) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 7 / 24 = 17 / 24 by norm_num] at hR2
  have step3 : Real.Gamma (3 / 8) * (Real.Gamma (1 / 4) * tw ^ (9 : ℕ) * Real.sqrt Real.pi)
      * Real.sin (Real.pi * (3 / 8)) = Real.pi * Real.Gamma (1 / 8) := by
    linear_combination Real.Gamma (1 / 8) * hR3
      - (Real.Gamma (3 / 8) * Real.sin (Real.pi * (3 / 8))) * hD3
  have step4 : Real.Gamma (1 / 24) * Real.Gamma (3 / 8) * Real.pi
      = 2 * Real.pi * th ^ (3 : ℕ) * Real.Gamma (1 / 8) * Real.Gamma (7 / 24)
        * Real.sin (Real.pi * (7 / 24)) := by
    linear_combination (Real.Gamma (7 / 24) * Real.sin (Real.pi * (7 / 24))) * hT1
      - (Real.Gamma (1 / 24) * Real.Gamma (3 / 8)) * hR2
  refine mul_right_cancel₀ (ne_of_gt (mul_pos hq hsq)) ?_
  linear_combination
    (Real.Gamma (7 / 24) * tw ^ (9 : ℕ) * th ^ (3 : ℕ) * Real.Gamma (1 / 4)
      * Real.sin (Real.pi * (3 / 8)) * Real.sin (Real.pi * (7 / 24)) * Real.Gamma (3 / 8)
      * Real.sqrt Real.pi) * tw_pow
    + (2 * Real.Gamma (7 / 24) * th ^ (3 : ℕ) * Real.sin (Real.pi * (7 / 24))) * step3
    - step4 - (Real.Gamma (1 / 24) * Real.Gamma (3 / 8)) * hsp

-- Theorem: `Γ(5/24)` against `Γ(1/24)`. Duplication at `s = 5/24` relates it to `Γ(7/24)`
-- through `Γ(5/12)`, and triplication at `s = 1/12` — which reads
-- `Γ(1/12) Γ(5/12) = 2 √3 sin(π/4) Γ(1/4)²` — eliminates `Γ(5/12)`.
theorem Gamma_five_twentyfourths_eq :
    Real.Gamma (5 / 24) * (tw ^ (2 : ℕ) * th * Real.Gamma (1 / 12)
        * Real.sin (Real.pi * (3 / 8)))
      = Real.Gamma (1 / 24) * Real.sin (Real.pi * (1 / 4)) * Real.Gamma (1 / 4) := by
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hf : (0 : ℝ) < Real.Gamma (17 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have ht : (0 : ℝ) < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hr : (0 : ℝ) < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hD2 := Real.Gamma_mul_Gamma_add_half (5 / 24 : ℝ)
  norm_num at hD2
  rw [two_rpow_seven_twelfths] at hD2
  have hR2 := Gamma_mul_Gamma_one_sub_mul_sin (x := (7 : ℝ) / 24) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 7 / 24 = 17 / 24 by norm_num] at hR2
  have hT2 := Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds (1 / 12 : ℝ)
  norm_num at hT2
  rw [three_rpow_one_quarter] at hT2
  have hR4 := Gamma_mul_Gamma_one_sub_mul_sin (x := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at hR4
  have stepA : Real.Gamma (5 / 24) * Real.pi
      = Real.Gamma (7 / 24) * Real.Gamma (5 / 12) * tw ^ (7 : ℕ) * Real.sqrt Real.pi
        * Real.sin (Real.pi * (7 / 24)) := by
    refine mul_right_cancel₀ hf.ne' ?_
    linear_combination Real.pi * hD2
      - (Real.Gamma (5 / 12) * tw ^ (7 : ℕ) * Real.sqrt Real.pi) * hR2
  have stepB : Real.Gamma (1 / 12) * Real.Gamma (5 / 12)
      = 2 * th ^ (2 : ℕ) * Real.Gamma (1 / 4) ^ 2 * Real.sin (Real.pi * (1 / 4)) := by
    refine mul_right_cancel₀ ht.ne' ?_
    linear_combination hT2 - (2 * th ^ (2 : ℕ) * Real.Gamma (1 / 4)) * hR4
  have h7 := Gamma_seven_twentyfourths_eq
  refine mul_right_cancel₀
    (ne_of_gt (mul_pos Real.pi_pos
      (mul_pos (mul_pos (pow_pos tw_pos 21) (pow_pos th_pos 3)) hr))) ?_
  linear_combination
    (tw ^ (23 : ℕ) * th ^ (4 : ℕ) * Real.Gamma (1 / 12) * Real.sin (Real.pi * (3 / 8))
      * Real.Gamma (1 / 4)) * stepA
    + (Real.Gamma (7 / 24) * tw ^ (30 : ℕ) * th ^ (4 : ℕ) * Real.sin (Real.pi * (3 / 8))
      * Real.Gamma (1 / 4) * Real.sqrt Real.pi * Real.sin (Real.pi * (7 / 24))) * stepB
    + (2 * tw ^ (9 : ℕ) * th ^ (3 : ℕ) * Real.Gamma (1 / 4) ^ 2 * Real.sin (Real.pi * (1 / 4))
      * Real.sqrt Real.pi) * h7
    + (2 * Real.Gamma (1 / 24) * tw ^ (9 : ℕ) * th ^ (3 : ℕ) * Real.Gamma (1 / 4) ^ 2
      * Real.sin (Real.pi * (1 / 4))) * hsp
    - (Real.Gamma (1 / 24) * Real.sin (Real.pi * (1 / 4)) * Real.Gamma (1 / 4) ^ 2 * Real.pi
      * tw ^ (9 : ℕ) * th ^ (3 : ℕ)) * tw_pow

/-! #### Everything at level `24` in terms of `Γ(1/24)` -/

-- Theorem: the algebraic identity the three solved forms multiply out to.
theorem reduce_aux :
    tw ^ (36 : ℕ) * (Real.sqrt 2 - 1) * (Real.sqrt 3 - Real.sqrt 2)
        * (Real.sqrt 3 + Real.sqrt 2) * (2 + Real.sqrt 2)
      = 8 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have htw : tw ^ (36 : ℕ) = 8 := by
    rw [show (36 : ℕ) = 12 * 3 from rfl, pow_mul, tw_pow]; norm_num
  rw [htw]
  linear_combination (8 * (Real.sqrt 2 - 1) * (2 + Real.sqrt 2)) * h3
    + (8 - 8 * (Real.sqrt 2 - 1) * (2 + Real.sqrt 2)) * h2

-- Theorem: `th ^ 4 √3 = 3`; the one place the `3` from triplication meets the `√3` in the
-- final constant.
theorem th_four_mul_sqrt_three : th ^ (4 : ℕ) * Real.sqrt 3 = 3 := by
  rw [th_four]; exact Real.mul_self_sqrt (by norm_num)

-- Theorem: **level `24` collapses onto `Γ(1/24)`.** Together with denominators `8` and
-- `12`, which the project already has unconditionally, this says exactly one number is
-- missing at level `24` — the one the sixth singular value supplies.
theorem Gamma_twentyfourths_reduce :
    Real.Gamma (5 / 24) * Real.Gamma (7 / 24) * Real.Gamma (11 / 24) * Real.Gamma (1 / 12) ^ 2
      = (2 : ℝ) ^ ((1 : ℝ) / 6) * Real.pi * Real.sqrt 3 * (Real.sqrt 2 - 1)
          * (Real.sqrt 3 - Real.sqrt 2) / 3 * Real.Gamma (1 / 24) ^ 3 := by
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hr : (0 : ℝ) < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have h11 := Gamma_eleven_twentyfourths_eq
  have h7 := Gamma_seven_twentyfourths_eq
  have h5 := Gamma_five_twentyfourths_eq
  have stage1 : Real.Gamma (5 / 24) * Real.Gamma (7 / 24) * Real.Gamma (11 / 24)
        * Real.Gamma (1 / 12) ^ 2
        * (tw ^ (34 : ℕ) * th ^ (4 : ℕ)
          * (Real.sin (Real.pi * (7 / 24)) * Real.sin (Real.pi * (11 / 24)))
          * Real.sin (Real.pi * (3 / 8)) ^ 2)
      = Real.Gamma (1 / 24) ^ 3 * Real.pi * Real.sin (Real.pi * (1 / 4)) := by
    refine mul_right_cancel₀ hr.ne' ?_
    linear_combination
      ((Real.Gamma (7 / 24) * (tw ^ (21 : ℕ) * th ^ (3 : ℕ) * Real.Gamma (1 / 4)
          * Real.sin (Real.pi * (3 / 8)) * Real.sin (Real.pi * (7 / 24))))
        * (Real.Gamma (5 / 24) * (tw ^ (2 : ℕ) * th * Real.Gamma (1 / 12)
          * Real.sin (Real.pi * (3 / 8))))) * h11
      + ((Real.Gamma (1 / 24) * Real.sqrt Real.pi)
        * (Real.Gamma (5 / 24) * (tw ^ (2 : ℕ) * th * Real.Gamma (1 / 12)
          * Real.sin (Real.pi * (3 / 8))))) * h7
      + ((Real.Gamma (1 / 24) * Real.sqrt Real.pi) * (Real.Gamma (1 / 24) * Real.sqrt Real.pi))
        * h5
      + (Real.Gamma (1 / 24) ^ 3 * Real.sin (Real.pi * (1 / 4)) * Real.Gamma (1 / 4)) * hsp
  rw [sin_seven_mul_sin_eleven, sin_pi_mul_three_eighths_sq, sin_pi_mul_one_quarter] at stage1
  rw [two_rpow_one_sixth]
  refine mul_right_cancel₀
    (ne_of_gt (mul_pos (mul_pos (mul_pos (pow_pos tw_pos 34) (pow_pos th_pos 4))
      (by positivity : (0 : ℝ) < Real.sqrt 3 + Real.sqrt 2))
      (by positivity : (0 : ℝ) < 2 + Real.sqrt 2))) ?_
  linear_combination 16 * stage1
    - (Real.Gamma (1 / 24) ^ 3 * Real.pi * th ^ (4 : ℕ) * Real.sqrt 3 / 3) * reduce_aux
    - (8 * Real.Gamma (1 / 24) ^ 3 * Real.pi * Real.sqrt 2 / 3) * th_four_mul_sqrt_three
/-! ### The sixth singular value

What is left is one number. See the file header for why no functional equation can supply
it, and `Gamma_twentyfourths_reduce` for the precise sense in which it is the only one. -/

-- Theorem: `√3 < 2`, the first of the two comparisons behind `0 < k₆`.
theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]

-- Theorem: `√2 < √3`, the second.
theorem sqrt_two_lt_sqrt_three : Real.sqrt 2 < Real.sqrt 3 :=
  Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

-- Theorem: `k₆` is positive; both of its factors are.
theorem sixthSingularMod_pos : 0 < sixthSingularMod :=
  mul_pos (by linarith [sqrt_three_lt_two]) (by linarith [sqrt_two_lt_sqrt_three])

/-- **Assumed.** The sixth singular value, in the form Borwein-Zucker give it:

`K(k₆) = 2 ^ (1/12) 3 ^ (1/4) (√2 - 1)(√3 + 1) / 48 · Γ(1/24)² / Γ(1/12)`,

cleared of its denominator. Equivalently `K(k₆) = c · Β(1/24, 1/24)` for an algebraic `c`,
which is how Zucker tabulates it. This is Chowla-Selberg at discriminant `-24`, and it is
the one statement in the file taken on trust; its classical proof runs through complex
multiplication and the Kronecker limit formula, neither of which Mathlib has.

It is stated here rather than in the symmetric four-`Γ` form of `ellipticF_sixthSingular`
because `Gamma_twentyfourths_reduce` shows the two are equivalent, and this one names the
single number that is actually missing: `Γ(1/24)`. Denominator `12` is already
unconditional in `Pptc.Gamma`. -/
theorem ellipticF_sixthSingular_beta :
    ellipticF (sixthSingularMod ^ 2) (Real.pi / 2) * (48 * Real.Gamma (1 / 12))
      = (2 : ℝ) ^ ((1 : ℝ) / 12) * (3 : ℝ) ^ ((1 : ℝ) / 4) * (Real.sqrt 2 - 1)
          * (Real.sqrt 3 + 1) * Real.Gamma (1 / 24) ^ 2 := by
  sorry

-- Theorem: the elementary constant relating the two forms. Both `(√2 - 1)(√2 + 1) = 1` and
-- `(√3 + 1)²(2 - √3) = 2` are needed, and they are exactly what makes `384` become `768`.
theorem sixthSingular_constant :
    ((2 : ℝ) ^ ((1 : ℝ) / 12) * (3 : ℝ) ^ ((1 : ℝ) / 4) * (Real.sqrt 2 - 1)
          * (Real.sqrt 3 + 1)) ^ 2 * (384 * Real.pi * (Real.sqrt 2 + 1) * sixthSingularMod)
      = 2304 * ((2 : ℝ) ^ ((1 : ℝ) / 6) * Real.pi * Real.sqrt 3 * (Real.sqrt 2 - 1)
          * (Real.sqrt 3 - Real.sqrt 2) / 3) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hA : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 3 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_eq_rpow]
    norm_num
  have hB : ((2 : ℝ) ^ ((1 : ℝ) / 12)) ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have e1 : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1 := by linear_combination h2
  have e2 : (Real.sqrt 3 + 1) ^ 2 * (2 - Real.sqrt 3) = 2 := by
    linear_combination (-Real.sqrt 3) * h3
  simp only [sixthSingularMod]
  linear_combination
    (768 * Real.pi * Real.sqrt 3 * (Real.sqrt 2 - 1) * (Real.sqrt 3 - Real.sqrt 2)) * hB
    + (((2 : ℝ) ^ ((1 : ℝ) / 12)) ^ 2 * (Real.sqrt 2 - 1) ^ 2 * (Real.sqrt 3 + 1) ^ 2 * 384
        * Real.pi * (Real.sqrt 2 + 1) * (2 - Real.sqrt 3) * (Real.sqrt 3 - Real.sqrt 2)) * hA
    + (384 * ((2 : ℝ) ^ ((1 : ℝ) / 12)) ^ 2 * Real.pi * Real.sqrt 3 * (Real.sqrt 2 - 1)
        * (Real.sqrt 3 - Real.sqrt 2) * (Real.sqrt 3 + 1) ^ 2 * (2 - Real.sqrt 3)) * e1
    + (384 * ((2 : ℝ) ^ ((1 : ℝ) / 12)) ^ 2 * Real.pi * Real.sqrt 3 * (Real.sqrt 2 - 1)
        * (Real.sqrt 3 - Real.sqrt 2)) * e2

-- Theorem: the sixth singular value in its symmetric four-`Γ` form, as
-- `Pptc.Gamma` wants it. This is the published Borwein-Zucker statement; the passage from
-- the single-`Γ` form above is `Gamma_twentyfourths_reduce` together with the elementary
-- constant, and nothing else.
theorem ellipticF_sixthSingular :
    ellipticF (sixthSingularMod ^ 2) (Real.pi / 2) ^ 2
      = Real.Gamma (1 / 24) * Real.Gamma (5 / 24) * Real.Gamma (7 / 24) * Real.Gamma (11 / 24)
          / (384 * Real.pi * (Real.sqrt 2 + 1) * sixthSingularMod) := by
  have hk := sixthSingularMod_pos
  have hpi := Real.pi_pos
  have hs2 := Real.sqrt_nonneg 2
  have hg : (0 : ℝ) < Real.Gamma (1 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have hbeta := ellipticF_sixthSingular_beta
  have hred := Gamma_twentyfourths_reduce
  have hcon := sixthSingular_constant
  rw [eq_div_iff (by positivity)]
  refine mul_right_cancel₀ (show (2304 : ℝ) * Real.Gamma (1 / 12) ^ 2 ≠ 0 by positivity) ?_
  linear_combination
    ((ellipticF (sixthSingularMod ^ 2) (Real.pi / 2) * (48 * Real.Gamma (1 / 12))
        + (2 : ℝ) ^ ((1 : ℝ) / 12) * (3 : ℝ) ^ ((1 : ℝ) / 4) * (Real.sqrt 2 - 1)
          * (Real.sqrt 3 + 1) * Real.Gamma (1 / 24) ^ 2)
      * (384 * Real.pi * (Real.sqrt 2 + 1) * sixthSingularMod)) * hbeta
    + (Real.Gamma (1 / 24) ^ 4) * hcon
    - (2304 * Real.Gamma (1 / 24)) * hred

end Pconstructible
