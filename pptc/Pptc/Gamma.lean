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
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Pptc.Gamma

Which values of Euler's `Γ` are P-constructible.

The question only has content at *rational* arguments, and there it splits cleanly in two.

**The functional equations, which are formalized here in full.** Three identities relate
the values of `Γ` at rational points, and all three land inside `PConstructible` because
their right-hand sides are built out of numbers already known to be reachable — rationals,
`π`, `sin`, `√`, and `2 ^ x`:

* the recurrence `Γ(x + 1) = x Γ(x)`, whose right-hand side is a product;
* Euler's reflection `Γ(x) Γ(1 - x) = π / sin (π x)`, whose right-hand side is
  P-constructible outright (`pi_Pconstructible`, `sin_Pconstructible`);
* Legendre's duplication `Γ(x) Γ(x + 1/2) = Γ(2x) · 2 ^ (1 - 2x) √π`, whose elementary
  factor `dupFactor` is P-constructible by `rpow_two_Pconstructible`.

Each of these turns knowledge of some values of `Γ` into knowledge of others, and — this is
the point — *never* loses anything, because `PConstructible` is closed under `+ - * /` and
the divisions involved are by nonzero quantities. The transfer lemmas below
(`Gamma_add_intCast_Pconstructible`, `Gamma_one_sub_Pconstructible`, and the three
duplication lemmas) are stated with no side conditions at all: the degenerate cases, where
the dividing quantity is a pole value `Γ(-m) = 0`, are exactly the cases where the target is
a half-integer or a positive integer and so is P-constructible for an unrelated reason.

Because `Γ(x)` and `Γ(x + n)` stand or fall together for every integer `n`, only the
residue of the argument modulo `1` matters. `Gamma_intCast_div_Pconstructible` packages
that: to reach every rational with denominator dividing `d` it is enough to reach the `d`
values `Γ(0/d), …, Γ((d-1)/d)`.

**The transcendental input, which is not.** The functional equations alone pin down `Γ` at
half-integers and nothing more, since `Γ(1/2) = √π` is itself elementary. That case is
`Gamma_intCast_div_two_Pconstructible`, the one *unconditional* infinite family here.
Every finer denominator needs one genuinely new number from outside the functional
equations, and the natural source is the elliptic integrals, which `Pptc.Basic` has already
shown to be P-constructible in all three kinds. The relevant classical identities are

    Γ(1/4) ^ 2 = 4 √π · K(1/√2)                              (the lemniscatic case)
    Γ(1/3) ^ 3 = 2 ^ (7/3) π · K(k₃) / 3 ^ (1/4),   k₃ = sin (π / 12)

and a companion at the second singular value `k₂ = √2 - 1` giving `Γ(1/8) Γ(3/8)`. Since
`ellipticF_sq_Pconstructible` already provides `K(k)` for every P-constructible `k`, each of
these identities would discharge the corresponding hypothesis below outright. Proving them
in Lean means pushing a singular change of variables through Mathlib's Beta integral, which
is left for later; until then the families for denominators `3`, `4`, `6` and `8` are stated
as implications, with the needed value as a named hypothesis.

What the implications buy is considerable, and more than the bare inputs suggest:

* `Γ(1/3)` alone gives every rational with denominator `3` *and* every one with
  denominator `6`, since duplication at `s = 1/6` reads `Γ(1/6)` off `Γ(1/3)` and `Γ(2/3)`.
* `Γ(1/4)` and `Γ(1/8)` together give every rational with denominator `8`; in particular
  `Γ(3/8)` is *derived*, not assumed, by duplication at `s = 3/8`.
* Conversely `Γ(1/8)` and `Γ(3/8)` give `Γ(1/4)`, so the pairs `{1/4, 1/8}` and `{1/8, 3/8}`
  carry exactly the same information.

Doubling the denominator again does need a new input each time: from denominator `8` the
duplication formula only ever delivers the *ratio* `Γ(1/16) / Γ(7/16)`, never either factor,
which is the P-constructible shadow of the fact that each new singular value of `K` is a new
transcendental. The one denominator that ought to come for free but does not is `12`:
Gauss's triplication formula would give `Γ(1/12)` from `Γ(1/4)` and `Γ(1/3)`, but Mathlib
proves only the `k = 2` case of the multiplication theorem.
-/

namespace Pconstructible

/-! ### Elementary numbers used below

Three small values that the Gamma identities keep needing. `ratval_Pconstructible` is the
workhorse: the arguments of `Γ` below are written as numerals such as `3 / 8`, and this
lets `norm_num` match them against `rat_Pconstructible`. -/

-- Theorem: an explicit rational numeral is P-constructible.
theorem ratval_Pconstructible {x : ℝ} (q : ℚ) (h : (q : ℝ) = x) : PConstructible x :=
  h ▸ rat_Pconstructible q

-- Theorem: 1/2 is P-constructible.
theorem half_Pconstructible : PConstructible ((1 : ℝ) / 2) :=
  PConstructible.div PConstructible.base_one two_Pconstructible

-- Theorem: √π is P-constructible. This is the value `Γ(1/2)`, and it is also the
-- elementary factor that duplication contributes.
theorem sqrt_pi_Pconstructible : PConstructible (Real.sqrt Real.pi) :=
  sqrt_Pconstructible pi_Pconstructible

/-! ### `Γ` at the integers and at `1/2`

The two starting points. Mathlib assigns `Γ` the value `0` at every pole, so the integers
give a *complete* answer rather than one restricted to `n ≥ 1`: `Γ(n)` is `(n-1)!` for
positive `n` and `0` otherwise, and both are rational. -/

-- Theorem: `Γ(n)` is P-constructible for every natural `n`.
theorem Gamma_natCast_Pconstructible (n : ℕ) : PConstructible (Real.Gamma n) := by
  cases n with
  | zero => simpa using zero_Pconstructible
  | succ m =>
    rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
    exact nat_Pconstructible _

-- Theorem: `Γ(z)` is P-constructible for every integer `z`, the poles included.
theorem Gamma_intCast_Pconstructible (z : ℤ) : PConstructible (Real.Gamma z) := by
  rcases le_total 0 z with hz | hz
  · lift z to ℕ using hz with n
    simpa using Gamma_natCast_Pconstructible n
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, z = -(m : ℤ) := ⟨(-z).toNat, by omega⟩
    rw [show ((-(m : ℤ) : ℤ) : ℝ) = -(m : ℝ) by push_cast; ring, Real.Gamma_neg_nat_eq_zero]
    exact zero_Pconstructible

-- Theorem: `Γ(1/2) = √π` is P-constructible.
theorem Gamma_one_half_Pconstructible : PConstructible (Real.Gamma (1 / 2)) := by
  rw [Real.Gamma_one_half_eq]
  exact sqrt_pi_Pconstructible

/-! ### The recurrence `Γ(x + 1) = x Γ(x)`

Shifting the argument by an integer costs a multiplication one way and a division the
other, so it never leaves the class. Neither direction needs a side condition. Going up,
the recurrence itself is unconditional once `x ≠ 0`, and at `x = 0` the target is
`Γ(1) = 1`. Going down, the division is by `x - 1`, and at `x = 1` the target is the pole
value `Γ(0) = 0`. -/

-- Theorem: `Γ(x + 1)` is P-constructible whenever `x` and `Γ(x)` are.
theorem Gamma_add_one_Pconstructible {x : ℝ} (hx : PConstructible x)
    (h : PConstructible (Real.Gamma x)) : PConstructible (Real.Gamma (x + 1)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using PConstructible.base_one
  · rw [Real.Gamma_add_one hx0]
    exact PConstructible.mul hx h

-- Theorem: `Γ(x - 1)` is P-constructible whenever `x` and `Γ(x)` are.
theorem Gamma_sub_one_Pconstructible {x : ℝ} (hx : PConstructible x)
    (h : PConstructible (Real.Gamma x)) : PConstructible (Real.Gamma (x - 1)) := by
  rcases eq_or_ne x 1 with rfl | hx1
  · simpa using zero_Pconstructible
  · have hne : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hg := Real.Gamma_add_one hne
    rw [show x - 1 + 1 = x by ring] at hg
    rw [show Real.Gamma (x - 1) = Real.Gamma x / (x - 1) by rw [hg]; field_simp]
    exact PConstructible.div h (PConstructible.sub hx PConstructible.base_one)

-- Theorem: only the argument's residue modulo `1` matters — `Γ(x + n)` is P-constructible
-- for every integer `n` as soon as `x` and `Γ(x)` are.
theorem Gamma_add_intCast_Pconstructible {x : ℝ} (hx : PConstructible x)
    (h : PConstructible (Real.Gamma x)) (n : ℤ) : PConstructible (Real.Gamma (x + n)) := by
  refine Int.induction_on n ?_ (fun k ih => ?_) (fun k ih => ?_)
  · simpa using h
  · rw [show x + (((k : ℤ) + 1 : ℤ) : ℝ) = x + ((k : ℤ) : ℝ) + 1 by push_cast; ring]
    exact Gamma_add_one_Pconstructible (PConstructible.add hx (int_Pconstructible _)) ih
  · rw [show x + ((-(k : ℤ) - 1 : ℤ) : ℝ) = x + ((-(k : ℤ) : ℤ) : ℝ) - 1 by push_cast; ring]
    exact Gamma_sub_one_Pconstructible (PConstructible.add hx (int_Pconstructible _)) ih

/-! ### Euler's reflection formula

`Γ(x) Γ(1 - x) = π / sin (π x)` has a P-constructible right-hand side for every
P-constructible `x`, with no hypotheses whatever: `π` is P-constructible and so is the sine
of anything P-constructible. So the product of the two values is always reachable, and
knowing either factor gives the other by a division.

The division needs `Γ(x) ≠ 0`, which fails exactly when `x = -m` is a pole. But then
`1 - x = m + 1` is a positive integer, so the target is a factorial and the conclusion
holds anyway. The transfer is therefore unconditional. -/

-- Theorem: `Γ(x) Γ(1 - x)` is P-constructible for every P-constructible `x`, whether or
-- not either factor is.
theorem Gamma_mul_Gamma_one_sub_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.Gamma x * Real.Gamma (1 - x)) := by
  rw [Real.Gamma_mul_Gamma_one_sub]
  exact PConstructible.div pi_Pconstructible
    (sin_Pconstructible (PConstructible.mul pi_Pconstructible hx))

-- Theorem: `Γ(1 - x)` is P-constructible whenever `x` and `Γ(x)` are.
theorem Gamma_one_sub_Pconstructible {x : ℝ} (hx : PConstructible x)
    (h : PConstructible (Real.Gamma x)) : PConstructible (Real.Gamma (1 - x)) := by
  rcases eq_or_ne (Real.Gamma x) 0 with h0 | h0
  · obtain ⟨m, rfl⟩ := (Real.Gamma_eq_zero_iff x).1 h0
    rw [show (1 : ℝ) - -(m : ℝ) = ((m + 1 : ℕ) : ℝ) by push_cast; ring]
    exact Gamma_natCast_Pconstructible _
  · rw [show Real.Gamma (1 - x) = Real.Gamma x * Real.Gamma (1 - x) / Real.Gamma x by
      field_simp]
    exact PConstructible.div (Gamma_mul_Gamma_one_sub_Pconstructible hx) h

/-! ### Legendre's duplication formula

`Γ(s) Γ(s + 1/2) = Γ(2s) · 2 ^ (1 - 2s) √π` ties together three values, and the elementary
factor `dupFactor s = 2 ^ (1 - 2s) √π` is both P-constructible and never zero. So knowing
any two of `Γ(s)`, `Γ(s + 1/2)`, `Γ(2s)` gives the third.

As with reflection, the two divisions can only fail at a pole, and at a pole the target has
a half-integer argument, which `Gamma_add_intCast_Pconstructible` already covers. All three
directions are therefore unconditional. -/

/-- The elementary factor in Legendre's duplication formula, `2 ^ (1 - 2 s) √π`. -/
noncomputable def dupFactor (s : ℝ) : ℝ := (2 : ℝ) ^ (1 - 2 * s) * Real.sqrt Real.pi

-- Theorem: it is P-constructible, since `2 ^ x` is.
theorem dupFactor_Pconstructible {s : ℝ} (hs : PConstructible s) :
    PConstructible (dupFactor s) :=
  PConstructible.mul
    (rpow_two_Pconstructible
      (PConstructible.sub PConstructible.base_one (PConstructible.mul two_Pconstructible hs)))
    sqrt_pi_Pconstructible

-- Theorem: it never vanishes, so dividing by it is safe.
theorem dupFactor_ne_zero (s : ℝ) : dupFactor s ≠ 0 := by
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (1 - 2 * s) := Real.rpow_pos_of_pos two_pos _
  have h2 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  unfold dupFactor
  positivity

-- Theorem: duplication, restated with the elementary factor named.
theorem Gamma_mul_Gamma_add_half' (s : ℝ) :
    Real.Gamma s * Real.Gamma (s + 1 / 2) = Real.Gamma (2 * s) * dupFactor s := by
  rw [dupFactor, ← mul_assoc]
  exact Real.Gamma_mul_Gamma_add_half s

-- Theorem: `Γ(2s)` from `Γ(s)` and `Γ(s + 1/2)`.
theorem Gamma_two_mul_Pconstructible {s : ℝ} (hs : PConstructible s)
    (h₁ : PConstructible (Real.Gamma s)) (h₂ : PConstructible (Real.Gamma (s + 1 / 2))) :
    PConstructible (Real.Gamma (2 * s)) := by
  rw [show Real.Gamma (2 * s) = Real.Gamma s * Real.Gamma (s + 1 / 2) / dupFactor s by
    rw [Gamma_mul_Gamma_add_half', mul_div_assoc, div_self (dupFactor_ne_zero s), mul_one]]
  exact PConstructible.div (PConstructible.mul h₁ h₂) (dupFactor_Pconstructible hs)

-- Theorem: `Γ(s + 1/2)` from `Γ(s)` and `Γ(2s)`.
theorem Gamma_add_half_Pconstructible {s : ℝ} (hs : PConstructible s)
    (h₁ : PConstructible (Real.Gamma s)) (h₂ : PConstructible (Real.Gamma (2 * s))) :
    PConstructible (Real.Gamma (s + 1 / 2)) := by
  rcases eq_or_ne (Real.Gamma s) 0 with h0 | h0
  · obtain ⟨m, rfl⟩ := (Real.Gamma_eq_zero_iff s).1 h0
    rw [show -(m : ℝ) + 1 / 2 = (1 : ℝ) / 2 + ((-(m : ℤ) : ℤ) : ℝ) by push_cast; ring]
    exact Gamma_add_intCast_Pconstructible half_Pconstructible Gamma_one_half_Pconstructible _
  · rw [show Real.Gamma (s + 1 / 2) = Real.Gamma (2 * s) * dupFactor s / Real.Gamma s by
      rw [eq_div_iff h0, mul_comm]; exact Gamma_mul_Gamma_add_half' s]
    exact PConstructible.div (PConstructible.mul h₂ (dupFactor_Pconstructible hs)) h₁

-- Theorem: `Γ(s)` from `Γ(s + 1/2)` and `Γ(2s)`.
theorem Gamma_of_add_half_Pconstructible {s : ℝ} (hs : PConstructible s)
    (h₁ : PConstructible (Real.Gamma (s + 1 / 2)))
    (h₂ : PConstructible (Real.Gamma (2 * s))) : PConstructible (Real.Gamma s) := by
  rcases eq_or_ne (Real.Gamma (s + 1 / 2)) 0 with h0 | h0
  · obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff (s + 1 / 2)).1 h0
    rw [show s = (1 : ℝ) / 2 + ((-(m : ℤ) - 1 : ℤ) : ℝ) by push_cast; linarith]
    exact Gamma_add_intCast_Pconstructible half_Pconstructible Gamma_one_half_Pconstructible _
  · rw [show Real.Gamma s = Real.Gamma (2 * s) * dupFactor s / Real.Gamma (s + 1 / 2) by
      rw [eq_div_iff h0]; exact Gamma_mul_Gamma_add_half' s]
    exact PConstructible.div (PConstructible.mul h₂ (dupFactor_Pconstructible hs)) h₁

/-! ### From residues to a whole denominator

`Gamma_add_intCast_Pconstructible` says the argument only matters modulo `1`. Every
rational with denominator dividing `d` is `r / d + q` for an integer `q` and a residue
`r < d`, so the `d` values `Γ(0/d), …, Γ((d-1)/d)` settle the whole family at one stroke.
Each family below is proved by supplying those `d` values and nothing else. -/

-- Theorem: `Γ` is P-constructible at every rational with denominator dividing `d`, as soon
-- as it is at the `d` residues `r / d`.
theorem Gamma_intCast_div_Pconstructible {d : ℕ} (hd : 0 < d)
    (hbase : ∀ r : ℕ, r < d → PConstructible (Real.Gamma ((r : ℝ) / (d : ℝ)))) (n : ℤ) :
    PConstructible (Real.Gamma ((n : ℝ) / (d : ℝ))) := by
  have hd0 : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd.ne'
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have h1 : 0 ≤ n % (d : ℤ) := Int.emod_nonneg n hd0
  have h2 : n % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos n (by exact_mod_cast hd)
  obtain ⟨r, hrlt, q, hq⟩ : ∃ r : ℕ, r < d ∧ ∃ q : ℤ, n = (d : ℤ) * q + (r : ℤ) := by
    refine ⟨(n % (d : ℤ)).toNat, by omega, n / (d : ℤ), ?_⟩
    rw [Int.toNat_of_nonneg h1]
    exact (Int.mul_ediv_add_emod n d).symm
  rw [show (n : ℝ) / (d : ℝ) = (r : ℝ) / (d : ℝ) + ((q : ℤ) : ℝ) by
    rw [hq]; push_cast; field_simp; ring]
  exact Gamma_add_intCast_Pconstructible
    (PConstructible.div (nat_Pconstructible r) (nat_Pconstructible d)) (hbase r hrlt) q

/-! ### The half-integers: the unconditional family

`Γ(1/2) = √π` is already elementary, so the functional equations settle every argument in
`(1/2) ℤ` with no transcendental input at all. This is the one family below that is a
theorem rather than an implication — and, since duplication only ever relates a denominator
to its double, it is exactly as far as the functional equations reach on their own. -/

-- Theorem: `Γ(n/2)` is P-constructible for every integer `n`.
theorem Gamma_intCast_div_two_Pconstructible (n : ℤ) :
    PConstructible (Real.Gamma ((n : ℝ) / 2)) := by
  rw [show ((n : ℝ)) / 2 = (n : ℝ) / ((2 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = 0 by norm_num, Real.Gamma_zero]
    exact zero_Pconstructible
  · rw [show ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 by norm_num]
    exact Gamma_one_half_Pconstructible

/-! ### Denominator `3`, and with it denominator `6`

One new value, `Γ(1/3)`, buys two whole families. Reflection turns it into `Γ(2/3)`, and
then duplication at `s = 1/6` — where `Γ(s + 1/2) = Γ(2/3)` and `Γ(2s) = Γ(1/3)` are both
in hand — reads off `Γ(1/6)`. Reflection again gives `Γ(5/6)`, and the residues `2/6`,
`3/6`, `4/6` are values already known. -/

-- Theorem: `Γ(2/3)` is P-constructible as soon as `Γ(1/3)` is, by reflection.
theorem Gamma_two_thirds_Pconstructible (h : PConstructible (Real.Gamma (1 / 3))) :
    PConstructible (Real.Gamma (2 / 3)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 3) (by norm_num)) h
  rwa [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at this

-- Theorem: `Γ(1/6)` is P-constructible as soon as `Γ(1/3)` is, by duplication at `s = 1/6`.
theorem Gamma_one_sixth_Pconstructible (h : PConstructible (Real.Gamma (1 / 3))) :
    PConstructible (Real.Gamma (1 / 6)) := by
  refine Gamma_of_add_half_Pconstructible (ratval_Pconstructible (1 / 6) (by norm_num)) ?_ ?_
  · rw [show (1 : ℝ) / 6 + 1 / 2 = 2 / 3 by norm_num]
    exact Gamma_two_thirds_Pconstructible h
  · rw [show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num]
    exact h

-- Theorem: `Γ(n/3)` is P-constructible for every integer `n`, given `Γ(1/3)`.
theorem Gamma_intCast_div_three_Pconstructible (h : PConstructible (Real.Gamma (1 / 3)))
    (n : ℤ) : PConstructible (Real.Gamma ((n : ℝ) / 3)) := by
  rw [show ((n : ℝ)) / 3 = (n : ℝ) / ((3 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = 0 by norm_num, Real.Gamma_zero]
    exact zero_Pconstructible
  · rw [show ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = 1 / 3 by norm_num]
    exact h
  · rw [show ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = 2 / 3 by norm_num]
    exact Gamma_two_thirds_Pconstructible h

-- Theorem: `Γ(n/6)` is P-constructible for every integer `n`, given `Γ(1/3)`. No separate
-- assumption about `Γ(1/6)` is needed; duplication supplies it.
theorem Gamma_intCast_div_six_Pconstructible (h : PConstructible (Real.Gamma (1 / 3)))
    (n : ℤ) : PConstructible (Real.Gamma ((n : ℝ) / 6)) := by
  have h16 : PConstructible (Real.Gamma (1 / 6)) := Gamma_one_sixth_Pconstructible h
  have h56 : PConstructible (Real.Gamma (5 / 6)) := by
    have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 6) (by norm_num)) h16
    rwa [show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num] at this
  rw [show ((n : ℝ)) / 6 = (n : ℝ) / ((6 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 0 by norm_num, Real.Gamma_zero]
    exact zero_Pconstructible
  · rw [show ((1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 1 / 6 by norm_num]
    exact h16
  · rw [show ((2 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 1 / 3 by norm_num]
    exact h
  · rw [show ((3 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 1 / 2 by norm_num]
    exact Gamma_one_half_Pconstructible
  · rw [show ((4 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 2 / 3 by norm_num]
    exact Gamma_two_thirds_Pconstructible h
  · rw [show ((5 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 5 / 6 by norm_num]
    exact h56

/-! ### Denominator `4`, and with it denominator `8`

`Γ(1/4)` gives its own family by reflection alone. Adding `Γ(1/8)` gives denominator `8`,
and the interesting step is that `Γ(3/8)` need not be assumed: reflection turns `Γ(1/8)`
into `Γ(7/8)` and `Γ(1/4)` into `Γ(3/4)`, and duplication at `s = 3/8` — where
`Γ(s + 1/2) = Γ(7/8)` and `Γ(2s) = Γ(3/4)` — then produces `Γ(3/8)`.

Read the other way, the same two identities recover `Γ(1/4)` from `Γ(1/8)` and `Γ(3/8)`
(`Gamma_one_quarter_Pconstructible_of_eighths`). So the two pairs `{Γ(1/4), Γ(1/8)}` and
`{Γ(1/8), Γ(3/8)}` are interchangeable as inputs. -/

-- Theorem: `Γ(3/4)` is P-constructible as soon as `Γ(1/4)` is, by reflection.
theorem Gamma_three_quarters_Pconstructible (h : PConstructible (Real.Gamma (1 / 4))) :
    PConstructible (Real.Gamma (3 / 4)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 4) (by norm_num)) h
  rwa [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at this

-- Theorem: `Γ(n/4)` is P-constructible for every integer `n`, given `Γ(1/4)`.
theorem Gamma_intCast_div_four_Pconstructible (h : PConstructible (Real.Gamma (1 / 4)))
    (n : ℤ) : PConstructible (Real.Gamma ((n : ℝ) / 4)) := by
  rw [show ((n : ℝ)) / 4 = (n : ℝ) / ((4 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 0 by norm_num, Real.Gamma_zero]
    exact zero_Pconstructible
  · rw [show ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 1 / 4 by norm_num]
    exact h
  · rw [show ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 1 / 2 by norm_num]
    exact Gamma_one_half_Pconstructible
  · rw [show ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 3 / 4 by norm_num]
    exact Gamma_three_quarters_Pconstructible h

-- Theorem: `Γ(7/8)` is P-constructible as soon as `Γ(1/8)` is, by reflection.
theorem Gamma_seven_eighths_Pconstructible (h : PConstructible (Real.Gamma (1 / 8))) :
    PConstructible (Real.Gamma (7 / 8)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 8) (by norm_num)) h
  rwa [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num] at this

-- Theorem: `Γ(3/8)` is P-constructible given `Γ(1/4)` and `Γ(1/8)`, by duplication at
-- `s = 3/8`. It is a consequence, not a further assumption.
theorem Gamma_three_eighths_Pconstructible (h₄ : PConstructible (Real.Gamma (1 / 4)))
    (h₈ : PConstructible (Real.Gamma (1 / 8))) : PConstructible (Real.Gamma (3 / 8)) := by
  refine Gamma_of_add_half_Pconstructible (ratval_Pconstructible (3 / 8) (by norm_num)) ?_ ?_
  · rw [show (3 : ℝ) / 8 + 1 / 2 = 7 / 8 by norm_num]
    exact Gamma_seven_eighths_Pconstructible h₈
  · rw [show (2 : ℝ) * (3 / 8) = 3 / 4 by norm_num]
    exact Gamma_three_quarters_Pconstructible h₄

-- Theorem: conversely, `Γ(1/4)` is P-constructible given `Γ(1/8)` and `Γ(3/8)`. The same
-- duplication at `s = 3/8`, read in the other direction, gives `Γ(3/4)`; reflection then
-- gives `Γ(1/4)`.
theorem Gamma_one_quarter_Pconstructible_of_eighths
    (h₈ : PConstructible (Real.Gamma (1 / 8))) (h₃₈ : PConstructible (Real.Gamma (3 / 8))) :
    PConstructible (Real.Gamma (1 / 4)) := by
  have h34 : PConstructible (Real.Gamma (3 / 4)) := by
    have := Gamma_two_mul_Pconstructible (ratval_Pconstructible (3 / 8) (by norm_num)) h₃₈
      (by rw [show (3 : ℝ) / 8 + 1 / 2 = 7 / 8 by norm_num]
          exact Gamma_seven_eighths_Pconstructible h₈)
    rwa [show (2 : ℝ) * (3 / 8) = 3 / 4 by norm_num] at this
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (3 / 4) (by norm_num)) h34
  rwa [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num] at this

-- Theorem: `Γ(n/8)` is P-constructible for every integer `n`, given `Γ(1/4)` and `Γ(1/8)`.
theorem Gamma_intCast_div_eight_Pconstructible (h₄ : PConstructible (Real.Gamma (1 / 4)))
    (h₈ : PConstructible (Real.Gamma (1 / 8))) (n : ℤ) :
    PConstructible (Real.Gamma ((n : ℝ) / 8)) := by
  have h38 : PConstructible (Real.Gamma (3 / 8)) := Gamma_three_eighths_Pconstructible h₄ h₈
  have h58 : PConstructible (Real.Gamma (5 / 8)) := by
    have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (3 / 8) (by norm_num)) h38
    rwa [show (1 : ℝ) - 3 / 8 = 5 / 8 by norm_num] at this
  rw [show ((n : ℝ)) / 8 = (n : ℝ) / ((8 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 0 by norm_num, Real.Gamma_zero]
    exact zero_Pconstructible
  · rw [show ((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 1 / 8 by norm_num]
    exact h₈
  · rw [show ((2 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 1 / 4 by norm_num]
    exact h₄
  · rw [show ((3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 3 / 8 by norm_num]
    exact h38
  · rw [show ((4 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 1 / 2 by norm_num]
    exact Gamma_one_half_Pconstructible
  · rw [show ((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 5 / 8 by norm_num]
    exact h58
  · rw [show ((6 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 3 / 4 by norm_num]
    exact Gamma_three_quarters_Pconstructible h₄
  · rw [show ((7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 7 / 8 by norm_num]
    exact Gamma_seven_eighths_Pconstructible h₈

end Pconstructible
