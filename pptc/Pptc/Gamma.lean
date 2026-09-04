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
import Mathlib.MeasureTheory.Function.JacobianOneDim

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
half-integers and nothing more, since `Γ(1/2) = √π` is itself elementary; that case is
`Gamma_intCast_div_two_Pconstructible`. Every finer denominator needs one genuinely new
number from outside the functional equations, and the natural source is the elliptic
integrals, which `Pptc.Basic` has already shown to be P-constructible in all three kinds.
The relevant classical identities are

    Γ(1/4) ^ 2 = 4 √π · K(1/√2)                              (the lemniscatic case)
    Γ(1/3) ^ 3 = 2 ^ (7/3) π · K(k₃) / 3 ^ (1/4),   k₃ = sin (π / 12)

and a companion at the second singular value `k₂ = √2 - 1` giving `Γ(1/8) Γ(3/8)`.

The first of these is **proved** here, in the section on `Γ(1/4)`: it is the one of the
three whose change of variables is elementary, a single substitution `x = cos⁴ t` in
Mathlib's Beta integral. That makes denominators `2` and `4` unconditional families, and
leaves `Γ(1/3)` and `Γ(1/8)` as the two named hypotheses still carried below.

Both remaining inputs are harder for the same reason: their change of variables is not a
substitution but an algebraic correspondence between curves. For `Γ(1/3)` the target is
`∫₀¹ dt/√(1 - t³) = 2 · K(sin (π/12)) / 3 ^ (3/4)`, a cubic reduced to Legendre form; for
`Γ(1/8)` the relevant curve is not even elliptic on the nose, and the classical derivation
goes through complex multiplication at discriminant `-8` rather than through any integral
identity Mathlib can currently reach.

What the two surviving hypotheses buy is more than the bare inputs suggest:

* `Γ(1/3)` alone gives every rational with denominator `3` *and* every one with
  denominator `6`, since duplication at `s = 1/6` reads `Γ(1/6)` off `Γ(1/3)` and `Γ(2/3)`.
* `Γ(1/8)` alone gives every rational with denominator `8`; in particular `Γ(3/8)` is
  *derived*, not assumed, by duplication at `s = 3/8` against the now-unconditional
  `Γ(3/4)`. Equally, `Γ(3/8)` alone would do, by the same identity read backwards.

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

/-! ### The half-integers: free of any transcendental input

`Γ(1/2) = √π` is already elementary, so the functional equations settle every argument in
`(1/2) ℤ` with nothing imported from outside them. Since duplication only ever relates a
denominator to its double, this is exactly as far as the functional equations reach on their
own: denominator `4` is unconditional too, but only because `Γ(1/4)` is separately supplied
by the elliptic integral below. -/

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

/-! ### The lemniscatic value `Γ(1/4)`

The first transcendental input — and, unlike the ones needed for denominators `3` and `8`,
one that an elementary change of variables can supply, so it is *proved* here rather than
assumed.

The classical statement is `Γ(1/4)² = 4 √π · K(1/√2)`, with `K` the complete elliptic
integral of the first kind. `Pptc.Basic` already reaches `K` at every P-constructible
modulus (`ellipticF_Pconstructible`, via the arc length of an ellipse), so the identity
exhibits `Γ(1/4)` as the square root of a P-constructible number.

The route is Mathlib's Beta integral. `Γ(1/4) Γ(1/2) = Γ(3/4) Β(1/4, 1/2)` together with
reflection reduces everything to

    Β(1/4, 1/2) = ∫₀¹ x ^ (-3/4) (1 - x) ^ (-1/2) dx = 2 √2 · K(1/√2),

and that is a single substitution `x = cos⁴ t`. The textbook route takes two steps,
`x = s⁴` and then `s = cos t`; composing them is what makes the endpoints tractable, since
the resulting `t`-integrand `4 / √(1 + cos² t)` is continuous on all of `ℝ` even though the
`x`-integrand blows up at both ends of `[0, 1]`.

Those singularities are still there in the `x`-integrand, which rules out the interval
change-of-variables lemmas: they want continuity on the *closed* interval. The
measure-theoretic `integral_image_eq_integral_abs_deriv_smul` does not — it asks only for a
derivative and injectivity on a measurable set, here the open `Ioo 0 (π/2)`, and imposes no
integrability hypothesis at all. Hence the detour through set integrals over `Ioo` and
back. -/

section Lemniscatic

open MeasureTheory Set

/-- The substitution carrying `Ioo 0 (π/2)` onto `Ioo 0 1` that turns the Beta integrand
`x ^ (-3/4) (1 - x) ^ (-1/2)` into a constant multiple of the first-kind elliptic
integrand at parameter `1/2`. -/
noncomputable def cosFourth (t : ℝ) : ℝ := Real.cos t ^ 4

-- Theorem: `cos` is positive on the open first quadrant.
theorem cos_pos_of_mem_Ioo {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) : 0 < Real.cos t :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩

-- Theorem: `sin` is positive on the open first quadrant.
theorem sin_pos_of_mem_Ioo {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) : 0 < Real.sin t :=
  Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])

-- Theorem: `cos⁴` maps the open first quadrant *onto* `(0, 1)`. The forward inclusion is
-- the bound `0 < cos t < 1`; the reverse is the intermediate value theorem, which is what
-- makes this an equality of sets and hence usable as a substitution.
theorem cosFourth_image_Ioo : cosFourth '' (Ioo 0 (Real.pi / 2)) = Ioo (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    have h1 : 0 < Real.cos t := cos_pos_of_mem_Ioo ht
    have h2 : Real.cos t < 1 := by
      have h := Real.strictAntiOn_cos (a := 0) (b := t)
      simpa using h ⟨le_refl 0, Real.pi_pos.le⟩
        ⟨ht.1.le, by linarith [ht.2, Real.pi_pos]⟩ ht.1
    refine ⟨pow_pos h1 4, ?_⟩
    change Real.cos t ^ 4 < 1
    calc Real.cos t ^ 4 < 1 ^ 4 := by gcongr
      _ = 1 := one_pow 4
  · have hcont : ContinuousOn cosFourth (Icc 0 (Real.pi / 2)) :=
      (Real.continuous_cos.pow 4).continuousOn
    have := intermediate_value_Ioo' (a := 0) (b := Real.pi / 2)
      (le_of_lt (by positivity)) hcont
    simpa [cosFourth, Real.cos_pi_div_two, Real.cos_zero] using this

-- Theorem: the derivative of the substitution.
theorem hasDerivAt_cosFourth (t : ℝ) :
    HasDerivAt cosFourth ((4 : ℕ) * Real.cos t ^ 3 * (-Real.sin t)) t :=
  (Real.hasDerivAt_cos t).pow 4

-- Theorem: the substitution is injective there, because `cos` is strictly decreasing and
-- positive on the first quadrant.
theorem cosFourth_injOn : InjOn cosFourth (Ioo 0 (Real.pi / 2)) := by
  have hanti : StrictAntiOn cosFourth (Ioo 0 (Real.pi / 2)) := by
    intro x hx y hy hxy
    have hcy : 0 < Real.cos y := cos_pos_of_mem_Ioo hy
    have hlt : Real.cos y < Real.cos x :=
      Real.strictAntiOn_cos ⟨hx.1.le, by linarith [hx.2, Real.pi_pos]⟩
        ⟨hy.1.le, by linarith [hy.2, Real.pi_pos]⟩ hxy
    exact pow_lt_pow_left₀ hlt hcy.le (by norm_num)
  exact hanti.injOn

-- Theorem: the heart of the substitution. Under `x = cos⁴ t` the Beta integrand times the
-- Jacobian collapses completely: the factors `cos ^ (-3)` and `sin ^ (-1)` coming from
-- `x ^ (-3/4)` and from `1 - cos⁴ t = sin² t (2 - sin² t)` cancel against the Jacobian
-- `4 cos³ t sin t`, leaving `4 / √(2 - sin² t) = 2 √2 / √(1 - sin² t / 2)`.
theorem cosFourth_integrand_eq {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    |((4 : ℕ) : ℝ) * Real.cos t ^ 3 * (-Real.sin t)| •
        ((Real.cos t ^ 4) ^ (-(3 : ℝ) / 4) * (1 - Real.cos t ^ 4) ^ (-(1 : ℝ) / 2))
      = 2 * Real.sqrt 2 * ellipticFIntegrand (1 / 2) t := by
  have hc : 0 < Real.cos t := cos_pos_of_mem_Ioo ht
  have hs : 0 < Real.sin t := sin_pos_of_mem_Ioo ht
  have hpy := Real.sin_sq_add_cos_sq t
  have h2s : 0 < 2 - Real.sin t ^ 2 := by nlinarith
  have hfac : 1 - Real.cos t ^ 4 = Real.sin t ^ 2 * (2 - Real.sin t ^ 2) := by nlinarith
  have hA : (Real.cos t ^ 4 : ℝ) ^ (-(3 : ℝ) / 4) = (Real.cos t ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast (Real.cos t) 4, ← Real.rpow_mul hc.le,
      show ((4 : ℕ) : ℝ) * (-(3 : ℝ) / 4) = -(3 : ℝ) by norm_num, Real.rpow_neg hc.le]
    norm_num
  have hB : ((1 : ℝ) - Real.cos t ^ 4) ^ (-(1 : ℝ) / 2)
      = (Real.sin t)⁻¹ * (Real.sqrt (2 - Real.sin t ^ 2))⁻¹ := by
    rw [hfac, Real.mul_rpow (by positivity) h2s.le]
    congr 1
    · rw [← Real.rpow_natCast (Real.sin t) 2, ← Real.rpow_mul hs.le,
        show ((2 : ℕ) : ℝ) * (-(1 : ℝ) / 2) = -(1 : ℝ) by norm_num, Real.rpow_neg hs.le]
      norm_num
    · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h2s.le]
      norm_num
  have hsplit : Real.sqrt (2 - Real.sin t ^ 2)
      = Real.sqrt 2 * Real.sqrt (1 - 1 / 2 * Real.sin t ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num)]
    ring_nf
  have hc3 : 0 < Real.cos t ^ 3 := pow_pos hc 3
  have habs : |((4 : ℕ) : ℝ) * Real.cos t ^ 3 * (-Real.sin t)|
      = 4 * Real.cos t ^ 3 * Real.sin t := by
    rw [abs_of_nonpos (by push_cast; nlinarith)]
    push_cast; ring
  have hQ : 0 < Real.sqrt (1 - 1 / 2 * Real.sin t ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp only [ellipticFIntegrand, ellipticEIntegrand, smul_eq_mul]
  rw [hA, hB, hsplit, habs]
  field_simp
  nlinarith [h22, hQ, h2pos]

-- Theorem: the substitution itself. `Β(1/4, 1/2) = 2 √2 · K(1/√2)`, with the Beta side
-- written as a set integral over the open interval so that no integrability hypothesis is
-- needed anywhere.
theorem beta_one_quarter_one_half_integral :
    (∫ x in Ioo (0 : ℝ) 1, x ^ (-(3 : ℝ) / 4) * (1 - x) ^ (-(1 : ℝ) / 2))
      = 2 * Real.sqrt 2 * ellipticF (1 / 2) (Real.pi / 2) := by
  rw [← cosFourth_image_Ioo, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun x _ => (hasDerivAt_cosFourth x).hasDerivWithinAt) cosFourth_injOn]
  simp only [cosFourth]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun t ht => cosFourth_integrand_eq ht),
    integral_const_mul, ellipticF,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
    integral_Ioc_eq_integral_Ioo]

-- Theorem: Mathlib's Beta integral is complex-valued and uses `cpow`; on `[0, 1]` both
-- bases are nonnegative, so it is the cast of the real integral above.
theorem betaIntegral_one_quarter_one_half :
    Complex.betaIntegral (1 / 4) (1 / 2)
      = ((∫ x in Ioo (0 : ℝ) 1, x ^ (-(3 : ℝ) / 4) * (1 - x) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_ofReal, Complex.betaIntegral]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx1 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
  push_cast
  rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow hx1]
  push_cast
  norm_num

-- Theorem: the lemniscatic identity `Γ(1/4)² = 4 √π · K(1/√2)`. Multiplying the Beta
-- relation `Γ(1/4) √π = Γ(3/4) · 2 √2 K` by `Γ(1/4)` and feeding in reflection
-- `Γ(1/4) Γ(3/4) = π √2` turns the left side into `Γ(1/4)² √π` and the right into `4 π K`.
theorem Gamma_one_quarter_sq :
    Real.Gamma (1 / 4) ^ 2 = 4 * Real.sqrt Real.pi * ellipticF (1 / 2) (Real.pi / 2) := by
  have hbeta : Real.Gamma (1 / 4) * Real.Gamma (1 / 2)
      = Real.Gamma (3 / 4) * (2 * Real.sqrt 2 * ellipticF (1 / 2) (Real.pi / 2)) := by
    have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
      (s := (1 / 4 : ℂ)) (t := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
    rw [betaIntegral_one_quarter_one_half, beta_one_quarter_one_half_integral,
      show ((1 : ℂ) / 4 + 1 / 2) = ((3 / 4 : ℝ) : ℂ) by norm_num,
      show ((1 : ℂ) / 4) = ((1 / 4 : ℝ) : ℂ) by norm_num,
      show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
    exact_mod_cast h
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1 / 4 : ℝ)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num,
    show Real.pi * (1 / 4) = Real.pi / 4 by ring, Real.sin_pi_div_four] at hrefl
  rw [Real.Gamma_one_half_eq] at hbeta
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hppos : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hrefl2 : Real.Gamma (1 / 4) * Real.Gamma (3 / 4) = Real.pi * Real.sqrt 2 := by
    rw [hrefl]
    field_simp
    exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm
  refine mul_right_cancel₀ hppos.ne' ?_
  linear_combination Real.Gamma (1 / 4) * hbeta
    + 2 * Real.sqrt 2 * ellipticF (1 / 2) (Real.pi / 2) * hrefl2
    - 4 * ellipticF (1 / 2) (Real.pi / 2) * hsq
    + 2 * Real.pi * ellipticF (1 / 2) (Real.pi / 2) * h22

-- Theorem: `Γ(1/4)` is P-constructible, unconditionally. `K(1/√2)` is `ellipticF` at
-- parameter `c = k² = 1/2`, which is P-constructible by `ellipticF_Pconstructible`; the
-- identity above then makes `Γ(1/4)²` P-constructible, and `Γ(1/4) > 0` lets `√` recover it.
theorem Gamma_one_quarter_Pconstructible : PConstructible (Real.Gamma (1 / 4)) := by
  have hpos : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hK : PConstructible (ellipticF (1 / 2) (Real.pi / 2)) :=
    ellipticF_Pconstructible half_Pconstructible
      (PConstructible.div pi_Pconstructible two_Pconstructible) (by norm_num)
  have hsq : PConstructible (Real.Gamma (1 / 4) ^ 2) := by
    rw [Gamma_one_quarter_sq]
    exact PConstructible.mul
      (PConstructible.mul (ratval_Pconstructible 4 (by norm_num)) sqrt_pi_Pconstructible) hK
  have h := sqrt_Pconstructible hsq
  rwa [Real.sqrt_sq hpos.le] at h

end Lemniscatic

/-! ### Denominator `4`, and with it denominator `8`

With `Γ(1/4)` in hand unconditionally, denominator `4` is an unconditional family:
reflection supplies `Γ(3/4)`, and `Γ(0)`, `Γ(1/2)` are already known.

Denominator `8` still needs one new input, `Γ(1/8)`. What it does *not* need is `Γ(3/8)`:
reflection turns `Γ(1/8)` into `Γ(7/8)`, and duplication at `s = 3/8` — where
`Γ(s + 1/2) = Γ(7/8)` and `Γ(2s) = Γ(3/4)` — then produces `Γ(3/8)`. Read in the other
direction the same two identities recover `Γ(1/4)` from `Γ(1/8)` and `Γ(3/8)`, so before
`Gamma_one_quarter_Pconstructible` the pairs `{Γ(1/4), Γ(1/8)}` and `{Γ(1/8), Γ(3/8)}` were
interchangeable inputs; now either one of them alone suffices. -/

-- Theorem: `Γ(3/4)` is P-constructible, by reflection from `Γ(1/4)`.
theorem Gamma_three_quarters_Pconstructible : PConstructible (Real.Gamma (3 / 4)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 4) (by norm_num))
    Gamma_one_quarter_Pconstructible
  rwa [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at this

-- Theorem: `Γ(n/4)` is P-constructible for every integer `n`.
theorem Gamma_intCast_div_four_Pconstructible
    (n : ℤ) : PConstructible (Real.Gamma ((n : ℝ) / 4)) := by
  rw [show ((n : ℝ)) / 4 = (n : ℝ) / ((4 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 0 by norm_num, Real.Gamma_zero]
    exact zero_Pconstructible
  · rw [show ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 1 / 4 by norm_num]
    exact Gamma_one_quarter_Pconstructible
  · rw [show ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 1 / 2 by norm_num]
    exact Gamma_one_half_Pconstructible
  · rw [show ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 3 / 4 by norm_num]
    exact Gamma_three_quarters_Pconstructible

-- Theorem: `Γ(7/8)` is P-constructible as soon as `Γ(1/8)` is, by reflection.
theorem Gamma_seven_eighths_Pconstructible (h : PConstructible (Real.Gamma (1 / 8))) :
    PConstructible (Real.Gamma (7 / 8)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 8) (by norm_num)) h
  rwa [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num] at this

-- Theorem: `Γ(3/8)` is P-constructible given `Γ(1/8)`, by duplication at `s = 3/8`. It is
-- a consequence, not a further assumption.
theorem Gamma_three_eighths_Pconstructible
    (h₈ : PConstructible (Real.Gamma (1 / 8))) : PConstructible (Real.Gamma (3 / 8)) := by
  refine Gamma_of_add_half_Pconstructible (ratval_Pconstructible (3 / 8) (by norm_num)) ?_ ?_
  · rw [show (3 : ℝ) / 8 + 1 / 2 = 7 / 8 by norm_num]
    exact Gamma_seven_eighths_Pconstructible h₈
  · rw [show (2 : ℝ) * (3 / 8) = 3 / 4 by norm_num]
    exact Gamma_three_quarters_Pconstructible

-- Theorem: `Γ(n/8)` is P-constructible for every integer `n`, given `Γ(1/8)`.
theorem Gamma_intCast_div_eight_Pconstructible
    (h₈ : PConstructible (Real.Gamma (1 / 8))) (n : ℤ) :
    PConstructible (Real.Gamma ((n : ℝ) / 8)) := by
  have h38 : PConstructible (Real.Gamma (3 / 8)) := Gamma_three_eighths_Pconstructible h₈
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
    exact Gamma_one_quarter_Pconstructible
  · rw [show ((3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 3 / 8 by norm_num]
    exact h38
  · rw [show ((4 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 1 / 2 by norm_num]
    exact Gamma_one_half_Pconstructible
  · rw [show ((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 5 / 8 by norm_num]
    exact h58
  · rw [show ((6 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 3 / 4 by norm_num]
    exact Gamma_three_quarters_Pconstructible
  · rw [show ((7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 7 / 8 by norm_num]
    exact Gamma_seven_eighths_Pconstructible h₈

end Pconstructible
