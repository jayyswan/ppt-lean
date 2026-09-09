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
import Pptc.EllipticFSecondSingular
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Pptc.Level24

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
Two such inputs are **proved** here, each by a change of variables in Mathlib's Beta
integral that lands the answer on `ellipticF`:

    Γ(1/3) ^ 3 = 2 π · 2 ^ (1/3) · 3 ^ (1/4) · F(arccos (2 - √3), (2 + √3)/4)
    Γ(1/4) ^ 2 = 4 √π · K(1/√2)

The second is the lemniscatic case, and its substitution is the single elementary
`x = cos⁴ t`. The first is the equianharmonic one: `Β(1/3, 1/2)` is `3 ∫₀¹ du/√(1 - u³)`,
and reducing that cubic to Legendre form takes a genuine Weierstrass reduction — the
rational map `v = √3 (1 - cos θ)/(1 + cos θ)` applied to `v = 1 - u`, which is a
correspondence between curves rather than a substitution in `u`. The familiar textbook
right-hand side `2 ^ (7/3) π K(sin (π/12)) / 3 ^ (1/4)` is a Landen transformation away
from the incomplete integral written above; P-constructibility does not care which side of
that transformation the value is written on, since `ellipticF_Pconstructible` accepts every
P-constructible parameter below `1` and every P-constructible amplitude.

Between them these settle denominators `1`, `2`, `3`, `4` and `6` unconditionally: `Γ(1/3)`
alone gives denominator `3` *and* denominator `6`, since duplication at `s = 1/6` reads
`Γ(1/6)` off `Γ(1/3)` and `Γ(2/3)`.

Denominator `8` needs a third input, the second singular value `K(√2 - 1)`, whose classical
derivation goes through complex multiplication at discriminant `-8` rather than through any
integral identity Mathlib can currently reach. It is proved in
`Pptc.EllipticFSecondSingular` and imported here, so denominator `8` is unconditional too.
What it buys is more than the bare input suggests: `Γ(3/8)` is *derived*, not assumed, by
duplication at `s = 3/8` against the unconditional `Γ(3/4)`, and equally `Γ(3/8)` alone
would do, by the same identity read backwards.

Doubling the denominator again does need a new input each time: from denominator `8` the
duplication formula only ever delivers the *ratio* `Γ(1/16) / Γ(7/16)`, never either factor,
which is the P-constructible shadow of the fact that each new singular value of `K` is a new
transcendental. Denominator `12` does come for free, but not out of Mathlib: Gauss's
triplication formula gives `Γ(1/12)` from `Γ(1/4)` and `Γ(1/3)`, and since Mathlib proves
only the `k = 2` case of the multiplication theorem, the `k = 3` case is proved from scratch
in `Pptc.GaussMultiplicationK3` and imported here.

Denominator `24` is where this circle of ideas ends. The missing quantity there is the
`χ`-weighted product of the four `Γ(a/24)` with `a` coprime to `24` and below `12`, which
is what a CM period of `ℚ(√-6)` supplies; classically that is Chowla-Selberg at
discriminant `-24`, whose proof needs complex multiplication and the Kronecker limit
formula. `Pptc.Level24` gets it instead by an explicit degree-12 algebraic substitution
carrying the period of `y² = v - v¹³` to a complete elliptic integral, so denominator `24`
is unconditional too, and with it every residue mod `24`. The section that reaches it
explains why no route through the functional equations alone can exist, and why level `24`
is the last one the method reaches at all.
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

/-! ### The equianharmonic value `Γ(1/3)`

The first transcendental input. Like the lemniscatic value below it is *proved* here rather
than assumed, but the change of variables is a genuine reduction of a cubic to Legendre
form rather than a single substitution.

The route is Mathlib's Beta integral. `Γ(1/3) Γ(1/2) = Γ(5/6) Β(1/3, 1/2)` together with
duplication at `s = 1/3` and reflection at `x = 1/3` turns everything into a statement
about

    Β(1/3, 1/2) = ∫₀¹ x ^ (-2/3) (1 - x) ^ (-1/2) dx,

which is `3 ∫₀¹ du / √(1 - u³)` under `x = u³`: the elliptic integral attached to the
cubic `1 - u³`.

**Reducing the cubic.** Write `v = 1 - u`, so that `1 - u³ = v (v² - 3v + 3)` and the cubic
carries its real root at the origin. The quadratic factor has complex roots `(3 ± i√3)/2`,
of modulus `A = √3`, and the classical reduction to Legendre form for a cubic with one real
root is the *rational* substitution

    v = A (1 - cos θ) / (1 + cos θ),

which is `cubicV` below. It is not a substitution in `u` at all, and that is the sense in
which this is harder than the `x = cos⁴ t` of the lemniscatic case. What it buys is a
complete collapse: writing `P = 1 + cos θ` and `c = (2 + √3)/4`,

    v = √3 (1 - cos θ) / P    and    v² - 3v + 3 = 12 (1 - c sin²θ) / P²,

the second because `P² - √3 (1 - cos θ) P + (1 - cos θ)² = 4 - (2 + √3) sin²θ`. Since
`1 - cos θ = sin²θ / P`, the product is `12 √3 sin²θ (1 - c sin²θ) / P⁴` — a perfect square
times the first-kind integrand. The factor `sin θ` cancels against the Jacobian
`2 √3 sin θ / P²`, and nothing algebraic survives.

The modulus is `√c = cos (π/12)`, the *complement* of the classical singular value
`k₃ = sin (π/12)`, and the amplitude `arccos (2 - √3)` falls short of the quarter turn. The
textbook form of the identity applies a Landen transformation to trade this incomplete
integral at `cos (π/12)` for a complete one at `sin (π/12)`; nothing here needs that, since
`ellipticF_Pconstructible` accepts any P-constructible parameter below `1` and any
P-constructible amplitude whatever.

The rest is bookkeeping identical to the lemniscatic case below: the `x`-integrand blows up
at both endpoints, so the substitution is performed by the measure-theoretic
`integral_image_eq_integral_abs_deriv_smul` over the open interval, which asks for a
derivative and injectivity and for no integrability at all. -/

section Equianharmonic

open MeasureTheory Set

/-- The parameter of the elliptic integral the cubic reduces to, `c = (2 + √3)/4`. Its
modulus `√c` is `cos (π/12)`. -/
noncomputable def cubicPar : ℝ := (2 + Real.sqrt 3) / 4

/-- The amplitude at which the reduced integral stops, `arccos (2 - √3)`: the angle at
which the Weierstrass parameter reaches `1` and so `x` reaches `0`. -/
noncomputable def cubicAmp : ℝ := Real.arccos (2 - Real.sqrt 3)

/-- The Weierstrass parameter `v = √3 (1 - cos θ) / (1 + cos θ)`, the rational map that
straightens the cubic `v (v² - 3v + 3)`. -/
noncomputable def cubicV (θ : ℝ) : ℝ := Real.sqrt 3 * ((1 - Real.cos θ) / (1 + Real.cos θ))

/-- The substitution itself, `x = (1 - v)³`, carrying `Ioo 0 cubicAmp` onto `Ioo 0 1`. -/
noncomputable def cubicSub (θ : ℝ) : ℝ := (1 - cubicV θ) ^ 3

/-- The derivative of `cubicV`, namely `2 √3 sin θ / (1 + cos θ)²`. -/
noncomputable def cubicVDer (θ : ℝ) : ℝ :=
  Real.sqrt 3 * (2 * Real.sin θ / (1 + Real.cos θ) ^ 2)

/-- The derivative of `cubicSub`. -/
noncomputable def cubicSubDer (θ : ℝ) : ℝ := -(3 * (1 - cubicV θ) ^ 2 * cubicVDer θ)

/-! #### `√3` and the interval of amplitudes -/

-- Theorem: `√3` squares to `3`.
theorem sq_sqrt_three : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

-- Theorem: `1 < √3`.
theorem one_lt_sqrt_three : 1 < Real.sqrt 3 := by
  nlinarith [sq_sqrt_three, Real.sqrt_nonneg 3]

-- Theorem: `√3 < 2`.
theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  nlinarith [sq_sqrt_three, Real.sqrt_nonneg 3]

-- Theorem: the parameter is below `1`, so the elliptic integrand is real and positive.
theorem cubicPar_lt_one : cubicPar < 1 := by
  rw [cubicPar]; linarith [sqrt_three_lt_two]

-- Theorem: the parameter is P-constructible.
theorem cubicPar_Pconstructible : PConstructible cubicPar :=
  PConstructible.div
    (PConstructible.add two_Pconstructible (sqrt_Pconstructible three_Pconstructible))
    four_Pconstructible

-- Theorem: the amplitude is P-constructible, being an arccosine.
theorem cubicAmp_Pconstructible : PConstructible cubicAmp :=
  arccos_Pconstructible
    (PConstructible.sub two_Pconstructible (sqrt_Pconstructible three_Pconstructible))

-- Theorem: the amplitude is positive, since `2 - √3 < 1`.
theorem cubicAmp_pos : 0 < cubicAmp :=
  Real.arccos_pos.mpr (by linarith [one_lt_sqrt_three])

-- Theorem: the amplitude falls short of the quarter turn, since `2 - √3 > 0`.
theorem cubicAmp_lt_pi_div_two : cubicAmp < Real.pi / 2 :=
  Real.arccos_lt_pi_div_two.mpr (by linarith [sqrt_three_lt_two])

-- Theorem: and so it is below `π`.
theorem cubicAmp_le_pi : cubicAmp ≤ Real.pi := Real.arccos_le_pi _

-- Theorem: the cosine of the amplitude is `2 - √3` — its defining property.
theorem cos_cubicAmp : Real.cos cubicAmp = 2 - Real.sqrt 3 :=
  Real.cos_arccos (by linarith [sqrt_three_lt_two]) (by linarith [one_lt_sqrt_three])

-- Theorem: on the closed interval of amplitudes `cos θ` stays at or above `2 - √3`.
theorem cos_ge_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Icc 0 cubicAmp) :
    2 - Real.sqrt 3 ≤ Real.cos θ :=
  cos_cubicAmp ▸ Real.cos_le_cos_of_nonneg_of_le_pi hθ.1 cubicAmp_le_pi hθ.2

-- Theorem: on the open interval the inequality is strict, `cos` being strictly decreasing.
theorem cos_gt_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Ioo 0 cubicAmp) :
    2 - Real.sqrt 3 < Real.cos θ := by
  have h := Real.strictAntiOn_cos (a := θ) (b := cubicAmp)
    ⟨hθ.1.le, le_trans hθ.2.le cubicAmp_le_pi⟩ ⟨cubicAmp_pos.le, cubicAmp_le_pi⟩ hθ.2
  rwa [cos_cubicAmp] at h

-- Theorem: and `cos θ < 1`, the other end of the same monotonicity.
theorem cos_lt_one_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Ioo 0 cubicAmp) : Real.cos θ < 1 := by
  have h := Real.strictAntiOn_cos (a := 0) (b := θ)
  simpa using h ⟨le_refl 0, Real.pi_pos.le⟩
    ⟨hθ.1.le, le_trans hθ.2.le cubicAmp_le_pi⟩ hθ.1

-- Theorem: the amplitudes lie in the first quadrant, so `sin θ > 0`.
theorem sin_pos_of_mem_Ioo_cubicAmp {θ : ℝ} (hθ : θ ∈ Ioo 0 cubicAmp) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi hθ.1
    (lt_of_lt_of_le hθ.2 (le_trans cubicAmp_lt_pi_div_two.le (by linarith [Real.pi_pos])))

-- Theorem: the denominator `1 + cos θ` of the substitution never vanishes there.
theorem one_add_cos_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 cubicAmp) : 0 < 1 + Real.cos θ := by
  have := cos_gt_of_mem_Ioo hθ
  have := sqrt_three_lt_two
  linarith

/-! #### The Weierstrass parameter runs from `0` to `1` -/

-- Theorem: `v > 0`, because `cos θ < 1`.
theorem cubicV_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 cubicAmp) : 0 < cubicV θ :=
  mul_pos (by linarith [one_lt_sqrt_three])
    (div_pos (by linarith [cos_lt_one_of_mem_Ioo hθ]) (one_add_cos_pos hθ))

-- Theorem: `v < 1`, because `cos θ > 2 - √3` — and `2 - √3` is exactly the cosine at which
-- `√3 (1 - cos θ)` and `1 + cos θ` agree. This is the computation that fixes the amplitude.
theorem cubicV_lt_one {θ : ℝ} (hθ : θ ∈ Ioo 0 cubicAmp) : cubicV θ < 1 := by
  have hP := one_add_cos_pos hθ
  have hc := cos_gt_of_mem_Ioo hθ
  have hr : (0 : ℝ) < Real.sqrt 3 := by linarith [one_lt_sqrt_three]
  have hkey : Real.sqrt 3 * (1 - Real.cos θ) < 1 + Real.cos θ := by
    nlinarith [sq_sqrt_three, mul_pos hr (sub_pos.mpr hc)]
  rw [cubicV, show Real.sqrt 3 * ((1 - Real.cos θ) / (1 + Real.cos θ))
    = Real.sqrt 3 * (1 - Real.cos θ) / (1 + Real.cos θ) by ring, div_lt_one hP]
  exact hkey

-- Theorem: hence the substitution takes values in `(0, 1)`.
theorem cubicSub_mem {θ : ℝ} (hθ : θ ∈ Ioo 0 cubicAmp) : cubicSub θ ∈ Ioo (0 : ℝ) 1 := by
  have h0 := cubicV_pos hθ
  have h1 := cubicV_lt_one hθ
  refine ⟨pow_pos (by linarith) 3, ?_⟩
  calc cubicSub θ = (1 - cubicV θ) ^ 3 := rfl
    _ < 1 ^ 3 := by gcongr; linarith
    _ = 1 := one_pow 3

/-! #### The endpoints, and the substitution as a bijection -/

-- Theorem: at `θ = 0` the parameter is `0`, so `x = 1`.
theorem cubicSub_zero : cubicSub 0 = 1 := by simp [cubicSub, cubicV]

-- Theorem: at `θ = cubicAmp` the parameter is `1`, so `x = 0`.
theorem cubicSub_cubicAmp : cubicSub cubicAmp = 0 := by
  have h3 : (0 : ℝ) < 3 - Real.sqrt 3 := by linarith [sqrt_three_lt_two]
  have hv : cubicV cubicAmp = 1 := by
    rw [cubicV, cos_cubicAmp, show (1 : ℝ) - (2 - Real.sqrt 3) = Real.sqrt 3 - 1 by ring,
      show (1 : ℝ) + (2 - Real.sqrt 3) = 3 - Real.sqrt 3 by ring]
    field_simp
    linear_combination sq_sqrt_three
  rw [cubicSub, hv]; norm_num

-- Theorem: the substitution is continuous on the closed interval, the denominator being
-- bounded away from zero there.
theorem continuousOn_cubicSub : ContinuousOn cubicSub (Icc 0 cubicAmp) := by
  have h : ∀ θ ∈ Icc (0 : ℝ) cubicAmp, 1 + Real.cos θ ≠ 0 := by
    intro θ hθ
    have := cos_ge_of_mem_Icc hθ
    have := sqrt_three_lt_two
    linarith
  unfold cubicSub cubicV
  refine ContinuousOn.pow (ContinuousOn.sub continuousOn_const
    (ContinuousOn.mul continuousOn_const (ContinuousOn.div ?_ ?_ h))) 3
  · exact continuousOn_const.sub Real.continuous_cos.continuousOn
  · exact continuousOn_const.add Real.continuous_cos.continuousOn

-- Theorem: `cubicSub` maps the open interval of amplitudes *onto* `(0, 1)`. The forward
-- inclusion is the bound above; the reverse is the intermediate value theorem, run
-- backwards because the substitution is decreasing.
theorem cubicSub_image_Ioo : cubicSub '' (Ioo 0 cubicAmp) = Ioo (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨θ, hθ, rfl⟩
    exact cubicSub_mem hθ
  · have h := intermediate_value_Ioo' (a := 0) (b := cubicAmp) cubicAmp_pos.le
      continuousOn_cubicSub
    rwa [cubicSub_zero, cubicSub_cubicAmp] at h

-- Theorem: the derivative of the Weierstrass parameter. The quotient rule collapses,
-- because `sin θ (1 + cos θ) + (1 - cos θ) sin θ = 2 sin θ`.
theorem hasDerivAt_cubicV {θ : ℝ} (h : 1 + Real.cos θ ≠ 0) :
    HasDerivAt cubicV (cubicVDer θ) θ := by
  have hnum : HasDerivAt (fun t : ℝ => 1 - Real.cos t) (Real.sin θ) θ := by
    have hc := (Real.hasDerivAt_cos θ).const_sub (1 : ℝ)
    rwa [neg_neg] at hc
  have hden : HasDerivAt (fun t : ℝ => 1 + Real.cos t) (-Real.sin θ) θ :=
    (Real.hasDerivAt_cos θ).const_add (1 : ℝ)
  have hdiv := (hnum.div hden h).const_mul (Real.sqrt 3)
  have heq : Real.sqrt 3 * ((Real.sin θ * (1 + Real.cos θ)
      - (1 - Real.cos θ) * -Real.sin θ) / (1 + Real.cos θ) ^ 2) = cubicVDer θ := by
    rw [cubicVDer]; field_simp; ring
  rw [← heq]
  exact hdiv

-- Theorem: the derivative of the substitution, by the chain rule on the cube.
theorem hasDerivAt_cubicSub {θ : ℝ} (h : 1 + Real.cos θ ≠ 0) :
    HasDerivAt cubicSub (cubicSubDer θ) θ := by
  have hpow := ((hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_cubicV h)).pow 3
  have heq : ((3 : ℕ) : ℝ) * (1 - cubicV θ) ^ (3 - 1) * (0 - cubicVDer θ)
      = cubicSubDer θ := by
    rw [cubicSubDer]; push_cast; ring
  rw [← heq]
  exact hpow

-- Theorem: the substitution is strictly decreasing: `cos` decreases, so `v` increases,
-- so `1 - v` decreases through positive values, and cubing preserves that.
theorem cubicSub_strictAntiOn : StrictAntiOn cubicSub (Ioo 0 cubicAmp) := by
  intro x hx y hy hxy
  have hPx := one_add_cos_pos hx
  have hPy := one_add_cos_pos hy
  have hr : (0 : ℝ) < Real.sqrt 3 := by linarith [one_lt_sqrt_three]
  have hcos : Real.cos y < Real.cos x :=
    Real.strictAntiOn_cos ⟨hx.1.le, le_trans hx.2.le cubicAmp_le_pi⟩
      ⟨hy.1.le, le_trans hy.2.le cubicAmp_le_pi⟩ hxy
  have hv : cubicV x < cubicV y := by
    rw [cubicV, cubicV, show Real.sqrt 3 * ((1 - Real.cos x) / (1 + Real.cos x))
        = Real.sqrt 3 * (1 - Real.cos x) / (1 + Real.cos x) by ring,
      show Real.sqrt 3 * ((1 - Real.cos y) / (1 + Real.cos y))
        = Real.sqrt 3 * (1 - Real.cos y) / (1 + Real.cos y) by ring,
      div_lt_div_iff₀ hPx hPy]
    nlinarith [hcos, hr]
  have hy1 : 0 < 1 - cubicV y := by linarith [cubicV_lt_one hy]
  exact pow_lt_pow_left₀ (by linarith) hy1.le (by norm_num)

-- Theorem: injectivity, which is what the change-of-variables lemma actually wants.
theorem cubicSub_injOn : InjOn cubicSub (Ioo 0 cubicAmp) := cubicSub_strictAntiOn.injOn

/-! #### The collapse of the integrand -/

-- Theorem: the factorization that makes the reduction work. With `P = 1 + cos θ`,
--
--     1 - (1 - v)³ = v (v² - 3v + 3) = 12 √3 sin²θ (1 - c sin²θ) / P⁴,
--
-- a perfect square times the first-kind integrand at parameter `c = (2 + √3)/4`. The
-- leftover factor `v` contributes `√3 (1 - cos θ)/P = √3 sin²θ / P²`, and the quadratic
-- contributes `12 (1 - c sin²θ)/P²`.
theorem one_sub_cubicSub_eq {θ : ℝ} (hP : 1 + Real.cos θ ≠ 0) :
    1 - cubicSub θ = 12 * Real.sqrt 3 * Real.sin θ ^ 2
      * (1 - cubicPar * Real.sin θ ^ 2) / (1 + Real.cos θ) ^ 4 := by
  have hs2 : Real.sin θ ^ 2 = (1 - Real.cos θ) * (1 + Real.cos θ) := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [cubicSub, cubicV, cubicPar, hs2]
  field_simp
  linear_combination (4 * (1 - Real.cos θ) ^ 3 * Real.sqrt 3) * sq_sqrt_three

-- Theorem: consequently `√(1 - x)` is the elliptic integrand times an elementary factor.
-- The perfect square that `one_sub_cubicSub_eq` exhibits has square root
-- `2 · 3 ^ (3/4) · sin θ · √(1 - c sin²θ) / P²`, and `3 ^ (3/4)` is written `√3 · √√3` so
-- that no `rpow` enters the computation.
theorem sqrt_one_sub_cubicSub {θ : ℝ} (hθ : θ ∈ Ioo 0 cubicAmp) :
    Real.sqrt (1 - cubicSub θ)
      = 2 * (Real.sqrt 3 * Real.sqrt (Real.sqrt 3)) * Real.sin θ
          * Real.sqrt (1 - cubicPar * Real.sin θ ^ 2) / (1 + Real.cos θ) ^ 2 := by
  have hs := sin_pos_of_mem_Ioo_cubicAmp hθ
  have hP := one_add_cos_pos hθ
  have hr : (0 : ℝ) < Real.sqrt 3 := by linarith [one_lt_sqrt_three]
  have hq2 : Real.sqrt (Real.sqrt 3) ^ 2 = Real.sqrt 3 := Real.sq_sqrt hr.le
  have hWpos : (0 : ℝ) < Real.sqrt (1 - cubicPar * Real.sin θ ^ 2) :=
    Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos cubicPar_lt_one θ)
  have hWsq : Real.sqrt (1 - cubicPar * Real.sin θ ^ 2) ^ 2
      = 1 - cubicPar * Real.sin θ ^ 2 :=
    Real.sq_sqrt (one_sub_mul_sin_sq_pos cubicPar_lt_one θ).le
  have hsq : (2 * (Real.sqrt 3 * Real.sqrt (Real.sqrt 3)) * Real.sin θ
        * Real.sqrt (1 - cubicPar * Real.sin θ ^ 2) / (1 + Real.cos θ) ^ 2) ^ 2
      = 1 - cubicSub θ := by
    rw [one_sub_cubicSub_eq hP.ne', div_pow,
      show ((1 + Real.cos θ) ^ 2) ^ 2 = (1 + Real.cos θ) ^ 4 by ring]
    congr 1
    linear_combination
      (4 * Real.sqrt 3 ^ 2 * Real.sqrt (Real.sqrt 3) ^ 2 * Real.sin θ ^ 2) * hWsq
      + (4 * Real.sqrt 3 ^ 2 * Real.sin θ ^ 2 * (1 - cubicPar * Real.sin θ ^ 2)) * hq2
      + (4 * Real.sqrt 3 * Real.sin θ ^ 2 * (1 - cubicPar * Real.sin θ ^ 2)) * sq_sqrt_three
  rw [← hsq, Real.sqrt_sq]
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) hs.le) hWpos.le) (by positivity)

-- Theorem: the heart of the reduction. Under `x = cubicSub θ` the Beta integrand times the
-- Jacobian collapses completely: the factor `(1 - v)⁻²` coming from `x ^ (-2/3)` cancels
-- against the `(1 - v)²` in the Jacobian, and the `2 sin θ / P²` left over cancels against
-- the same factor inside `√(1 - x)`, leaving `3 / (3 ^ (1/4) √(1 - c sin²θ))`.
theorem cubicSub_integrand_eq {θ : ℝ} (hθ : θ ∈ Ioo 0 cubicAmp) :
    |cubicSubDer θ| • (cubicSub θ ^ (-(2 : ℝ) / 3) * (1 - cubicSub θ) ^ (-(1 : ℝ) / 2))
      = Real.sqrt 3 * Real.sqrt (Real.sqrt 3) * ellipticFIntegrand cubicPar θ := by
  have hs := sin_pos_of_mem_Ioo_cubicAmp hθ
  have hP := one_add_cos_pos hθ
  have hu : 0 < 1 - cubicV θ := by linarith [cubicV_lt_one hθ]
  have hr : (0 : ℝ) < Real.sqrt 3 := by linarith [one_lt_sqrt_three]
  have hq : (0 : ℝ) < Real.sqrt (Real.sqrt 3) := Real.sqrt_pos.mpr hr
  have hq2 : Real.sqrt (Real.sqrt 3) ^ 2 = Real.sqrt 3 := Real.sq_sqrt hr.le
  have hWpos : (0 : ℝ) < Real.sqrt (1 - cubicPar * Real.sin θ ^ 2) :=
    Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos cubicPar_lt_one θ)
  have hx := cubicSub_mem hθ
  have hA : cubicSub θ ^ (-(2 : ℝ) / 3) = ((1 - cubicV θ) ^ 2)⁻¹ := by
    rw [show cubicSub θ = (1 - cubicV θ) ^ 3 from rfl,
      ← Real.rpow_natCast (1 - cubicV θ) 3, ← Real.rpow_mul hu.le,
      show ((3 : ℕ) : ℝ) * (-(2 : ℝ) / 3) = -(2 : ℝ) by norm_num, Real.rpow_neg hu.le]
    norm_num
  have hB : ((1 : ℝ) - cubicSub θ) ^ (-(1 : ℝ) / 2) = (Real.sqrt (1 - cubicSub θ))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith [hx.2] : (0 : ℝ) ≤ 1 - cubicSub θ)]
    norm_num
  have hvd : 0 < cubicVDer θ := by
    rw [cubicVDer]
    exact mul_pos hr (div_pos (by linarith) (pow_pos hP 2))
  have habs : |cubicSubDer θ| = 3 * (1 - cubicV θ) ^ 2 * cubicVDer θ := by
    rw [cubicSubDer, abs_neg, abs_of_nonneg (mul_nonneg (by positivity) hvd.le)]
  rw [smul_eq_mul, habs, hA, hB, sqrt_one_sub_cubicSub hθ, ellipticFIntegrand,
    ellipticEIntegrand, cubicVDer]
  set W := Real.sqrt (1 - cubicPar * Real.sin θ ^ 2) with hWdef
  field_simp
  linear_combination (-Real.sqrt 3) * hq2 - sq_sqrt_three

/-! #### From the Beta integral to `Γ(1/3)`

The substitution is now performed, and what remains is the three-way algebra between the
Beta relation `Γ(1/3) Γ(1/2) = Γ(5/6) Β(1/3, 1/2)`, duplication at `s = 1/3` (which reads
`Γ(1/3) Γ(5/6) = Γ(2/3) 2 ^ (1/3) √π`) and reflection at `x = 1/3` (which reads
`Γ(1/3) Γ(2/3) √3 = 2π`). Multiplying the first by `Γ(1/3)` and substituting the second
cancels `√π` and leaves `Γ(1/3)² = Γ(2/3) 2 ^ (1/3) Β`; multiplying by `Γ(1/3)` once more
and substituting the third turns the left side into `Γ(1/3)³` and clears the last
`Γ(2/3)`. -/

-- Theorem: the substitution, with the Beta side written as a set integral over the open
-- interval so that no integrability hypothesis is needed anywhere.
theorem beta_one_third_one_half_integral :
    (∫ x in Ioo (0 : ℝ) 1, x ^ (-(2 : ℝ) / 3) * (1 - x) ^ (-(1 : ℝ) / 2))
      = Real.sqrt 3 * Real.sqrt (Real.sqrt 3) * ellipticF cubicPar cubicAmp := by
  rw [← cubicSub_image_Ioo, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun x hx => (hasDerivAt_cubicSub (one_add_cos_pos hx).ne').hasDerivWithinAt)
      cubicSub_injOn]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun t ht => cubicSub_integrand_eq ht),
    integral_const_mul, ellipticF, intervalIntegral.integral_of_le cubicAmp_pos.le,
    integral_Ioc_eq_integral_Ioo]

-- Theorem: Mathlib's Beta integral is complex-valued and uses `cpow`; on `[0, 1]` both
-- bases are nonnegative, so it is the cast of the real integral above.
theorem betaIntegral_one_third_one_half :
    Complex.betaIntegral (1 / 3) (1 / 2)
      = ((∫ x in Ioo (0 : ℝ) 1, x ^ (-(2 : ℝ) / 3) * (1 - x) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
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

-- Theorem: the equianharmonic identity `Γ(1/3)³ = 2 π · 2 ^ (1/3) · 3 ^ (1/4) · F`, with
-- `F` the incomplete elliptic integral of the first kind at parameter `(2 + √3)/4` and
-- amplitude `arccos (2 - √3)`. Written with `3 ^ (1/4)` spelled `√√3`.
theorem Gamma_one_third_cube :
    Real.Gamma (1 / 3) ^ 3
      = 2 * Real.pi * (2 : ℝ) ^ ((1 : ℝ) / 3) * Real.sqrt (Real.sqrt 3)
          * ellipticF cubicPar cubicAmp := by
  have hr : (0 : ℝ) < Real.sqrt 3 := by linarith [one_lt_sqrt_three]
  have hppos : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hbeta : Real.Gamma (1 / 3) * Real.sqrt Real.pi
      = Real.Gamma (5 / 6)
          * (Real.sqrt 3 * Real.sqrt (Real.sqrt 3) * ellipticF cubicPar cubicAmp) := by
    have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
      (s := (1 / 3 : ℂ)) (t := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
    rw [betaIntegral_one_third_one_half, beta_one_third_one_half_integral,
      show ((1 : ℂ) / 3 + 1 / 2) = ((5 / 6 : ℝ) : ℂ) by norm_num,
      show ((1 : ℂ) / 3) = ((1 / 3 : ℝ) : ℂ) by norm_num,
      show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
    rw [← Real.Gamma_one_half_eq]
    exact_mod_cast h
  have hdup : Real.Gamma (1 / 3) * Real.Gamma (5 / 6)
      = Real.Gamma (2 / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) * Real.sqrt Real.pi := by
    have h := Real.Gamma_mul_Gamma_add_half (1 / 3 : ℝ)
    rw [show (1 : ℝ) / 3 + 1 / 2 = 5 / 6 by norm_num,
      show (2 : ℝ) * (1 / 3) = 2 / 3 by norm_num,
      show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num] at h
    exact h
  have hrefl : Real.Gamma (1 / 3) * Real.Gamma (2 / 3) * Real.sqrt 3 = 2 * Real.pi := by
    have h := Real.Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
      show Real.pi * (1 / 3) = Real.pi / 3 by ring, Real.sin_pi_div_three] at h
    rw [h]
    field_simp
  have step : Real.Gamma (1 / 3) ^ 2
      = Real.Gamma (2 / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3)
          * (Real.sqrt 3 * Real.sqrt (Real.sqrt 3) * ellipticF cubicPar cubicAmp) := by
    refine mul_right_cancel₀ hppos.ne' ?_
    linear_combination Real.Gamma (1 / 3) * hbeta
      + (Real.sqrt 3 * Real.sqrt (Real.sqrt 3) * ellipticF cubicPar cubicAmp) * hdup
  linear_combination Real.Gamma (1 / 3) * step
    + ((2 : ℝ) ^ ((1 : ℝ) / 3) * Real.sqrt (Real.sqrt 3)
        * ellipticF cubicPar cubicAmp) * hrefl

-- Theorem: `Γ(1/3)` is P-constructible, unconditionally. Every factor on the right of the
-- identity above is reachable — `2 ^ (1/3)` by `rpow_two_Pconstructible`, `3 ^ (1/4)` by
-- two square roots, `F` by `ellipticF_Pconstructible` — so `Γ(1/3)³` is P-constructible,
-- and `Γ(1/3) > 0` lets the cube root, which is `rpow_Pconstructible` at exponent `1/3`,
-- recover the value itself.
theorem Gamma_one_third_Pconstructible : PConstructible (Real.Gamma (1 / 3)) := by
  have hpos : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hF : PConstructible (ellipticF cubicPar cubicAmp) :=
    ellipticF_Pconstructible cubicPar_Pconstructible cubicAmp_Pconstructible cubicPar_lt_one
  have hcube : PConstructible (Real.Gamma (1 / 3) ^ 3) := by
    rw [Gamma_one_third_cube]
    exact PConstructible.mul (PConstructible.mul (PConstructible.mul
      (PConstructible.mul two_Pconstructible pi_Pconstructible)
      (rpow_two_Pconstructible (ratval_Pconstructible (1 / 3) (by norm_num))))
      (sqrt_Pconstructible (sqrt_Pconstructible three_Pconstructible))) hF
  have h := rpow_Pconstructible (b := (1 : ℝ) / 3) hcube
    (ratval_Pconstructible (1 / 3) (by norm_num)) (pow_pos hpos 3)
  rwa [← Real.rpow_natCast (Real.Gamma (1 / 3)) 3, ← Real.rpow_mul hpos.le,
    show ((3 : ℕ) : ℝ) * ((1 : ℝ) / 3) = 1 by norm_num, Real.rpow_one] at h

end Equianharmonic

/-! ### Denominator `3`, and with it denominator `6`

The one value `Γ(1/3)` buys two whole families, and it is now in hand unconditionally.
Reflection turns it into `Γ(2/3)`, and then duplication at `s = 1/6` — where
`Γ(s + 1/2) = Γ(2/3)` and `Γ(2s) = Γ(1/3)` are both available — reads off `Γ(1/6)`.
Reflection again gives `Γ(5/6)`, and the residues `2/6`, `3/6`, `4/6` are values already
known. Both families are therefore unconditional. -/

-- Theorem: `Γ(2/3)` is P-constructible, by reflection from `Γ(1/3)`.
theorem Gamma_two_thirds_Pconstructible : PConstructible (Real.Gamma (2 / 3)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 3) (by norm_num))
    Gamma_one_third_Pconstructible
  rwa [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at this

-- Theorem: `Γ(1/6)` is P-constructible, by duplication at `s = 1/6`.
theorem Gamma_one_sixth_Pconstructible : PConstructible (Real.Gamma (1 / 6)) := by
  refine Gamma_of_add_half_Pconstructible (ratval_Pconstructible (1 / 6) (by norm_num)) ?_ ?_
  · rw [show (1 : ℝ) / 6 + 1 / 2 = 2 / 3 by norm_num]
    exact Gamma_two_thirds_Pconstructible
  · rw [show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num]
    exact Gamma_one_third_Pconstructible

-- Theorem: `Γ(n/3)` is P-constructible for every integer `n`.
theorem Gamma_intCast_div_three_Pconstructible
    (n : ℤ) : PConstructible (Real.Gamma ((n : ℝ) / 3)) := by
  rw [show ((n : ℝ)) / 3 = (n : ℝ) / ((3 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = 0 by norm_num, Real.Gamma_zero]
    exact zero_Pconstructible
  · rw [show ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = 1 / 3 by norm_num]
    exact Gamma_one_third_Pconstructible
  · rw [show ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = 2 / 3 by norm_num]
    exact Gamma_two_thirds_Pconstructible

-- Theorem: `Γ(n/6)` is P-constructible for every integer `n`. No separate input about
-- `Γ(1/6)` is needed; duplication supplies it from `Γ(1/3)`.
theorem Gamma_intCast_div_six_Pconstructible
    (n : ℤ) : PConstructible (Real.Gamma ((n : ℝ) / 6)) := by
  have h56 : PConstructible (Real.Gamma (5 / 6)) := by
    have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 6) (by norm_num))
      Gamma_one_sixth_Pconstructible
    rwa [show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num] at this
  rw [show ((n : ℝ)) / 6 = (n : ℝ) / ((6 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 0 by norm_num, Real.Gamma_zero]
    exact zero_Pconstructible
  · rw [show ((1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 1 / 6 by norm_num]
    exact Gamma_one_sixth_Pconstructible
  · rw [show ((2 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 1 / 3 by norm_num]
    exact Gamma_one_third_Pconstructible
  · rw [show ((3 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 1 / 2 by norm_num]
    exact Gamma_one_half_Pconstructible
  · rw [show ((4 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 2 / 3 by norm_num]
    exact Gamma_two_thirds_Pconstructible
  · rw [show ((5 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 5 / 6 by norm_num]
    exact h56

/-! ### The lemniscatic value `Γ(1/4)`

The second transcendental input, and the easier of the two: unlike the equianharmonic case
above, and unlike the one still needed for denominator `8`, a single elementary
substitution supplies it.

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

/-! ### The second singular value, and with it `Γ(1/8)`

`k₂ = √2 - 1` is the modulus at which `K'/K = √2`. Evaluating `K` there is Chowla-Selberg
at discriminant `-8`; it is a genuine theorem (Whittaker-Watson; Borwein-Borwein, *Pi and
the AGM*), but its proof needs complex multiplication and the Kronecker limit formula,
neither of which Mathlib has. It is proved in `Pptc.EllipticFSecondSingular`, by a
degree-2 algebraic substitution, and everything derived from it is elementary. -/

-- Theorem: the parameter `c = k₂² = (√2 - 1)²` lies below `1`, so `K` there is covered by
-- `ellipticF_Pconstructible`.
theorem secondSingularPar_lt_one : (Real.sqrt 2 - 1) ^ 2 < 1 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

-- Theorem: that parameter is P-constructible.
theorem secondSingularPar_Pconstructible : PConstructible ((Real.sqrt 2 - 1) ^ 2) :=
  sq_Pconstructible
    (PConstructible.sub (sqrt_Pconstructible two_Pconstructible) PConstructible.base_one)

-- Theorem: hence the product `Γ(1/8) Γ(3/8)` is P-constructible — the singular value
-- identity read as a statement about `Γ`.
theorem Gamma_one_eighth_mul_three_eighths_Pconstructible :
    PConstructible (Real.Gamma (1 / 8) * Real.Gamma (3 / 8)) := by
  have hK : PConstructible (ellipticF ((Real.sqrt 2 - 1) ^ 2) (Real.pi / 2)) :=
    ellipticF_Pconstructible secondSingularPar_Pconstructible
      (PConstructible.div pi_Pconstructible two_Pconstructible) secondSingularPar_lt_one
  have hroot : (0 : ℝ) < Real.sqrt (Real.sqrt 2 + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ ((13 : ℝ) / 4) := Real.rpow_pos_of_pos two_pos _
  have hsolve : Real.Gamma (1 / 8) * Real.Gamma (3 / 8)
      = ellipticF ((Real.sqrt 2 - 1) ^ 2) (Real.pi / 2)
          * ((2 : ℝ) ^ ((13 : ℝ) / 4) * Real.sqrt Real.pi)
          / Real.sqrt (Real.sqrt 2 + 1) := by
    rw [ellipticF_secondSingular]
    field_simp
  rw [hsolve]
  exact PConstructible.div
    (PConstructible.mul hK
      (PConstructible.mul (rpow_two_Pconstructible (ratval_Pconstructible (13 / 4) (by norm_num)))
        sqrt_pi_Pconstructible))
    (sqrt_Pconstructible
      (PConstructible.add (sqrt_Pconstructible two_Pconstructible) PConstructible.base_one))

-- Theorem: `Γ(1/8)` is P-constructible. `Γ(7/8)` cancels between reflection at `1/8` and
-- duplication at `s = 3/8` (whose `Γ(2s) = Γ(3/4)` is unconditional), leaving `Γ(1/8)²` as
-- the assumed product times an elementary factor; `Γ(1/8) > 0` then recovers the value.
theorem Gamma_one_eighth_Pconstructible : PConstructible (Real.Gamma (1 / 8)) := by
  have hpos : 0 < Real.Gamma (1 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have h38 : 0 < Real.Gamma (3 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have h78 : 0 < Real.Gamma (7 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have hrefl : Real.Gamma (1 / 8) * Real.Gamma (7 / 8)
      = Real.pi / Real.sin (Real.pi * (1 / 8)) := by
    have h := Real.Gamma_mul_Gamma_one_sub (1 / 8 : ℝ)
    rwa [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num] at h
  have hdup : Real.Gamma (3 / 8) * Real.Gamma (7 / 8) = Real.Gamma (3 / 4) * dupFactor (3 / 8) := by
    have h := Gamma_mul_Gamma_add_half' (3 / 8 : ℝ)
    rwa [show (3 : ℝ) / 8 + 1 / 2 = 7 / 8 by norm_num,
      show (2 : ℝ) * (3 / 8) = 3 / 4 by norm_num] at h
  have hsq : PConstructible (Real.Gamma (1 / 8) ^ 2) := by
    have key : Real.Gamma (1 / 8) ^ 2
        = Real.Gamma (1 / 8) * Real.Gamma (3 / 8) * (Real.Gamma (1 / 8) * Real.Gamma (7 / 8))
            / (Real.Gamma (3 / 8) * Real.Gamma (7 / 8)) := by
      field_simp
    rw [key, hrefl, hdup]
    exact PConstructible.div
      (PConstructible.mul Gamma_one_eighth_mul_three_eighths_Pconstructible
        (PConstructible.div pi_Pconstructible
          (sin_Pconstructible
            (PConstructible.mul pi_Pconstructible (ratval_Pconstructible (1 / 8) (by norm_num))))))
      (PConstructible.mul Gamma_three_quarters_Pconstructible
        (dupFactor_Pconstructible (ratval_Pconstructible (3 / 8) (by norm_num))))
  have h := sqrt_Pconstructible hsq
  rwa [Real.sqrt_sq hpos.le] at h

-- Theorem: `Γ(7/8)` is P-constructible, by reflection from `Γ(1/8)`.
theorem Gamma_seven_eighths_Pconstructible :
    PConstructible (Real.Gamma (7 / 8)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 8) (by norm_num))
    Gamma_one_eighth_Pconstructible
  rwa [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num] at this

-- Theorem: `Γ(3/8)` is P-constructible, by duplication at `s = 3/8`. It is a consequence of
-- `Γ(1/8)`, not a further assumption.
theorem Gamma_three_eighths_Pconstructible :
    PConstructible (Real.Gamma (3 / 8)) := by
  refine Gamma_of_add_half_Pconstructible (ratval_Pconstructible (3 / 8) (by norm_num)) ?_ ?_
  · rw [show (3 : ℝ) / 8 + 1 / 2 = 7 / 8 by norm_num]
    exact Gamma_seven_eighths_Pconstructible
  · rw [show (2 : ℝ) * (3 / 8) = 3 / 4 by norm_num]
    exact Gamma_three_quarters_Pconstructible

-- Theorem: `Γ(n/8)` is P-constructible for every integer `n`, unconditionally.
theorem Gamma_intCast_div_eight_Pconstructible
    (n : ℤ) :
    PConstructible (Real.Gamma ((n : ℝ) / 8)) := by
  have h38 : PConstructible (Real.Gamma (3 / 8)) := Gamma_three_eighths_Pconstructible
  have h58 : PConstructible (Real.Gamma (5 / 8)) := by
    have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (3 / 8) (by norm_num)) h38
    rwa [show (1 : ℝ) - 3 / 8 = 5 / 8 by norm_num] at this
  rw [show ((n : ℝ)) / 8 = (n : ℝ) / ((8 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 0 by norm_num, Real.Gamma_zero]
    exact zero_Pconstructible
  · rw [show ((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 1 / 8 by norm_num]
    exact Gamma_one_eighth_Pconstructible
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
    exact Gamma_seven_eighths_Pconstructible


/-! ### Gauss's triplication, and with it `Γ(1/12)`

Mathlib proves only the `k = 2` case of Gauss's multiplication theorem, so the `k = 3` case
is proved from scratch in `Pptc.GaussMultiplicationK3` — Bohr-Mollerup on `(0, ∞)`, then
descent along the recurrence to the rest of the line — and used here as
`Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds`. Unlike the singular value above it
needs no transcendental input at all: it is a functional equation of the same character as
duplication and reflection, and with it denominator `12` follows from the already
unconditional `Γ(1/4)`, `Γ(1/3)` and `Γ(1/6)`. Duplication and reflection alone do not
suffice: they pin down `Γ(1/12) / Γ(5/12)` but never either factor. Triplication at
`s = 1/12` supplies the missing *product* `Γ(1/12) Γ(5/12)`, and product times ratio is a
square. -/

-- Theorem: `Γ(5/6)` is P-constructible, by reflection from `Γ(1/6)`.
theorem Gamma_five_sixths_Pconstructible : PConstructible (Real.Gamma (5 / 6)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 6) (by norm_num))
    Gamma_one_sixth_Pconstructible
  rwa [show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num] at this

-- Theorem: triplication at `s = 1/12`, where the third factor `Γ(3/4)` and the right-hand
-- side's `Γ(1/4)` are both already unconditional. This is the product that duplication and
-- reflection cannot reach.
theorem Gamma_one_twelfth_mul_five_twelfths :
    Real.Gamma (1 / 12) * Real.Gamma (5 / 12)
      = 2 * Real.pi * (3 : ℝ) ^ ((1 : ℝ) / 4) * Real.Gamma (1 / 4) / Real.Gamma (3 / 4) := by
  have h := Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds (1 / 12 : ℝ)
  rw [show (1 : ℝ) / 12 + 1 / 3 = 5 / 12 by norm_num,
    show (1 : ℝ) / 12 + 2 / 3 = 3 / 4 by norm_num,
    show (3 : ℝ) * (1 / 12) = 1 / 4 by norm_num,
    show (1 : ℝ) / 2 - 1 / 4 = 1 / 4 by norm_num] at h
  have h34 : Real.Gamma (3 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  field_simp
  linear_combination h

-- Theorem: hence that product is P-constructible.
theorem Gamma_one_twelfth_mul_five_twelfths_Pconstructible :
    PConstructible (Real.Gamma (1 / 12) * Real.Gamma (5 / 12)) := by
  rw [Gamma_one_twelfth_mul_five_twelfths]
  exact PConstructible.div
    (PConstructible.mul
      (PConstructible.mul
        (PConstructible.mul two_Pconstructible pi_Pconstructible)
        (rpow_Pconstructible three_Pconstructible
          (ratval_Pconstructible (1 / 4) (by norm_num)) (by norm_num)))
      Gamma_one_quarter_Pconstructible)
    Gamma_three_quarters_Pconstructible

-- Theorem: `Γ(1/12)` is P-constructible. `Γ(11/12)` cancels between reflection at `1/12`
-- and duplication at `s = 5/12` (whose `Γ(2s) = Γ(5/6)` is unconditional), leaving
-- `Γ(1/12)²` as the triplication product times an elementary factor.
theorem Gamma_one_twelfth_Pconstructible : PConstructible (Real.Gamma (1 / 12)) := by
  have hpos : 0 < Real.Gamma (1 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have h512 : 0 < Real.Gamma (5 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have h1112 : 0 < Real.Gamma (11 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have hrefl : Real.Gamma (1 / 12) * Real.Gamma (11 / 12)
      = Real.pi / Real.sin (Real.pi * (1 / 12)) := by
    have h := Real.Gamma_mul_Gamma_one_sub (1 / 12 : ℝ)
    rwa [show (1 : ℝ) - 1 / 12 = 11 / 12 by norm_num] at h
  have hdup : Real.Gamma (5 / 12) * Real.Gamma (11 / 12)
      = Real.Gamma (5 / 6) * dupFactor (5 / 12) := by
    have h := Gamma_mul_Gamma_add_half' (5 / 12 : ℝ)
    rwa [show (5 : ℝ) / 12 + 1 / 2 = 11 / 12 by norm_num,
      show (2 : ℝ) * (5 / 12) = 5 / 6 by norm_num] at h
  have hsq : PConstructible (Real.Gamma (1 / 12) ^ 2) := by
    have key : Real.Gamma (1 / 12) ^ 2
        = Real.Gamma (1 / 12) * Real.Gamma (5 / 12)
            * (Real.Gamma (1 / 12) * Real.Gamma (11 / 12))
            / (Real.Gamma (5 / 12) * Real.Gamma (11 / 12)) := by
      field_simp
    rw [key, hrefl, hdup]
    exact PConstructible.div
      (PConstructible.mul Gamma_one_twelfth_mul_five_twelfths_Pconstructible
        (PConstructible.div pi_Pconstructible
          (sin_Pconstructible
            (PConstructible.mul pi_Pconstructible
              (ratval_Pconstructible (1 / 12) (by norm_num))))))
      (PConstructible.mul Gamma_five_sixths_Pconstructible
        (dupFactor_Pconstructible (ratval_Pconstructible (5 / 12) (by norm_num))))
  have h := sqrt_Pconstructible hsq
  rwa [Real.sqrt_sq hpos.le] at h

-- Theorem: `Γ(5/12)` follows, dividing the triplication product by `Γ(1/12)`.
theorem Gamma_five_twelfths_Pconstructible : PConstructible (Real.Gamma (5 / 12)) := by
  have hpos : 0 < Real.Gamma (1 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have key : Real.Gamma (5 / 12)
      = Real.Gamma (1 / 12) * Real.Gamma (5 / 12) / Real.Gamma (1 / 12) := by
    field_simp
  rw [key]
  exact PConstructible.div Gamma_one_twelfth_mul_five_twelfths_Pconstructible
    Gamma_one_twelfth_Pconstructible

-- Theorem: `Γ(7/12)`, by reflection from `Γ(5/12)`.
theorem Gamma_seven_twelfths_Pconstructible : PConstructible (Real.Gamma (7 / 12)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (5 / 12) (by norm_num))
    Gamma_five_twelfths_Pconstructible
  rwa [show (1 : ℝ) - 5 / 12 = 7 / 12 by norm_num] at this

-- Theorem: `Γ(11/12)`, by reflection from `Γ(1/12)`.
theorem Gamma_eleven_twelfths_Pconstructible : PConstructible (Real.Gamma (11 / 12)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 12) (by norm_num))
    Gamma_one_twelfth_Pconstructible
  rwa [show (1 : ℝ) - 1 / 12 = 11 / 12 by norm_num] at this

-- Theorem: `Γ(n/12)` is P-constructible for every integer `n`. Denominator `12` is now an
-- unconditional family, and with it every denominator dividing `12`.
theorem Gamma_intCast_div_twelve_Pconstructible
    (n : ℤ) : PConstructible (Real.Gamma ((n : ℝ) / 12)) := by
  rw [show ((n : ℝ)) / 12 = (n : ℝ) / ((12 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 0 by norm_num, Real.Gamma_zero]
    exact zero_Pconstructible
  · rw [show ((1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 1 / 12 by norm_num]
    exact Gamma_one_twelfth_Pconstructible
  · rw [show ((2 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 1 / 6 by norm_num]
    exact Gamma_one_sixth_Pconstructible
  · rw [show ((3 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 1 / 4 by norm_num]
    exact Gamma_one_quarter_Pconstructible
  · rw [show ((4 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 1 / 3 by norm_num]
    exact Gamma_one_third_Pconstructible
  · rw [show ((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 5 / 12 by norm_num]
    exact Gamma_five_twelfths_Pconstructible
  · rw [show ((6 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 1 / 2 by norm_num]
    exact Gamma_one_half_Pconstructible
  · rw [show ((7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 7 / 12 by norm_num]
    exact Gamma_seven_twelfths_Pconstructible
  · rw [show ((8 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 2 / 3 by norm_num]
    exact Gamma_two_thirds_Pconstructible
  · rw [show ((9 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 3 / 4 by norm_num]
    exact Gamma_three_quarters_Pconstructible
  · rw [show ((10 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 5 / 6 by norm_num]
    exact Gamma_five_sixths_Pconstructible
  · rw [show ((11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) = 11 / 12 by norm_num]
    exact Gamma_eleven_twelfths_Pconstructible

/-! ### `Γ(1/24)`, from the level-24 substitution

`Pptc.Level24` evaluates the singular value at `N = 3/2` — the modulus at which
`K'/K = √(3/2)` — by an explicit degree-12 algebraic substitution, and reads off

`Γ(1/24)/Γ(13/24) + (√3+√6) Γ(5/24)/Γ(17/24) + (3+√6) Γ(7/24)/Γ(19/24)
    + cot(π/24) Γ(11/24)/Γ(23/24) = 12/(ρ √π) · F(κ, π)`

whose right-hand side is P-constructible.  Duplication turns each `Γ(p)/Γ(p+1/2)` into
`Γ(p)²` over a denominator of level `12`, so the left-hand side is `Γ(1/24)²` times a
P-constructible factor once the three ratios below are in hand.

Why a new input was needed at all, with denominators `8` and `12` already there: consider
the twist `Γ(a/24) ↦ t ^ χ(a) · Γ(a/24)`, where `χ` is the quadratic character of
discriminant `-24` (`+1` on `1, 5, 7, 11` and `-1` on `13, 17, 19, 23`). It fixes `π`,
every algebraic number, and every `Γ(a/n)` with `n ∣ 12` or `n ∣ 8`, and it preserves
reflection and every Gauss multiplication relation at level `24`, since `χ` sums to zero
over each of the relevant residue sets — `{1, 13}` for duplication, `{1, 9, 17}` for
triplication, `{1, 7, 13, 19}` for `k = 4`. No combination of the functional equations can
therefore pin down `Γ(1/24)`: they fix the three ratios below and nothing more. The
substitution supplies exactly the missing `χ`-weighted quantity.

Level `24` is where the method stops. Every character of `(ℤ/24)ˣ` is quadratic — `24` is
the largest modulus for which that is true — so all four odd characters mod `24` belong to
imaginary quadratic fields (`ℚ(i)`, `ℚ(√-2)`, `ℚ(√-3)`, `ℚ(√-6)`), and each has a CM
period. Mod `5` the odd characters have order `4`, no imaginary quadratic field has
conductor `5`, and the method gives nothing. -/

/-! #### The three ratios the functional equations do reach

Each is a quotient of two known products in which the unknown `Γ(13/24)` or `Γ(17/24)`
cancels: duplication supplies the numerator, reflection the denominator. Together they
determine `Γ(5/24)`, `Γ(7/24)` and `Γ(11/24)` from `Γ(1/24)`. -/

-- Theorem: `Γ(1/24) / Γ(11/24)` is P-constructible. Duplication at `s = 1/24` gives
-- `Γ(1/24) Γ(13/24) = Γ(1/12) · dupFactor (1/24)`; reflection at `11/24` gives
-- `Γ(11/24) Γ(13/24)`; the quotient is the ratio.
theorem Gamma_one_div_eleven_twentyfourths_Pconstructible :
    PConstructible (Real.Gamma (1 / 24) / Real.Gamma (11 / 24)) := by
  have h11 : (0 : ℝ) < Real.Gamma (11 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have h13 : (0 : ℝ) < Real.Gamma (13 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have hdup : Real.Gamma (1 / 24) * Real.Gamma (13 / 24)
      = Real.Gamma (1 / 12) * dupFactor (1 / 24) := by
    have h := Gamma_mul_Gamma_add_half' (1 / 24 : ℝ)
    rwa [show (1 : ℝ) / 24 + 1 / 2 = 13 / 24 by norm_num,
      show (2 : ℝ) * (1 / 24) = 1 / 12 by norm_num] at h
  have hrefl : Real.Gamma (11 / 24) * Real.Gamma (13 / 24)
      = Real.pi / Real.sin (Real.pi * (11 / 24)) := by
    have h := Real.Gamma_mul_Gamma_one_sub (11 / 24 : ℝ)
    rwa [show (1 : ℝ) - 11 / 24 = 13 / 24 by norm_num] at h
  have key : Real.Gamma (1 / 24) / Real.Gamma (11 / 24)
      = Real.Gamma (1 / 24) * Real.Gamma (13 / 24)
          / (Real.Gamma (11 / 24) * Real.Gamma (13 / 24)) := by
    field_simp
  rw [key, hdup, hrefl]
  exact PConstructible.div
    (PConstructible.mul Gamma_one_twelfth_Pconstructible
      (dupFactor_Pconstructible (ratval_Pconstructible (1 / 24) (by norm_num))))
    (PConstructible.div pi_Pconstructible
      (sin_Pconstructible
        (PConstructible.mul pi_Pconstructible
          (ratval_Pconstructible (11 / 24) (by norm_num)))))

-- Theorem: `Γ(5/24) / Γ(7/24)` is P-constructible, by the same argument one step over:
-- duplication at `s = 5/24` against reflection at `7/24`, with `Γ(17/24)` cancelling.
theorem Gamma_five_div_seven_twentyfourths_Pconstructible :
    PConstructible (Real.Gamma (5 / 24) / Real.Gamma (7 / 24)) := by
  have h7 : (0 : ℝ) < Real.Gamma (7 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have h17 : (0 : ℝ) < Real.Gamma (17 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have hdup : Real.Gamma (5 / 24) * Real.Gamma (17 / 24)
      = Real.Gamma (5 / 12) * dupFactor (5 / 24) := by
    have h := Gamma_mul_Gamma_add_half' (5 / 24 : ℝ)
    rwa [show (5 : ℝ) / 24 + 1 / 2 = 17 / 24 by norm_num,
      show (2 : ℝ) * (5 / 24) = 5 / 12 by norm_num] at h
  have hrefl : Real.Gamma (7 / 24) * Real.Gamma (17 / 24)
      = Real.pi / Real.sin (Real.pi * (7 / 24)) := by
    have h := Real.Gamma_mul_Gamma_one_sub (7 / 24 : ℝ)
    rwa [show (1 : ℝ) - 7 / 24 = 17 / 24 by norm_num] at h
  have key : Real.Gamma (5 / 24) / Real.Gamma (7 / 24)
      = Real.Gamma (5 / 24) * Real.Gamma (17 / 24)
          / (Real.Gamma (7 / 24) * Real.Gamma (17 / 24)) := by
    field_simp
  rw [key, hdup, hrefl]
  exact PConstructible.div
    (PConstructible.mul Gamma_five_twelfths_Pconstructible
      (dupFactor_Pconstructible (ratval_Pconstructible (5 / 24) (by norm_num))))
    (PConstructible.div pi_Pconstructible
      (sin_Pconstructible
        (PConstructible.mul pi_Pconstructible
          (ratval_Pconstructible (7 / 24) (by norm_num)))))

-- Theorem: `Γ(1/24) / Γ(7/24)` is P-constructible. Here it is triplication at `s = 1/24`
-- that supplies the numerator — `Γ(1/24) Γ(3/8) Γ(17/24) = 2 π 3 ^ (3/8) Γ(1/8)`, whose
-- right-hand side is unconditional — again against reflection at `7/24`.
theorem Gamma_one_div_seven_twentyfourths_Pconstructible :
    PConstructible (Real.Gamma (1 / 24) / Real.Gamma (7 / 24)) := by
  have h7 : (0 : ℝ) < Real.Gamma (7 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have h17 : (0 : ℝ) < Real.Gamma (17 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have h38 : (0 : ℝ) < Real.Gamma (3 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have htrip : Real.Gamma (1 / 24) * Real.Gamma (3 / 8) * Real.Gamma (17 / 24)
      = 2 * Real.pi * (3 : ℝ) ^ ((3 : ℝ) / 8) * Real.Gamma (1 / 8) := by
    have h := Gamma_mul_Gamma_add_third_mul_Gamma_add_two_thirds (1 / 24 : ℝ)
    rwa [show (1 : ℝ) / 24 + 1 / 3 = 3 / 8 by norm_num,
      show (1 : ℝ) / 24 + 2 / 3 = 17 / 24 by norm_num,
      show (3 : ℝ) * (1 / 24) = 1 / 8 by norm_num,
      show (1 : ℝ) / 2 - 1 / 8 = (3 : ℝ) / 8 by norm_num] at h
  have hrefl : Real.Gamma (7 / 24) * Real.Gamma (17 / 24)
      = Real.pi / Real.sin (Real.pi * (7 / 24)) := by
    have h := Real.Gamma_mul_Gamma_one_sub (7 / 24 : ℝ)
    rwa [show (1 : ℝ) - 7 / 24 = 17 / 24 by norm_num] at h
  have key : Real.Gamma (1 / 24) / Real.Gamma (7 / 24)
      = Real.Gamma (1 / 24) * Real.Gamma (3 / 8) * Real.Gamma (17 / 24)
          / (Real.Gamma (3 / 8) * (Real.Gamma (7 / 24) * Real.Gamma (17 / 24))) := by
    field_simp
  rw [key, htrip, hrefl]
  exact PConstructible.div
    (PConstructible.mul
      (PConstructible.mul (PConstructible.mul two_Pconstructible pi_Pconstructible)
        (rpow_Pconstructible three_Pconstructible
          (ratval_Pconstructible (3 / 8) (by norm_num)) (by norm_num)))
      Gamma_one_eighth_Pconstructible)
    (PConstructible.mul Gamma_three_eighths_Pconstructible
      (PConstructible.div pi_Pconstructible
        (sin_Pconstructible
          (PConstructible.mul pi_Pconstructible
            (ratval_Pconstructible (7 / 24) (by norm_num))))))

/-! #### `Γ(1/24)` and the rest of the residues -/

-- Theorem: `Γ(1/24)` is P-constructible. Duplication turns each ratio `Γ(p)/Γ(p + 1/2)`
-- of `Pconstructible.lvGamma_key` into `Γ(p) ^ 2` over a level-`12` denominator; the three
-- ratios above convert `Γ(5/24), Γ(7/24), Γ(11/24)` into `Γ(1/24)`, so the whole left-hand
-- side is `Γ(1/24) ^ 2` times a P-constructible positive factor.
theorem Gamma_one_twentyfourth_Pconstructible : PConstructible (Real.Gamma (1 / 24)) := by
  have h1 : (0 : ℝ) < Real.Gamma (1 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have h5 : (0 : ℝ) < Real.Gamma (5 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have h7 : (0 : ℝ) < Real.Gamma (7 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have h11 : (0 : ℝ) < Real.Gamma (11 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have g12 : (0 : ℝ) < Real.Gamma (1 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have g512 : (0 : ℝ) < Real.Gamma (5 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have g712 : (0 : ℝ) < Real.Gamma (7 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have g1112 : (0 : ℝ) < Real.Gamma (11 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have hd : ∀ s : ℝ, 0 < dupFactor s := fun s => by
    simp only [dupFactor]
    positivity
  have d1 : Real.Gamma (1 / 24) * Real.Gamma (13 / 24)
      = Real.Gamma (1 / 12) * dupFactor (1 / 24) := by
    have h := Gamma_mul_Gamma_add_half' (1 / 24 : ℝ)
    rwa [show (1 : ℝ) / 24 + 1 / 2 = 13 / 24 by norm_num,
      show (2 : ℝ) * (1 / 24) = 1 / 12 by norm_num] at h
  have d5 : Real.Gamma (5 / 24) * Real.Gamma (17 / 24)
      = Real.Gamma (5 / 12) * dupFactor (5 / 24) := by
    have h := Gamma_mul_Gamma_add_half' (5 / 24 : ℝ)
    rwa [show (5 : ℝ) / 24 + 1 / 2 = 17 / 24 by norm_num,
      show (2 : ℝ) * (5 / 24) = 5 / 12 by norm_num] at h
  have d7 : Real.Gamma (7 / 24) * Real.Gamma (19 / 24)
      = Real.Gamma (7 / 12) * dupFactor (7 / 24) := by
    have h := Gamma_mul_Gamma_add_half' (7 / 24 : ℝ)
    rwa [show (7 : ℝ) / 24 + 1 / 2 = 19 / 24 by norm_num,
      show (2 : ℝ) * (7 / 24) = 7 / 12 by norm_num] at h
  have d11 : Real.Gamma (11 / 24) * Real.Gamma (23 / 24)
      = Real.Gamma (11 / 12) * dupFactor (11 / 24) := by
    have h := Gamma_mul_Gamma_add_half' (11 / 24 : ℝ)
    rwa [show (11 : ℝ) / 24 + 1 / 2 = 23 / 24 by norm_num,
      show (2 : ℝ) * (11 / 24) = 11 / 12 by norm_num] at h
  have q5 : PConstructible (Real.Gamma (5 / 24) / Real.Gamma (1 / 24)) := by
    have e : Real.Gamma (5 / 24) / Real.Gamma (1 / 24)
        = Real.Gamma (5 / 24) / Real.Gamma (7 / 24)
            / (Real.Gamma (1 / 24) / Real.Gamma (7 / 24)) := by
      field_simp
    rw [e]
    exact PConstructible.div Gamma_five_div_seven_twentyfourths_Pconstructible
      Gamma_one_div_seven_twentyfourths_Pconstructible
  have q7 : PConstructible (Real.Gamma (7 / 24) / Real.Gamma (1 / 24)) := by
    have e : Real.Gamma (7 / 24) / Real.Gamma (1 / 24)
        = 1 / (Real.Gamma (1 / 24) / Real.Gamma (7 / 24)) := by field_simp
    rw [e]
    exact PConstructible.div PConstructible.base_one
      Gamma_one_div_seven_twentyfourths_Pconstructible
  have q11 : PConstructible (Real.Gamma (11 / 24) / Real.Gamma (1 / 24)) := by
    have e : Real.Gamma (11 / 24) / Real.Gamma (1 / 24)
        = 1 / (Real.Gamma (1 / 24) / Real.Gamma (11 / 24)) := by field_simp
    rw [e]
    exact PConstructible.div PConstructible.base_one
      Gamma_one_div_eleven_twentyfourths_Pconstructible
  have hr2 : PConstructible (Real.sqrt 2) :=
    sqrt_Pconstructible (ratval_Pconstructible 2 (by norm_num))
  have hr3 : PConstructible (Real.sqrt 3) :=
    sqrt_Pconstructible (ratval_Pconstructible 3 (by norm_num))
  have hAP : PConstructible (Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3) :=
    PConstructible.add hr3 (PConstructible.mul hr2 hr3)
  have hBP : PConstructible (3 + Real.sqrt 2 * Real.sqrt 3) :=
    PConstructible.add (ratval_Pconstructible 3 (by norm_num)) (PConstructible.mul hr2 hr3)
  have hCP : PConstructible Pconstructible.lvCot := by
    rw [Pconstructible.lvCot]
    exact PConstructible.add (PConstructible.add (PConstructible.add
      (ratval_Pconstructible 2 (by norm_num)) hr2) hr3) (PConstructible.mul hr2 hr3)
  have hApos : (0 : ℝ) < Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3 := Pconstructible.lv_a_pos
  have hBpos : (0 : ℝ) < 3 + Real.sqrt 2 * Real.sqrt 3 := Pconstructible.lv_b_pos
  have hCpos : (0 : ℝ) < Pconstructible.lvCot := Pconstructible.lvCot_pos
  have hbeta : PConstructible (1 / (Real.Gamma (1 / 12) * dupFactor (1 / 24))
      + (Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3)
          * (Real.Gamma (5 / 24) / Real.Gamma (1 / 24)) ^ 2
          / (Real.Gamma (5 / 12) * dupFactor (5 / 24))
      + (3 + Real.sqrt 2 * Real.sqrt 3) * (Real.Gamma (7 / 24) / Real.Gamma (1 / 24)) ^ 2
          / (Real.Gamma (7 / 12) * dupFactor (7 / 24))
      + Pconstructible.lvCot * (Real.Gamma (11 / 24) / Real.Gamma (1 / 24)) ^ 2
          / (Real.Gamma (11 / 12) * dupFactor (11 / 24))) :=
    PConstructible.add (PConstructible.add (PConstructible.add
      (PConstructible.div PConstructible.base_one
        (PConstructible.mul Gamma_one_twelfth_Pconstructible
          (dupFactor_Pconstructible (ratval_Pconstructible (1 / 24) (by norm_num)))))
      (PConstructible.div (PConstructible.mul hAP (sq_Pconstructible q5))
        (PConstructible.mul Gamma_five_twelfths_Pconstructible
          (dupFactor_Pconstructible (ratval_Pconstructible (5 / 24) (by norm_num))))))
      (PConstructible.div (PConstructible.mul hBP (sq_Pconstructible q7))
        (PConstructible.mul Gamma_seven_twelfths_Pconstructible
          (dupFactor_Pconstructible (ratval_Pconstructible (7 / 24) (by norm_num))))))
      (PConstructible.div (PConstructible.mul hCP (sq_Pconstructible q11))
        (PConstructible.mul Gamma_eleven_twelfths_Pconstructible
          (dupFactor_Pconstructible (ratval_Pconstructible (11 / 24) (by norm_num)))))
  have hbpos : (0 : ℝ) < 1 / (Real.Gamma (1 / 12) * dupFactor (1 / 24))
      + (Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3)
          * (Real.Gamma (5 / 24) / Real.Gamma (1 / 24)) ^ 2
          / (Real.Gamma (5 / 12) * dupFactor (5 / 24))
      + (3 + Real.sqrt 2 * Real.sqrt 3) * (Real.Gamma (7 / 24) / Real.Gamma (1 / 24)) ^ 2
          / (Real.Gamma (7 / 12) * dupFactor (7 / 24))
      + Pconstructible.lvCot * (Real.Gamma (11 / 24) / Real.Gamma (1 / 24)) ^ 2
          / (Real.Gamma (11 / 12) * dupFactor (11 / 24)) := by
    have e1 := hd (1 / 24)
    have e5 := hd (5 / 24)
    have e7 := hd (7 / 24)
    have e11 := hd (11 / 24)
    positivity
  have hkey := Pconstructible.lvGamma_key
  have g13 : (0 : ℝ) < Real.Gamma (13 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have g17 : (0 : ℝ) < Real.Gamma (17 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have g19 : (0 : ℝ) < Real.Gamma (19 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have g23 : (0 : ℝ) < Real.Gamma (23 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have hsum : Real.Gamma (1 / 24) / Real.Gamma (13 / 24)
      + (Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3) * (Real.Gamma (5 / 24) / Real.Gamma (17 / 24))
      + (3 + Real.sqrt 2 * Real.sqrt 3) * (Real.Gamma (7 / 24) / Real.Gamma (19 / 24))
      + Pconstructible.lvCot * (Real.Gamma (11 / 24) / Real.Gamma (23 / 24))
      = Real.Gamma (1 / 24) ^ 2 * (1 / (Real.Gamma (1 / 12) * dupFactor (1 / 24))
        + (Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3)
            * (Real.Gamma (5 / 24) / Real.Gamma (1 / 24)) ^ 2
            / (Real.Gamma (5 / 12) * dupFactor (5 / 24))
        + (3 + Real.sqrt 2 * Real.sqrt 3) * (Real.Gamma (7 / 24) / Real.Gamma (1 / 24)) ^ 2
            / (Real.Gamma (7 / 12) * dupFactor (7 / 24))
        + Pconstructible.lvCot * (Real.Gamma (11 / 24) / Real.Gamma (1 / 24)) ^ 2
            / (Real.Gamma (11 / 12) * dupFactor (11 / 24))) := by
    rw [← d1, ← d5, ← d7, ← d11]
    field_simp
    try ring
  rw [hsum] at hkey
  have hR : PConstructible (12 / (Pconstructible.lvRho * Real.sqrt Real.pi)
      * ellipticF Pconstructible.lvPar Real.pi) := by
    have hnegA : PConstructible (-Pconstructible.lvA) := by
      rw [Pconstructible.lvA, neg_neg]
      exact PConstructible.add (PConstructible.add (PConstructible.add
        (ratval_Pconstructible 9 (by norm_num))
        (PConstructible.mul (ratval_Pconstructible 6 (by norm_num)) hr2))
        (PConstructible.mul (ratval_Pconstructible 6 (by norm_num)) hr3))
        (PConstructible.mul (ratval_Pconstructible 4 (by norm_num))
          (PConstructible.mul hr2 hr3))
    have hrho : PConstructible Pconstructible.lvRho := by
      rw [Pconstructible.lvRho]
      exact PConstructible.div (sqrt_Pconstructible hnegA)
        (PConstructible.mul (ratval_Pconstructible 2 (by norm_num)) hCP)
    have hpar : PConstructible Pconstructible.lvPar := by
      rw [Pconstructible.lvPar]
      exact PConstructible.sub (PConstructible.add (PConstructible.add
        (neg_Pconstructible (ratval_Pconstructible 34 (by norm_num)))
        (PConstructible.mul (ratval_Pconstructible 24 (by norm_num)) hr2))
        (PConstructible.mul (ratval_Pconstructible 20 (by norm_num)) hr3))
        (PConstructible.mul (ratval_Pconstructible 14 (by norm_num))
          (PConstructible.mul hr2 hr3))
    exact PConstructible.mul
      (PConstructible.div (ratval_Pconstructible 12 (by norm_num))
        (PConstructible.mul hrho sqrt_pi_Pconstructible))
      (ellipticF_Pconstructible hpar pi_Pconstructible Pconstructible.lvPar_lt_one)
  have hsq : PConstructible (Real.Gamma (1 / 24) ^ 2) := by
    have e : Real.Gamma (1 / 24) ^ 2
        = 12 / (Pconstructible.lvRho * Real.sqrt Real.pi)
            * ellipticF Pconstructible.lvPar Real.pi
          / (1 / (Real.Gamma (1 / 12) * dupFactor (1 / 24))
            + (Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3)
                * (Real.Gamma (5 / 24) / Real.Gamma (1 / 24)) ^ 2
                / (Real.Gamma (5 / 12) * dupFactor (5 / 24))
            + (3 + Real.sqrt 2 * Real.sqrt 3) * (Real.Gamma (7 / 24) / Real.Gamma (1 / 24)) ^ 2
                / (Real.Gamma (7 / 12) * dupFactor (7 / 24))
            + Pconstructible.lvCot * (Real.Gamma (11 / 24) / Real.Gamma (1 / 24)) ^ 2
                / (Real.Gamma (11 / 12) * dupFactor (11 / 24))) := by
      rw [eq_div_iff hbpos.ne']
      exact hkey
    rw [e]
    exact PConstructible.div hR hbeta
  have h := sqrt_Pconstructible hsq
  rwa [Real.sqrt_sq h1.le] at h

-- Theorem: `Γ(7/24)`, by dividing `Γ(1/24)` by the ratio `Γ(1/24) / Γ(7/24)`.
theorem Gamma_seven_twentyfourths_Pconstructible : PConstructible (Real.Gamma (7 / 24)) := by
  have h1 : (0 : ℝ) < Real.Gamma (1 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have h7 : (0 : ℝ) < Real.Gamma (7 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have key : Real.Gamma (7 / 24)
      = Real.Gamma (1 / 24) / (Real.Gamma (1 / 24) / Real.Gamma (7 / 24)) := by
    field_simp
  rw [key]
  exact PConstructible.div Gamma_one_twentyfourth_Pconstructible
    Gamma_one_div_seven_twentyfourths_Pconstructible

-- Theorem: `Γ(5/24)`, by multiplying `Γ(7/24)` by the ratio `Γ(5/24) / Γ(7/24)`.
theorem Gamma_five_twentyfourths_Pconstructible : PConstructible (Real.Gamma (5 / 24)) := by
  have h7 : (0 : ℝ) < Real.Gamma (7 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have key : Real.Gamma (5 / 24)
      = Real.Gamma (7 / 24) * (Real.Gamma (5 / 24) / Real.Gamma (7 / 24)) := by
    field_simp
  rw [key]
  exact PConstructible.mul Gamma_seven_twentyfourths_Pconstructible
    Gamma_five_div_seven_twentyfourths_Pconstructible

-- Theorem: `Γ(11/24)`, by dividing `Γ(1/24)` by the ratio `Γ(1/24) / Γ(11/24)`.
theorem Gamma_eleven_twentyfourths_Pconstructible : PConstructible (Real.Gamma (11 / 24)) := by
  have h1 : (0 : ℝ) < Real.Gamma (1 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have h11 : (0 : ℝ) < Real.Gamma (11 / 24) := Real.Gamma_pos_of_pos (by norm_num)
  have key : Real.Gamma (11 / 24)
      = Real.Gamma (1 / 24) / (Real.Gamma (1 / 24) / Real.Gamma (11 / 24)) := by
    field_simp
  rw [key]
  exact PConstructible.div Gamma_one_twentyfourth_Pconstructible
    Gamma_one_div_eleven_twentyfourths_Pconstructible

-- Theorem: `Γ(13/24)`, by reflection from `Γ(11/24)`.
theorem Gamma_thirteen_twentyfourths_Pconstructible :
    PConstructible (Real.Gamma (13 / 24)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (11 / 24) (by norm_num))
    Gamma_eleven_twentyfourths_Pconstructible
  rwa [show (1 : ℝ) - 11 / 24 = 13 / 24 by norm_num] at this

-- Theorem: `Γ(17/24)`, by reflection from `Γ(7/24)`.
theorem Gamma_seventeen_twentyfourths_Pconstructible :
    PConstructible (Real.Gamma (17 / 24)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (7 / 24) (by norm_num))
    Gamma_seven_twentyfourths_Pconstructible
  rwa [show (1 : ℝ) - 7 / 24 = 17 / 24 by norm_num] at this

-- Theorem: `Γ(19/24)`, by reflection from `Γ(5/24)`.
theorem Gamma_nineteen_twentyfourths_Pconstructible :
    PConstructible (Real.Gamma (19 / 24)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (5 / 24) (by norm_num))
    Gamma_five_twentyfourths_Pconstructible
  rwa [show (1 : ℝ) - 5 / 24 = 19 / 24 by norm_num] at this

-- Theorem: `Γ(23/24)`, by reflection from `Γ(1/24)`.
theorem Gamma_twentythree_twentyfourths_Pconstructible :
    PConstructible (Real.Gamma (23 / 24)) := by
  have := Gamma_one_sub_Pconstructible (ratval_Pconstructible (1 / 24) (by norm_num))
    Gamma_one_twentyfourth_Pconstructible
  rwa [show (1 : ℝ) - 1 / 24 = 23 / 24 by norm_num] at this

-- Theorem: `Γ(n/24)` is P-constructible for every integer `n`. The eight residues coprime
-- to `24` are the new work above; the sixteen others reduce to denominator `12` (the even
-- ones) or denominator `8` (the odd multiples of `3`), both already unconditional.
theorem Gamma_intCast_div_twentyfour_Pconstructible
    (n : ℤ) : PConstructible (Real.Gamma ((n : ℝ) / 24)) := by
  rw [show ((n : ℝ)) / 24 = (n : ℝ) / ((24 : ℕ) : ℝ) by norm_num]
  refine Gamma_intCast_div_Pconstructible (by norm_num) (fun r hr => ?_) n
  interval_cases r
  · rw [show ((0 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((0 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 0
  · rw [show ((1 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = 1 / 24 by norm_num]
    exact Gamma_one_twentyfourth_Pconstructible
  · rw [show ((2 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((1 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 1
  · rw [show ((3 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((1 : ℤ) : ℝ) / 8 by norm_num]
    exact Gamma_intCast_div_eight_Pconstructible 1
  · rw [show ((4 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((2 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 2
  · rw [show ((5 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = 5 / 24 by norm_num]
    exact Gamma_five_twentyfourths_Pconstructible
  · rw [show ((6 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((3 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 3
  · rw [show ((7 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = 7 / 24 by norm_num]
    exact Gamma_seven_twentyfourths_Pconstructible
  · rw [show ((8 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((4 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 4
  · rw [show ((9 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((3 : ℤ) : ℝ) / 8 by norm_num]
    exact Gamma_intCast_div_eight_Pconstructible 3
  · rw [show ((10 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((5 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 5
  · rw [show ((11 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = 11 / 24 by norm_num]
    exact Gamma_eleven_twentyfourths_Pconstructible
  · rw [show ((12 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((6 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 6
  · rw [show ((13 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = 13 / 24 by norm_num]
    exact Gamma_thirteen_twentyfourths_Pconstructible
  · rw [show ((14 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((7 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 7
  · rw [show ((15 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((5 : ℤ) : ℝ) / 8 by norm_num]
    exact Gamma_intCast_div_eight_Pconstructible 5
  · rw [show ((16 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((8 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 8
  · rw [show ((17 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = 17 / 24 by norm_num]
    exact Gamma_seventeen_twentyfourths_Pconstructible
  · rw [show ((18 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((9 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 9
  · rw [show ((19 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = 19 / 24 by norm_num]
    exact Gamma_nineteen_twentyfourths_Pconstructible
  · rw [show ((20 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((10 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 10
  · rw [show ((21 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((7 : ℤ) : ℝ) / 8 by norm_num]
    exact Gamma_intCast_div_eight_Pconstructible 7
  · rw [show ((22 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = ((11 : ℤ) : ℝ) / 12 by norm_num]
    exact Gamma_intCast_div_twelve_Pconstructible 11
  · rw [show ((23 : ℕ) : ℝ) / ((24 : ℕ) : ℝ) = 23 / 24 by norm_num]
    exact Gamma_twentythree_twentyfourths_Pconstructible

end Pconstructible
