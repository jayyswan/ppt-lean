/-
Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/

import Pptc.Basic
import Pptc.Octic.Main
import Pptc.Solvable.Main
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-! # The field of P-constructible reals and the coordinate hypothesis classes

The paper source `X1` reduces the trinomial construction problem to a statement
about the coordinates of a real point: each coordinate should be reachable from
`ℚ` by a tower of roots of low-degree polynomials with P-constructible
coefficients, or should be a real algebraic number with solvable Galois group.

This file records the two purely algebraic ingredients of that reduction.

* `PReal` is the subfield of `ℝ` formed by the P-constructible reals. Packaging
  the closure properties proved in `Pptc.Basic` as a `Subfield` lets later
  arguments work with `PReal[X]` (for instance `Polynomial.gcd` and resultants)
  instead of unpacking `PConstructible` at every step.
* The coordinate predicates `SolvableReal`, `DegreeLE8Real`, `DegreeLE2Real` and
  the inductive `PTowerReal` mirror the hypothesis hierarchy of
  `notes/algebraic/PLAN-taylor-lean.md` §4–5, and each of them is proved to
  imply `PConstructible`. These lemmas turn an arithmetic hypothesis of the form
  "the point is defined over such-and-such a field" into the conclusion
  `PConstructible β` that the recovery argument needs.

Finally `mobius_Pconstructible` records that the Möbius transformation used by
the square-lift step of the plan preserves P-constructibility: Lean's division
is total, so no hypothesis on the denominator is needed.
-/

namespace Pconstructible

open Polynomial

-- The plan mandates the names `PReal.Pconstructible`, `SolvableReal.Pconstructible`, …,
-- whose last component repeats the ambient namespace; that is not a mistake here.
set_option linter.dupNamespace false

noncomputable section

/-! ### The subfield of P-constructible reals -/

/-- The P-constructible real numbers form a subfield of `ℝ`: they contain `0` and
`1` and are closed under addition, multiplication, negation and inversion. -/
def PReal : Subfield ℝ where
  carrier := {x | PConstructible x}
  zero_mem' := zero_Pconstructible
  one_mem' := PConstructible.base_one
  add_mem' := fun hx hy => PConstructible.add hx hy
  mul_mem' := fun hx hy => PConstructible.mul hx hy
  neg_mem' := fun hx => neg_Pconstructible hx
  inv_mem' := fun _ hx => inv_Pconstructible hx

/-- Membership in `PReal` is exactly P-constructibility. -/
@[simp]
theorem mem_PReal {x : ℝ} : x ∈ PReal ↔ PConstructible x := Iff.rfl

/-- A real number that lies in `PReal` is P-constructible. -/
theorem PReal.Pconstructible {x : ℝ} (h : x ∈ PReal) : PConstructible x := h

/-- A P-constructible real number lies in `PReal`. -/
theorem PConstructible.mem_PReal {x : ℝ} (h : PConstructible x) : x ∈ PReal := h

/-- The algebra structure of `ℝ` over its subfield `PReal` is the inclusion map. -/
@[simp]
theorem PReal.coe_algebraMap (x : PReal) : (algebraMap PReal ℝ x : ℝ) = x := rfl

/-! ### Lifting polynomials from a subfield of `ℝ` -/

/-- A real polynomial all of whose coefficients lie in a subfield `K ≤ ℝ` is the
image of a polynomial over `K`. -/
theorem _root_.Subfield.exists_map_eq_of_forall_coeff_mem (K : Subfield ℝ) {p : ℝ[X]}
    (h : ∀ i, p.coeff i ∈ K) : ∃ p' : K[X], p'.map (algebraMap K ℝ) = p := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), C ⟨p.coeff i, h i⟩ * X ^ i, ?_⟩
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
  rfl

/-! ### Coordinate predicates -/

/-- Real algebraic numbers whose defining polynomial has solvable Galois group. -/
def SolvableReal (x : ℝ) : Prop :=
  ∃ q : ℚ[X], q ≠ 0 ∧ Group.IsSolvable q.Gal ∧ aeval x q = 0

/-- Real algebraic numbers of degree at most 8 over `ℚ`. -/
def DegreeLE8Real (x : ℝ) : Prop :=
  ∃ q : ℚ[X], q ≠ 0 ∧ q.natDegree ≤ 8 ∧ aeval x q = 0

/-- Real algebraic numbers of degree at most 2 over `ℚ`. -/
def DegreeLE2Real (x : ℝ) : Prop :=
  ∃ q : ℚ[X], q ≠ 0 ∧ q.natDegree ≤ 2 ∧ aeval x q = 0

/-- Real numbers reachable from `ℚ` by a tower of roots of degree-≤8 polynomials
with `PTowerReal` coefficients, together with solvable real algebraic numbers. -/
inductive PTowerReal : ℝ → Prop
  | rat (q : ℚ) : PTowerReal (q : ℝ)
  | root8 {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 8)
      (hcoeff : ∀ i, PTowerReal (p.coeff i)) {x : ℝ} (hx : p.eval x = 0) : PTowerReal x
  | solvable {q : ℚ[X]} (hq : q ≠ 0) (h : Group.IsSolvable q.Gal)
      {x : ℝ} (hx : aeval x q = 0) : PTowerReal x

/-! ### Each coordinate class consists of P-constructible numbers -/

/-- A real algebraic number with solvable Galois group is P-constructible. -/
theorem SolvableReal.Pconstructible {x : ℝ} (h : SolvableReal x) : PConstructible x := by
  obtain ⟨q, hq, hsol, hx⟩ := h
  exact root_Pconstructible_of_solvable_gal hq hsol hx

/-- A real algebraic number of degree at most 8 over `ℚ` is P-constructible. -/
theorem DegreeLE8Real.Pconstructible {x : ℝ} (h : DegreeLE8Real x) : PConstructible x := by
  obtain ⟨q, hq, hdeg, hx⟩ := h
  have hq' : q.map (algebraMap ℚ ℝ) ≠ 0 := Polynomial.map_ne_zero hq
  have hdeg' : (q.map (algebraMap ℚ ℝ)).natDegree ≤ 8 :=
    (Polynomial.natDegree_map_le).trans hdeg
  have hcoef : ∀ k, PConstructible ((q.map (algebraMap ℚ ℝ)).coeff k) := by
    intro k
    rw [Polynomial.coeff_map]
    exact rat_Pconstructible (q.coeff k)
  have hx' : (q.map (algebraMap ℚ ℝ)).eval x = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]
    exact hx
  exact root_Pconstructible_deg8_coeffs hq' hdeg' hcoef hx'

/-- A real algebraic number of degree at most 2 over `ℚ` is P-constructible. -/
theorem DegreeLE2Real.Pconstructible {x : ℝ} (h : DegreeLE2Real x) : PConstructible x := by
  obtain ⟨q, hq, hdeg, hx⟩ := h
  exact DegreeLE8Real.Pconstructible ⟨q, hq, by omega, hx⟩

/-- A real number in a tower of degree-≤8 roots with `PTowerReal` coefficients,
possibly topped off by a solvable algebraic number, is P-constructible. -/
theorem PTowerReal.Pconstructible {x : ℝ} (h : PTowerReal x) : PConstructible x := by
  induction h with
  | rat q => exact rat_Pconstructible q
  | root8 hp hdeg hcoeff hx ih => exact root_Pconstructible_deg8_coeffs hp hdeg ih hx
  | solvable hq hsol hx => exact root_Pconstructible_of_solvable_gal hq hsol hx

/-! ### Möbius transformations -/

/-- A Möbius transformation with P-constructible coefficients preserves
P-constructibility. No hypothesis on the denominator is needed, because division
in `ℝ` is total. -/
theorem mobius_Pconstructible {a b c d x : ℝ} (hx : PConstructible x)
    (ha : PConstructible a) (hb : PConstructible b) (hc : PConstructible c)
    (hd : PConstructible d) : PConstructible ((a * x + b) / (c * x + d)) := by
  exact PConstructible.div (PConstructible.add (PConstructible.mul ha hx) hb)
    (PConstructible.add (PConstructible.mul hc hx) hd)

end

end Pconstructible
