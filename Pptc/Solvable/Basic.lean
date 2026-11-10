/-
Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/

import Pptc.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IntermediateField.Basic

/-! # P-constructible complex numbers

`PConstructible` is a predicate on `ℝ`.  This file packages it componentwise on `ℂ`:
`PConstructibleC z` means that `z.re` and `z.im` are both `PConstructible`.  The main
point is that this predicate is a subfield of `ℂ`, so it can be compared with Mathlib's
`solvableByRad ℚ ℂ` later.

The field structure is bookkeeping.  The interesting closure property, closure under
complex `n`-th roots, is in `Pptc.Solvable.Roots`; it needs the trigonometric
constructions from `Pptc.Basic`.
-/

namespace Pconstructible

/-- A complex number is P-constructible if both its real and imaginary parts are. -/
def PConstructibleC (z : ℂ) : Prop :=
  PConstructible z.re ∧ PConstructible z.im

namespace PConstructibleC

theorem zero : PConstructibleC 0 := by
  constructor <;> simp [zero_Pconstructible]

theorem one : PConstructibleC 1 := by
  constructor
  · simpa only [Complex.one_re] using (PConstructible.base_one : PConstructible (1 : ℝ))
  · simpa only [Complex.one_im] using zero_Pconstructible

theorem add {z w : ℂ} (hz : PConstructibleC z) (hw : PConstructibleC w) :
    PConstructibleC (z + w) := by
  constructor
  · simpa using PConstructible.add hz.1 hw.1
  · simpa using PConstructible.add hz.2 hw.2

theorem neg {z : ℂ} (hz : PConstructibleC z) : PConstructibleC (-z) := by
  constructor
  · simpa using neg_Pconstructible hz.1
  · simpa using neg_Pconstructible hz.2

theorem sub {z w : ℂ} (hz : PConstructibleC z) (hw : PConstructibleC w) :
    PConstructibleC (z - w) := by
  simpa [sub_eq_add_neg] using add hz (neg hw)

theorem mul {z w : ℂ} (hz : PConstructibleC z) (hw : PConstructibleC w) :
    PConstructibleC (z * w) := by
  constructor
  · have h : PConstructible (z.re * w.re - z.im * w.im) :=
      PConstructible.sub (PConstructible.mul hz.1 hw.1) (PConstructible.mul hz.2 hw.2)
    simpa using h
  · have h : PConstructible (z.re * w.im + z.im * w.re) :=
      PConstructible.add (PConstructible.mul hz.1 hw.2) (PConstructible.mul hz.2 hw.1)
    simpa using h

theorem inv {z : ℂ} (hz : PConstructibleC z) : PConstructibleC z⁻¹ := by
  have hden : PConstructible (z.re ^ 2 + z.im ^ 2) :=
    PConstructible.add (sq_Pconstructible hz.1) (sq_Pconstructible hz.2)
  constructor
  · rw [Complex.inv_re, Complex.normSq_apply, ← sq, ← sq]
    exact PConstructible.div hz.1 hden
  · rw [Complex.inv_im, Complex.normSq_apply, ← sq, ← sq]
    exact PConstructible.div (neg_Pconstructible hz.2) hden

theorem div {z w : ℂ} (hz : PConstructibleC z) (hw : PConstructibleC w) :
    PConstructibleC (z / w) := by
  simpa [div_eq_mul_inv] using mul hz (inv hw)

theorem ofReal {x : ℝ} (hx : PConstructible x) : PConstructibleC (x : ℂ) := by
  constructor
  · simpa using hx
  · simp [zero_Pconstructible]

theorem ofRat (q : ℚ) : PConstructibleC (q : ℂ) :=
  ofReal (rat_Pconstructible q)

end PConstructibleC

/-- The complex numbers with P-constructible coordinates form a subfield of `ℂ`. -/
noncomputable def PComplexField : Subfield ℂ where
  carrier := {z | PConstructibleC z}
  zero_mem' := PConstructibleC.zero
  one_mem' := PConstructibleC.one
  add_mem' := PConstructibleC.add
  neg_mem' := PConstructibleC.neg
  mul_mem' := PConstructibleC.mul
  inv_mem' := fun z hz => PConstructibleC.inv (z := z) hz

/-- The field of P-constructible complex numbers, as an intermediate field of `ℚ → ℂ`. -/
noncomputable def PComplex : IntermediateField ℚ ℂ :=
  PComplexField.toIntermediateField fun q => PConstructibleC.ofRat q

@[simp]
theorem mem_PComplex {z : ℂ} : z ∈ PComplex ↔ PConstructibleC z :=
  Iff.rfl

theorem PConstructibleC.of_mem_PComplex {z : ℂ} (hz : z ∈ PComplex) : PConstructibleC z :=
  mem_PComplex.mp hz

theorem mem_PComplex_of_PConstructibleC {z : ℂ} (hz : PConstructibleC z) : z ∈ PComplex :=
  mem_PComplex.mpr hz

/-- The imaginary unit has P-constructible coordinates. -/
theorem PConstructibleC.I : PConstructibleC Complex.I := by
  constructor <;> simp [zero_Pconstructible, PConstructible.base_one]

end Pconstructible
