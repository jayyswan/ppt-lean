/-
Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/

import Pptc.Solvable.AbelRuffini
import Pptc.Solvable.Roots
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.Algebra.Polynomial.Splits

/-! # The converse Abel–Ruffini theorem

This file proves the converse direction of Abel–Ruffini over `ℂ`: a complex
algebraic number whose minimal polynomial has solvable Galois group lies in the
radical closure of `ℚ`.  The forward direction is Mathlib's
`isSolvable_gal_minpoly`.  Consequently, every real algebraic number with
solvable Galois group is constructible by straightedge and compass.

The mathematical input is the paper source `X1` §2.2 and §4: complex radicals
are free in the P-constructible world because `cos`, `sin`, `arccos`, and
`rpow` are already P-constructible operations.
-/

namespace Pconstructible

open Polynomial

noncomputable section

/-- A complex root of a nonzero polynomial with solvable Galois group is
P-constructible. -/
theorem root_PConstructibleC_of_solvable_gal {z : ℂ} {q : ℚ[X]}
    (hq : q ≠ 0) (h : Group.IsSolvable q.Gal) (hz : aeval z q = 0) :
    PConstructibleC z := by
  have hz_alg : IsAlgebraic ℚ z := ⟨q, hq, hz⟩
  have hp_dvd : minpoly ℚ z ∣ q := minpoly.dvd ℚ z hz
  have hsplit : (minpoly ℚ z).map (algebraMap ℚ q.SplittingField) |>.Splits :=
    Splits.of_dvd (Polynomial.SplittingField.splits (f := q))
      (Polynomial.map_ne_zero hq)
      (Polynomial.map_dvd (algebraMap ℚ q.SplittingField) hp_dvd)
  have hmin_solv : Group.IsSolvable (minpoly ℚ z).Gal :=
    gal_isSolvable_of_splits (p := minpoly ℚ z) (q := q) ⟨hsplit⟩ h
  exact PConstructibleC.of_mem_PComplex
    (mem_PComplex_of_mem_solvableByRad (mem_solvableByRad_of_isSolvable_gal hz_alg hmin_solv))

/-- A real root of a nonzero polynomial with solvable Galois group is
P-constructible. -/
theorem root_Pconstructible_of_solvable_gal {α : ℝ} {q : ℚ[X]}
    (hq : q ≠ 0) (h : Group.IsSolvable q.Gal) (hα : aeval α q = 0) :
    PConstructible α := by
  have hαC : aeval (α : ℂ) q = 0 := by
    change aeval (algebraMap ℝ ℂ α) q = 0
    rw [Polynomial.aeval_algebraMap_apply]
    simp [hα]
  have hz := root_PConstructibleC_of_solvable_gal (z := (α : ℂ)) hq h hαC
  simpa using hz.1

end

end Pconstructible
