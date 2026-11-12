/-
Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/

import Pptc.Taylor.Field
import Pptc.Taylor.Lift
import Pptc.Taylor.Statement
import Pptc.Taylor.Engine

/-! # Pptc.Taylor.Main

Entry point for the Taylor ⇒ `R_alg ⊆ P` formalization
(`notes/algebraic/PLAN-taylor-lean.md`).  This module collects tasks **T0–T3** of the
plan and is the file imported by `Pptc.lean`.

## What is proved here

* **T0 (`Pptc.Taylor.Field`).** The P-constructible reals form a subfield `PReal` of `ℝ`;
  the coordinate classes `SolvableReal`, `DegreeLE8Real`, `DegreeLE2Real` and the
  inductive root tower `PTowerReal` are defined, and each of them is shown to consist of
  P-constructible numbers:
  `SolvableReal.Pconstructible`, `DegreeLE8Real.Pconstructible`,
  `DegreeLE2Real.Pconstructible`, `PTowerReal.Pconstructible`.
* **T1 (`Pptc.Taylor.Lift`).** The lift data `TrinomialLift Coord β` of a point on the
  trinomial surface `x ^ D + a * x + b = 0`, and the generic recovery theorem
  `TrinomialLift.Pconstructible`: if every `Coord`-number is P-constructible, then a
  trinomial lift of `β` makes `β` P-constructible.  The recovery uses the minimal
  polynomial of `y₀` over `PReal`: it divides both `q` and `T - x₀`, so every conjugate of
  `y₀` is a root of both, and `hinj` forces the conjugate to be `y₀` itself; separability
  of `q` then makes the minimal polynomial linear.  Hence the hypothesis needs the
  separability of `q` and the distinctness of the conjugates on all complex roots.
* **T2 (`Pptc.Taylor.Statement`).** The hypothesis hierarchy `TaylorTrinomial`, `SR`,
  `SR_tot`, `SR_tower`, `SR_8`, `SR_quad`, `SR_F`, the monotonicity of the lift in the
  coordinate class (`TrinomialLift.mono`), the formal implication diagram
  `SR_quad → SR_8 → SR_tower → P`, `SR → SR_tower → P`, `SR_tot → SR → P`,
  `SR_F → P`, and the conditional main theorem

  ```lean
  theorem realAlgebraic_Pconstructible_of_taylorTrinomial (hTaylor : TaylorTrinomial) :
      ∀ β : ℝ, IsAlgebraic ℚ β → PConstructible β
  ```

  together with its analogues `realAlgebraic_Pconstructible_of_SR`,
  `_of_SR_tower`, `_of_SR_8`, `_of_SR_quad`, `_of_SR_F`.
* **T3 (`Pptc.Taylor.Engine`, optional strengthening).** The paper's geometric engine:
  crossing the power curve `y = x ^ D` with the P-constructible line `y = -(a * x) - b`
  isolates roots of the trinomial `x ^ D + a * x + b`.  Hence
  `trinomial_root_Pconstructible` (with an isolating window) and, because a nondegenerate
  trinomial has finitely many roots, `trinomial_root_pos_Pconstructible`: **a positive
  root of a nondegenerate trinomial with P-constructible coefficients is
  P-constructible, with no degree bound and no isolation hypothesis.**

## What is *not* proved here

* **Taylor's question itself.** `TaylorTrinomial` is a hypothesis, not a theorem: it
  asserts that every real algebraic `β` has a trinomial lift over `SolvableReal`.  The
  main theorem is therefore **conditional** on this point-existence statement; likewise
  each corollary is conditional on the corresponding `SR_*` hypothesis.
* **The geometry of the trinomial surface** (`Pptc/Taylor/Geometry.lean`, task T4) and
  **PSC / weak approximation**: deriving `SR`, `SR_8`, `SR_quad`, `SR_tot` from Taylor's
  PSC conjecture or from a rational-point search (tasks T4/T5/T6) is future work.
* The arrow `SR_F → SR` is deliberately absent: `FReal` only records that a coordinate
  is P-constructible and algebraic, not that it has a *solvable* defining polynomial.

See `notes/algebraic/PLAN-taylor-lean.md` §5 for the full hypothesis table (with the
strength of each row and its Lean status) and §6 for the task breakdown T0–T6.
-/
