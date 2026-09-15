/-
Copyright (c) 2026 Pptc contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/
import Pptc.HasseMinkowski.Locally

/-!
# SCRATCH: inter-layer contracts for Hasse–Minkowski (all `sorry`)

These are the `sorry`-stubbed statements of the results that the layers above depend on.
They exist so that parallel workers can develop downstream results *before* the upstream
proofs land: e.g. the rank-4 proof may `import Pptc.HasseMinkowski.Targets` and use
`Targets.isotropic_of_rank_three`, while a separate worker supplies the real rank-3 proof.

Nothing here is part of the final development. As real proofs land, downstream files are
repointed from `Targets.X` to the proved `Pptc.HasseMinkowski.X`, and this file shrinks
until it is deleted. Do **not** import this from any completed layer.
-/

open Module QuadraticMap

namespace Pptc.HasseMinkowski

namespace Targets

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

-- Theorem (rank 1): locally-everywhere-isotropic rank-1 forms over ℚ are isotropic.
theorem isotropic_of_rank_one (Q : QuadraticForm ℚ V) (hr : finrank ℚ V = 1)
    (hQ' : EverywhereLocallyIsotropic Q) : Isotropic Q := sorry

-- Theorem (rank 2): nondegenerate rank-2 Hasse–Minkowski over ℚ.
theorem isotropic_of_rank_two (Q : QuadraticForm ℚ V) [FiniteDimensional ℚ V]
    (hr : finrank ℚ V = 2) (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) :
    Isotropic Q := sorry

-- Theorem (rank 3, ternary/Legendre): nondegenerate rank-3 Hasse–Minkowski over ℚ.
theorem isotropic_of_rank_three (Q : QuadraticForm ℚ V) [FiniteDimensional ℚ V]
    (hr : finrank ℚ V = 3) (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) :
    Isotropic Q := sorry

-- Theorem (rank 4): nondegenerate rank-4 Hasse–Minkowski over ℚ (via rank 3).
theorem isotropic_of_rank_four (Q : QuadraticForm ℚ V) [FiniteDimensional ℚ V]
    (hr : finrank ℚ V = 4) (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) :
    Isotropic Q := sorry

-- Theorem (rank >= 5, Meyer): nondegenerate high-rank Hasse–Minkowski over ℚ.
theorem isotropic_of_five_le_rank (Q : QuadraticForm ℚ V) [FiniteDimensional ℚ V]
    (hr : 5 ≤ finrank ℚ V) (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) :
    Isotropic Q := sorry

-- Theorem (Hasse–Minkowski over ℚ, isotropy form).
theorem hasseMinkowski (Q : QuadraticForm ℚ V) [FiniteDimensional ℚ V] :
    Isotropic Q ↔ EverywhereLocallyIsotropic Q := sorry

-- Corollary (Meyer): an indefinite form over ℚ in >= 5 variables is isotropic.
theorem meyer (Q : QuadraticForm ℚ V) [FiniteDimensional ℚ V] (h : 5 ≤ finrank ℚ V)
    (hind : Indefinite (QuadraticForm.baseChange ℝ Q)) : Isotropic Q := sorry

end Targets

end Pptc.HasseMinkowski
