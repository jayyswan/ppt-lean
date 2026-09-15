import Pptc.HasseMinkowski.Targets

/-!
# Rank-4 Hasse–Minkowski over ℚ (port of WiN7 `QuadraticForm/RankFour.lean`)

Blueprint (`Scratch/win7-reference.md`).  A nondegenerate rank-4 form `Q` over ℚ that is
locally isotropic everywhere restricts, via a rational vector with prescribed local
behaviour (weak approximation, `RatApproximation.lean`), to a rank-3/2 subform, and the
Hilbert-symbol forcing of the local data `a, b` (Existence.lean) yields an isotropic
rank-2 pair `⟪a, b⟫ * ⟪-1, -abc r⟫`.  The preceding document describes the schematical
outline deeper; READ `Scratch/win7-reference.md` FIRST for the exact upstream shape of
`QuadraticForm/RankFour.lean` (it was fully proved upstream).
-/

open Module

namespace Pptc.HasseMinkowski

namespace RankFour

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-! ### Skeleton — implement -/

-- Theorem: rank 4 Hasse–Minkowski over ℚ.
theorem isotropic_of_rank_four (Q : QuadraticForm ℚ V) [FiniteDimensional ℚ V]
    (hr : finrank ℚ V = 4) (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) :
    Isotropic Q := by
  sorry

end RankFour

end Pptc.HasseMinkowski
