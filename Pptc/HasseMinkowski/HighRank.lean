import Pptc.HasseMinkowski.Targets

/-!
# Meyer's theorem for rank ≥ 5 over ℚ (port of WiN7 `HighDimensionMeyer`)

Blueprint (`Scratch/win7-reference.md`; upstream `QuadraticForm/HighDimensionMeyer.lean`):
the n → n-1 reduction says that a rank-`n` nondegenerate form over ℚ which is locally
isotropic at every place contains a rank-`(n-1)` nondegenerate subform with the same
property; iterating lands at rank 4, whose Hasse–Minkowski theorem is the contract
`Targets.isotropic_of_rank_four` (sorry stub, to be replaced by `RankFour`).

Design statement first, together with the reading of `Scratch/win7-reference.md`
(upstream has this sorry too, so the mathematical scheme must be engineered here):
weak approximation of ℚ in the local completions (`RatApproximation.lean`) supplies a
rational vector carrying the right local data; the standard reduction of WiN7's
rank-lowering step is the intended Mathematical scheme; May adapt the statement of the
lemma below.  Read `Scratch/win7-reference.md` FIRST for exact upstream shape, and
use that shape only.
-/

open Module

namespace Pptc.HasseMinkowski

namespace HighRank

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-! ### Skeleton — implement -/

-- Theorem: rank ≥ 5 Hasse–Minkowski (Meyer) over ℚ.
theorem isotropic_of_five_le_rank (Q : QuadraticForm ℚ V) [FiniteDimensional ℚ V]
    (hr : 5 ≤ finrank ℚ V) (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) :
    Isotropic Q := by
  sorry

end HighRank

end Pptc.HasseMinkowski
