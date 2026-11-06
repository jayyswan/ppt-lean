# HANDOFF: rank-4 Hasse–Minkowski port (`Pptc/HasseMinkowski/RankFour.lean`)

Goal: `isotropic_of_rank_four (Q : QuadraticForm ℚ V) [FiniteDimensional ℚ V]
(hr : finrank ℚ V = 4) (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) : Isotropic Q`
in new file `Pptc/HasseMinkowski/RankFour.lean`, namespace `Pptc.HasseMinkowski`.

Plan: port WiN7 `QuadraticForm/RankFour.lean` blueprint, restructured to avoid
`hasseMinkowskiInv` well-definedness (use `hasseMinkowskiInvAux`-level diagonal criteria).
Consume `Targets.isotropic_of_rank_three` (sorry stub). Trailing hypotheses expected:
2-adic Hilbert bilinearity + the two-prescribed Hilbert-symbol existence theorem.

Log:
- Created log; surveyed Targets/Prod/RankCriteria/HasseInvariant/Locally/Reciprocity/Existence.
