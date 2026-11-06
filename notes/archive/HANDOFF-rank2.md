# HANDOFF: rank-one/two Hasse–Minkowski

Target file: `pptc/Pptc/HasseMinkowski/RankTwo.lean`, namespace `Pptc.HasseMinkowski`.

Goal:
```lean
lemma isotropic_of_rank_one {V} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)
    (hr : Module.finrank ℚ V = 1) (hQ' : EverywhereLocallyIsotropic Q) : Isotropic Q
lemma isotropic_of_rank_two {V} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)
    [Module.Finite ℚ V] (hr : Module.finrank ℚ V = 2) (hQ : Q.Nondegenerate)
    (hQ' : EverywhereLocallyIsotropic Q) : Isotropic Q
```

Plan: read Basic.lean/Locally.lean/RatSquares.lean, adapt WiN7 rank-2 proof.

## Log
- [start] created log, reading deps.
