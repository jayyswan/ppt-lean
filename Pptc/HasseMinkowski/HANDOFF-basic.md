# HANDOFF: Layer 0 Basic.lean (Isotropic / represents / nondegeneracy / base change)

Goal: new file `Pptc/HasseMinkowski/Basic.lean`, namespace `Pptc.HasseMinkowski`,
compiles via `lake_check`, no `sorry`. Items 1-12 of the task spec.

- [start] Recon: dir exists with Plan.md + HANDOFF.md. Need to inspect Mathlib
  `QuadraticMap` / `QuadraticForm` definitions for exact contexts.
- [recon] Confirmed: `QuadraticMap.Anisotropic` ctx [CommSemiring][AddCommMonoid M/N][Module];
  `not_anisotropic_iff_exists`; `Nondegenerate`/`nondegenerate_iff_radical_eq_bot`/
  `radical_eq_ker_polarBilin` in Radical.lean; `prod`/`polar_prod`/`polarBilin_prod`;
  `QuadraticForm.baseChange` in TensorProduct.lean; `LinearEquiv.baseChange` in
  TensorProduct/Tower.lean; `Pi.spanSubset`; `radical_weightedSumSquares`;
  `intermediate_value_Icc`. Dot notation needs the def in the *type's* namespace
  (function-level pred fails); so generic API in Pptc.HasseMinkowski + QuadraticMap aliases.
- [deviation] `represents` defined with nonzero witness (∃ x ≠ 0, Q x = a): necessary for
  `represents_zero_iff_isotropic` / `represents_iff_sub_isotropic` to be true.
  For a≠0 it agrees with the naive `∃ x, Q x = a`.
- [draft] Wrote full Basic.lean (items 1-12). Item 10 named `not_isotropic_of_rank_zero`
  (`isotropic_of_rank_zero` is false: rank zero forms are NOT isotropic).
  Item 11 in `QuadraticMap` namespace for dot notation. Checking compile now.
- [probe] Scratch tests confirmed `Q.TestIsoQ` (QuadraticMap arg) works but function-arg
  pred does not support dot notation; both `Q.IsotropicF`/`Q.IsotropicQ` in wrong ns fail.
- [compile] `lake_check Pptc/HasseMinkowski/Basic.lean` => OK, no errors or warnings.
  `lean_verify Pptc.HasseMinkowski.Indefinite.isotropic` => propext, Classical.choice,
  Quot.sound only. No `sorry`. Scratch deleted.
- [final declarations] Pptc.HasseMinkowski.Isotropic, .IsotropicFn, .represents,
  .isotropic_iff_not_anisotropic, .not_isotropic_iff_anisotropic,
  .represents_zero_iff_isotropic, .represents_iff_sub_isotropic,
  .isotropic_iff_zero_of_rank_one, .nondegenerate_weightedSumSquares,
  .nondegenerate_prod, .nondegenerate_of_anisotropic, .anisotropic_of_rank_zero,
  .not_isotropic_of_rank_zero, .Indefinite, .Indefinite.isotropic;
  QuadraticMap.IsometryEquiv.baseChange, QuadraticMap.Equivalent.baseChange;
  plus dot-notation aliases QuadraticMap.Isotropic / QuadraticMap.represents.
- [deviations] (a) `represents` uses a nonzero witness (needed for items 4/5 to be true;
  for a≠0 equivalent to naive `∃x, Qx=a`). (b) item 10 `isotropic_of_rank_zero` is FALSE
  (rank-0 forms are not isotropic); proved `not_isotropic_of_rank_zero`. (c) item 5 uses
  `IsotropicFn (x ↦ Q x - a)` since that translate is not a quadratic map. (d) item 9
  proved via `mem_radical_iff'` + `nondegenerate_iff_radical_eq_bot` instead of
  `separatingLeft_of_anisotropic` (simpler, same result). (e) item 11 lives in namespace
  `QuadraticMap` for idiomatic dot notation `e.baseChange`. (f) item 8 carries the
  `[Invertible (2:R)]` hypothesis (characteristic 2 is not covered).
