# HANDOFF: HasseMinkowski/HasseInvariant.lean

## Goal (Lean syntax)
```lean
noncomputable def hasseMinkowskiInvAux {k : Type*} [Field k] {n : ℕ} (w : Fin n → kˣ) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2 : k)

noncomputable def hasseMinkowskiInv {k} [Field k] {V} [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) (hQ : LinearMap.SeparatingLeft Q.associated) : ℤ :=
  hasseMinkowskiInvAux (equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose
```

Targets (priority order):
1. small-n computational lemmas
2. `hasseMinkowskiInvAux_eq_one_or_neg_one`, `hasseMinkowskiInvAux_prod_rank_one`
3. `hasseMinkowskiInv_of_baseChange_weightedSumSquares`
4. Well-definedness `eq_of_equivalent` — likely out of reach, document omission.

## Plan
- Read WiN7 reference + local signature dump.
- Inspect our API (HilbertSymbol/Defs, Real, Basic, Locally, Prod).
- Write file incrementally, lake_check.

## Progress log
- (start) created log.
- Read WiN7 ref, Defs.lean, Real.lean, Basic.lean, Locally.lean, Prod.lean, RankTwo.lean.
- `equivalent_weightedSumSquares_units_of_nondegenerate'` found in Mathlib IsometryEquiv.lean.
- Wrote HasseInvariant.lean: defs + zero/one/two/three + eq_one_or_neg_one.
- lake_check: OK, no errors or warnings.
- Now attempting Aux-level `prod_rank_one`.
- SUCCESS: proved `hasseMinkowskiInvAux_cons` (prepend weight) via
  `Finset.prod_filter` + `Fintype.prod_prod_type` + `Fin.prod_univ_succ`.
- SUCCESS: proved `hasseMinkowskiInvAux_prod_rank_one` ([HasBilinHilbertSym k]) by collapsing the
  product with a MonoidHom `b ↦ hilbertSym a b` (`map_prod`).
- Final lake_check: OK - no errors or warnings. lean_verify: axioms only propext/Classical.choice/Quot.sound.

## Declarations proved (all in Pptc.HasseMinkowski)
- `hasseMinkowskiInvAux` (def)
- `hasseMinkowskiInvAux_def`
- `hasseMinkowskiInvAux_zero`
- `hasseMinkowskiInvAux_one`
- `hasseMinkowskiInvAux_two`
- `hasseMinkowskiInvAux_three`
- `hilbertSym_eq_one_or_neg_one_of_ne_zero`
- `hasseMinkowskiInvAux_eq_one_or_neg_one`
- `hasseMinkowskiInvAux_cons` (Aux-level rank-one decomposition)
- `hasseMinkowskiInvAux_prod_rank_one` (collapsed form, needs `[HasBilinHilbertSym k]`)
- `hasseMinkowskiInv` (def)

## Dropped (documented, not stated)
- `hasseMinkowskiInvAux.eq_of_equivalent` (well-definedness; needs local-field Hilbert symbol theory)
- `hasseMinkowskiInv.weightedSumSquares`, `_two`, `_three` (depend on the above)
- `hasseMinkowskiInv.eq_one_or_neg_one` (depend on the above)
- `hasseMinkowskiInv.of_baseChange_weightedSumSquares` (depend on the above)
- `hasseMinkowskiInv.prod_rank_one` (depend on the above; Aux-level analogue proved instead)

Note: `hasseMinkowskiInv` itself is defined but has no proved theorem about it, because every such
theorem needs well-definedness (`eq_of_equivalent`), which is explicitly out of scope.

Result: WORKS. File: Pptc/HasseMinkowski/HasseInvariant.lean
