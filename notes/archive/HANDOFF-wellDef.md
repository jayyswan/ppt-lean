# HANDOFF: Hasse–Minkowski invariant well-definedness

Target file: `Pptc/HasseMinkowski/HasseInvariantWellDef.lean` (namespace `Pptc.HasseMinkowski`)

Goal (in order):
1. `LinearMap.separatingLeft_of_equivalent`
   `(h : Q.Equivalent Q') (hQ : LinearMap.SeparatingLeft Q.associated) : LinearMap.SeparatingLeft Q'.associated`
2. `QuadraticForm.hasseMinkowskiInvAux.eq_of_equivalent` — equal invariant for equivalent weighted sums of squares
3. `QuadraticForm.hasseMinkowskiInv.eq_of_equivalent_weightedSumSquares` and `hasseMinkowskiInv.eq_of_equivalent`

Plan:
- Read `Pptc/HasseMinkowski/Scratch/win7-reference.md`, `HasseInvariant.lean`, `Prod.lean`, `RankCriteria.lean`.
- Port WiN7 proof.

## Log
- created handoff
- KEY FINDING: upstream `HasseMinkowskiInvariant.lean` has `sorry` for ALL FOUR targets
  (separatingLeft_of_equivalent, hasseMinkowskiInvAux.eq_of_equivalent,
  hasseMinkowskiInv.eq_of_equivalent_weightedSumSquares, hasseMinkowskiInv.eq_of_equivalent).
  So there is no proof to "port"; item 2 is the honest missing input.
- Local API check: `QuadraticForm.orthoCompl`, `prodOrthoComplEquiv`, Witt cancellation are NOT
  in Mathlib 4.33 nor Pptc. Upstream's own `Chain.lean` (`chainOfNondegenerate`, `exists_const`)
  is itself 2 sorries. So an unconditional item 2 needs that chain development.
- Plan: item 1 full; item 2 conditional on `[HasBilinHilbertSym k]` + `[Invertible (2:k)]` +
  an explicit connectivity hypothesis `hconn` (the Chain.lean content); item 3 derived from item 2.
- Rewrote HANDOFF (this file) at start.
- Writing HasseInvariantWellDef.lean.
- Proved item 1 (`LinearMap.separatingLeft_of_equivalent`) via Nondegenerate transport; compiles.
- Proved `hasseMinkowskiInvAux_comp_equiv` (permutation invariance) via sorted-pair prod_bij; compiles.
- Proved `hilbertSym_prod_eq_of_equivalent` (discr_comp ⇒ discriminant square ⇒ (a,s²)=1).
- Proved `Step` (elementary move), item 2 (`hasseMinkowskiInvAux.eq_of_equivalent`, conditional on
  `hconn`), item 3 (`hasseMinkowskiInv.eq_of_equivalent_weightedSumSquares`, `.eq_of_equivalent`),
  plus `wssCongr` (reindexing isometry) and `hasseMinkowskiInvAux_finCongr`.
- LSP diagnostics: no errors (only 2 harmless `abel` "Try this" infos).

## DECLARATIONS ACTUALLY DELIVERED (all in `Pptc.HasseMinkowski`)
- `LinearMap.separatingLeft_of_equivalent`            -- UNCONDITIONAL
- `hasseMinkowskiInvAux_comp_equiv`                   -- permutation invariance of ε
- `hilbertSym_prod_eq_of_equivalent`                  -- [HasBilinHilbertSym k] [Invertible 2]
- `Step`                                               -- elementary move relation
- `hasseMinkowskiInvAux.eq_of_equivalent`             -- [..] + explicit `hconn` hypothesis
- `wssCongr`, `hasseMinkowskiInvAux_finCongr`          -- reindexing helpers
- `hasseMinkowskiInv.eq_of_equivalent_weightedSumSquares`, `hasseMinkowskiInv.eq_of_equivalent`
  (both from item 2; carry the same `hconn`).

## NOTE ON THE EXPLICIT HYPOTHESIS
`hconn : ∀ {n} (w w' : Fin n → kˣ), (weightedSumSquares k w).Equivalent (weightedSumSquares k w')
  → Relation.ReflTransGen (Step n) w w'`
is a purely *geometric* statement (WiN7 `Chain.lean` / `chainOfNondegenerate`): any two equivalent
diagonalizations are connected by reindexings and by splitting off a common rank-one summand with
equivalent tails.  It contains no invariant-theoretic content, so items 2/3 are genuine
  reductions.  Discharging `hconn` requires porting `Chain.lean` (upstream itself has 2 `sorry`s there).

## FINAL STATUS
- File: `Pptc/HasseMinkowski/HasseInvariantWellDef.lean`, namespace `Pptc.HasseMinkowski`.
- `lean_diagnostic_messages`: SUCCESS, no errors/warnings (only 2 harmless `abel` "Try this" infos).
- `lean_verify hasseMinkowskiInv.eq_of_equivalent`: axioms = {propext, Classical.choice, Quot.sound}.
- No `sorry`/`admit` in the file.
- `lake_check` could NOT be used for final confirmation: every invocation exited 1 with a *toolchain*
  read error naming a different builtin file each time (`UInt.ir`, `UserWidget.olean.private`,
  `Types.olean.private`), all of which exist (verified with `Test-Path`). This is an environmental
  file-locking problem, not a proof error; the warm LSP environment elaborates the file cleanly.
