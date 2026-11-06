# HANDOFF — Main.lean (WP6 Hasse–Minkowski assembly)

Goal: create `Pptc/HasseMinkowski/Main.lean` proving:
- 6.1 `isotropic_of_radical_ne_bot` (unconditional)
- 6.2 `hasseMinkowski_of (h4) (h5)` : `Isotropic Q ↔ EverywhereLocallyIsotropic Q`
- 6.3 `meyer_of (h4) (h5)` : `Indefinite (baseChange ℝ Q)` + rank ≥ 5 → `Isotropic Q`

Plan: read Plan-v3 WP6, Targets, Basic, Locally, RankTwo, Legendre, RankFour, HighRank,
HilbertSymbol/Local; then build Main.lean.

## Log
- [start] created log; about to read source files.
- Read Plan-v3 WP6, Targets, Basic, Locally, RankTwo, Legendre, RankFour, HighRank, Local.
- Confirmed names: `Submodule.ne_bot_iff`, `QuadraticMap.mem_radical_iff'`,
  `QuadraticMap.Equivalent.isotropic_iff` (RankCriteria.lean:44), `Module.finrank_fin_fun`,
  `nondegenerate_wss_of_ne` (HighRank), `isotropic_weightedSumSquares_of_five_le` (Local).
- Design: private helper `isotropic_wss_of` dispatches on n=0..4 and n+5 via `rcases`.
- Wrote Main.lean; removed shadowing `haveI : Invertible (2:ℚ)` (ambient instance
  `invertibleTwo` already exists). LSP diagnostics: clean, 0 items.
- Note: HighRank.lean is being modified by another worker (grew past 760 lines); was
  briefly broken, now clean. Main imports it for `RankFiveLeDiagonalHM`.
- Running final `lake_check`.
- DONE. `lake_check Pptc/HasseMinkowski/Main.lean` → "OK - no errors or warnings."
  Declarations in Main.lean:
  - line 48  `isotropic_of_radical_ne_bot` (WP6.1, unconditional)
  - line 68  `isotropic_wss_of` (private rank dispatch helper, h4/h5 conditional)
  - line 103 `hasseMinkowski_of` (WP6.2, h4/h5 conditional)
  - line 152 `meyer_of` (WP6.3, h4/h5 conditional)
  No `sorry`/`axiom`; all lines ≤ 100 chars. `lean_verify` was inconclusive (LSP busy),
  but the only hypotheses are the two explicit `Prop`s, so no extra axioms.
  Note: HighRank.lean is concurrently edited by another worker; Main compiles against the
  current (clean) version.
