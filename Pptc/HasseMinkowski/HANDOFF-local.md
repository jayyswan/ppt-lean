# HANDOFF — WP2.1 / WP2.2 HilbertSymbol/Local.lean

Goal 2.1: `instance instHasBilinHilbertSymPadic (p : ℕ) [Fact p.Prime] : HasBilinHilbertSym ℚ_[p]`
Goal 2.2: `represents_weightedSumSquares_two_iff {k} [Field k] [HasBilinHilbertSym k]
  [Invertible (2:k)] {a b x} (ha hb hx) : (weightedSumSquares k ![a,b]).represents x ↔
  hilbertSym x (-(a*b)) = hilbertSym a b`

Plan: by_cases p=2; p=2 uses Two's instance; p≠2 uses hilbertSym_padic_odd_mul_left.

- [start] read Plan-v3 §WP2 and Defs.lean.
- 2.1 written in Local.lean; `lean_diagnostic_messages` = clean (no diamond). Instance name
  `instHasBilinHilbertSymPadic`.
- 2.2: found bridge `weightedSumSquares_two_represents_iff_ternary` in FROZEN
  RankCriteriaGeneral.lean (private, cannot import). Will reproduce it in Local.lean.
  Rank-3 criterion + hilbertSym_mul_mul + mul_eq_one_iff_eq_of_signs are in RankCriteria.lean.
- Need `open Module QuadraticMap` for `weightedSumSquares` (added).
- Both 2.1 (line 30) and 2.2 (line 122) now compile; lean_diagnostic_messages = clean, no warnings.
  Proof state at end of 2.2 is closed.
- DONE. `lake_check` on Pptc/HasseMinkowski/HilbertSymbol/Local.lean: OK, no errors or warnings.
  lean_verify represents_weightedSumSquares_two_iff: {propext, Classical.choice, Quot.sound}.
  2.1 `instHasBilinHilbertSymPadic` line 30; 2.2 `represents_weightedSumSquares_two_iff` line 122.
