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

## WP2.3 (nontriviality of x ↦ (x,c))

- Read Real.lean `hilbertSym_real_eq`, Padic.lean `hilbertSym_padic_odd_eq` (line 863),
  Two.lean `hilbertSym_padic_two_eq` (line 1454). Plan: ℝ via x=-1; odd p via x = nonresidue
  unit when v(c) odd, x = p when v(c) even (needs ¬IsSquare (toZMod (padicUnit c)));
  p=2 via x=5 (v odd), x=-1 (v even, u≢1 mod4), x=2 (v even, u≡5 mod8).
- Will reprove private `coe_padicUnit` as local helper (padicUnit def is public).
- 2.3: ℝ theorem + odd-prime theorem compile; p=2 section (eps/omg witnesses 5,7,2) compiles.
  Final `exists_hilbertSym_eq_neg_one_padic` added. Diagnostics clean so far.
- DONE WP2.3. `lake_check` on Local.lean: OK, no errors or warnings.
  `lean_verify exists_hilbertSym_eq_neg_one_padic`: {propext, Classical.choice, Quot.sound}.
  Lines: exists_hilbertSym_eq_neg_one_real 146; ..._odd (private) 250; ..._two (private) 411;
  ..._padic 436. p=2 witnesses: 5 (v(c) odd), 7 (v(c) even, eps=1), 2 (v(c) even, eps=0).
