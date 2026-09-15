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
- WP2.5 + WP2.4 appended (section Prescribed). Key: even_valuation_of_isSquare /
  not_isSquare_of_odd_valuation; exists_nonsquare_unit (odd: lifted non-residue; p=2: 7);
  2.5 picks c₂=p when v(c) even, c₂=unit-nonsquare when v(c) odd. 2.4 by explicit case
  analysis on the signs s=(y,c₂), t=(w,c₁) using y,w,z from hnd. Diagnostics clean.
- DONE WP2.4+2.5. lake_check Local.lean: OK, no errors or warnings. lean_verify both: clean.
  Lines: even_valuation_of_isSquare 449, not_isSquare_of_odd_valuation 456,
  exists_nonsquare_unit 461, exists_not_isSquare_and_not_isSquare_mul 540,
  exists_hilbertSym_two_prescribed 561.

## WP2.6 (five-variable isotropy)

- NOTE: the requested `represents_weightedSumSquares_three_iff` (`represents x ↔
  ¬IsSquare(-(b₁b₂b₃)x)`) is FALSE: over ℚ_3, ⟨1,1,1⟩ is isotropic (hilbertSym(-1)(-1)=1,
  case00) hence represents x=-1, but -(1·1·1)·(-1)=1 is a square. Delivering instead:
  (i) `wss2_val`, `wss3_val`, `nondegenerate_wss3`, and the implication
  `represents_three_of_not_isSquare` (condition → represents), which is what the proof needs.
- `wss5_val`, `isotropic_weightedSumSquares_five` and `isotropic_weightedSumSquares_of_five_le`
  now compile with `lean_diagnostic_messages` clean (no warnings).
  Five-var route: c1 = -(w0w1); square → explicit isotropic vector; else WP2.5 gives c2,
  WP2.4 gives x with (x,c1)=(w0,w1) and (x,c2) = -(w2w3w4,c2); then x·w2w3w4 is nonsquare,
  so Piece-A implication gives ⟨-w2,-w3,-w4⟩ rep x; combine the two representations into a
  Fin 5 vector. Corollary restricts via an injection Fin 5 ↪ ι and `Function.extend`-style
  extension by zero.
- DONE WP2.6. lake_check Local.lean: OK, no errors or warnings; lean_verify both clean.
  Lines: wss2_val 652, wss3_val 657, nondegenerate_wss3 663,
  represents_three_of_not_isSquare 675, wss5_val 771, isotropic_weightedSumSquares_five 777,
  isotropic_weightedSumSquares_of_five_le 860.
  NOTE on the requested `represents_weightedSumSquares_three_iff` (`↔ ¬IsSquare(-(b₁b₂b₃)x)`):
  it is FALSE (counterexample over ℚ_3: ⟨1,1,1⟩ is isotropic because hilbertSym(-1)(-1)=1,
  so it represents x = -1, but -1·1·1·(-1) = 1 is a square).  Delivered the true implication
  `represents_three_of_not_isSquare` instead; it is exactly what WP2.6 needs.
