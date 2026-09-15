# HANDOFF: WP5 HighRank.lean toolkit

Goal: rewrite `Pptc/HasseMinkowski/HighRank.lean` as WP5 toolkit.
- WP5.1: `isotropic_weightedSumSquares_three_units`, `isotropic_of_three_units`
- WP5.2: `isSquare_div_of_close_real`, `isSquare_div_of_close_padic`, `exists_rat_close_vec`

Target file: `Pptc/HasseMinkowski/HighRank.lean`, namespace `Pptc.HasseMinkowski.HighRank`.

Plan: read Plan-v3 WP4/WP5 + reference files, then build up.

## Log
- read plan/reference files next
- Read Plan-v3 WP4/WP5, RankCriteria outline, Local.lean. Next: Padic.lean, Squares, RatApproximation.
- Read Squares.lean (`isSquare_of_dist_one_lt_one`, `..._pow`), RatApproximation (`approximation'`, `norm_sub_le`). `hilbertSym_padicInt_units` at Padic.lean:172.
- NOTE: stated `isotropic_of_three_units` with `w : ι → ℚ_[p]` and `IsUnit (w (u j))` is mathematically FALSE (IsUnit in a field = nonzero; ⟨1,1,1⟩ anisotropic over ℚ_2). Will deliver integral-unit version.
- NOTE2: stated `isSquare_div_of_close_padic` FALSE for p=2 (a₀=1,a=2: ‖1‖<1 but 2 not square). Will split odd/even: odd with given hyp, p=2 with `< 2^-2`.
- `Real.isSquare_iff` in Mathlib.Data.Real.Sqrt. Legendre outline timed out; skip. Next: write draft.
- Wrote full draft of HighRank.lean (5 declarations). Next: diagnostics.
- First diagnostics: 7 errors. Fixed: deprecated import -> Mathlib.Analysis.Real.Sqrt; norm rewrite; Ne.symm; `Padic.isSquare_of_dist_one_lt_one (p:=p)`; `(-u2)*u0` shape; TYPE ERROR in task: `ℚ_[p] ^ (Fin 2)` must be `Fin 2 → ℚ_[p]`. Re-diagnosing.
- Second diagnostics: 2 errors (`Finset.single_le_sum` needs explicit `f :=`). Fixed. Now success:true, no diagnostics.
- Added `isotropic_of_three_units_int` (integral weights, literal `IsUnit`). Still clean.
- Next: lake_check final.
- `lake_check` attempt 1+2: "failed to read ...Vandermonde.olean.private"; attempt 3: INTERNAL PANIC: out of memory. attempt 4/5: "failed to read ...olean.private" (toolchain / Jacobson). OOM/IO symptoms under memory pressure (a sibling subagent's lean worker held 2 GB). LSP diagnostics (warm) = success, zero diagnostics; `lean_verify` gives {propext, Classical.choice, Quot.sound}.
- `lake_check` FINAL (after sibling worker freed memory): "OK - no errors or warnings." DONE.

## Final declarations (all in `Pptc.HasseMinkowski`, file compiles clean)
- L42  `isotropic_weightedSumSquares_three_units` (exactly as requested)
- L71  `isotropic_of_three_units` (w : ι → ℚ_[p], ∃ unit witness)
- L126 `isotropic_of_three_units_int` (w : ι → ℤ_[p], literal `IsUnit`)
- L136 `isSquare_div_of_close_real` (exactly as requested)
- L154 `isSquare_div_of_close_padic` (odd p; added `hp : p ≠ 2`)
- L165 `isSquare_div_of_close_padic_two` (p=2, threshold 2⁻²)
- L174 `local instance factPrimeOfPrimesHighRank`
- L183 `exists_rat_close_vec` (`Fin 2 → ℚ_[p]`, not the invalid `^`)

## Statement adjustments (all forced; see summary)
- `IsUnit (w (u j))` for `w : ι → ℚ_[p]` is `w (u j) ≠ 0` (field), and the claim is FALSE
  (⟨1,1,1⟩ is anisotropic over ℚ_2). Replaced by an explicit `ℤ_[p]ˣ` witness; added the
  integral-weight variant for the literal `IsUnit` form.
- `isSquare_div_of_close_padic` is FALSE for p = 2 (a₀=1, a=2); split off the p=2 case with
  `‖a-a₀‖ < 2⁻²‖a₀‖`.
- `ℚ_[p] ^ (Fin 2)` does not typecheck (no `HPow Type Type`); used `Fin 2 → ℚ_[p]`.
