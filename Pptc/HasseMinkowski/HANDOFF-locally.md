# HANDOFF: Layer 2 — Locally.lean + RankTwo.lean

Goal: two new files, no `sorry`, compile with `lake_check`.

A) `Pptc/HasseMinkowski/Locally.lean`, namespace `Pptc.HasseMinkowski`:
```lean
def EverywhereLocallyIsotropic (Q : QuadraticForm ℚ V) : Prop :=
  (∀ (p : ℕ) [Fact (Nat.Prime p)], (Q.baseChange ℚ_[p]).Isotropic) ∧
    (Q.baseChange ℝ).Isotropic
```
plus `Isotropic Q → Q.EverywhereLocallyIsotropic`, and base-change helpers
`baseChange_weightedSumSquares`, `baseChange_prod`.

B) `Pptc/HasseMinkowski/RankTwo.lean`: rank 0/1/2 cases of Hasse–Minkowski,
helpers `coeff_ratio_isSquare_of_represents_zero`, `comp_ne_zero_of_nondegenerate`,
and the `Equivalent.represents_iff` transfer if missing.

## Log
- (start) created log. Read Basic.lean + RatSquares.lean + Plan + handoffs.
- (A) `baseChange_weightedSumSquares` PROVED. Recon of `baseChange`, `TensorProduct.piScalarRight`,
  `Module.FaithfullyFlat.one_tmul_eq_zero_iff` done. Fetched WiN7 Rat.lean verbatim.
- (A) `isotropic_baseChange`, `EverywhereLocallyIsotropic`, `isotropic_everywhereLocallyIsotropic`
  written but needed two fixes.
- (A) RESCUED (main agent): added `import Mathlib.Algebra.CharP.Invertible`, fixed
  `fun _ _ =>` to `fun p _ =>`, dropped unused `[DecidableEq ι]` + added `classical`.
  `lake_check Pptc/HasseMinkowski/Locally.lean` -> OK, no errors or warnings. olean built.
- (B) NOT STARTED. Next: RankTwo.lean (see prompt below).

## (B) RankTwo.lean — DONE
- `Pptc/HasseMinkowski/RankTwo.lean` created, namespace `Pptc.HasseMinkowski`.
- `lake_check Pptc/HasseMinkowski/RankTwo.lean` => exit 0 (warnings only, no errors, **no sorry**).
- `lean_verify` on both main lemmas => axioms `propext, Classical.choice, Quot.sound`.
- Declarations:
  * `QuadraticMap.Equivalent.represents_iff` (support lemma, proved from `IsometryEquiv.map_app`).
  * `Pptc.HasseMinkowski.isotropic_of_rank_one : (Q : QuadraticForm ℚ V) → finrank ℚ V = 1 →
      EverywhereLocallyIsotropic Q → Isotropic Q`.
    Proof: real isotropy + `finrank_baseChange` give `Q.baseChange ℝ = 0` (rank-one
    `isotropic_iff_zero_of_rank_one`); evaluate at `1 ⊗ m`, `baseChange_tmul`, `Rat.cast_eq_zero`.
  * `Pptc.HasseMinkowski.isotropic_of_rank_two : (Q : QuadraticForm ℚ V) → [Module.Finite ℚ V] →
      finrank ℚ V = 2 → Q.Nondegenerate → EverywhereLocallyIsotropic Q → Isotropic Q`.
    Proof: WiN7 adaptation. Reindex `equivalent_weightedSumSquares_units_of_nondegenerate'`
    (`Fin (finrank) → Fin 2` by `revert`+`rw [hr]`; `exact fun w hw => ⟨w, hw⟩` because the
    Units action is definitionally the ℚ action). Real isotropy ⇒ `0 ≤ -w₀⁻¹w₁`; each p-adic
    local isotropy ⇒ even `padicValRat`; conclude via `isSquare_of_nonneg_of_even_padicValRat`
    and the vector `![x, 1]`.
- Private helpers: `coeff_ratio_isSquare_of_represents_zero`, `comp_ne_zero_of_nondegenerate`.
- Note: WiN7's `comp_ne_zero_of_nondegenerate` argument order was changed to
  `(hw0) (hw1) (hx) (h)` and the ratio lemma to the ℚ-valued-weight form `w : Fin 2 → ℚ` with
  explicit nonzeroness, differing from the literal prompt snippet (which had inconsistent
  argument order and `Units`-valued `w`). Mathematically identical.
- Deviation: `equivalent_weightedSumSquares_units_of_nondegenerate'` in Mathlib 4.33 already
  returns `Fin (finrank K V) → Kˣ`, so no `n`-indexed wrapper was needed; the `Fin`-reindex is
  done inline in the proof. The import `Mathlib.LinearAlgebra.Dimension.Constructions` supplies
  `Module.finrank_baseChange`; `Mathlib.Analysis.Real.Sqrt` supplies `Real.isSquare_iff`;
  `open TensorProduct` is required for the `⊗[ℚ]` notation.


