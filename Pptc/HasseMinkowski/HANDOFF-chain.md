# HANDOFF: Chain.lean (hconn discharge)

Goal: discharge `hconn` in `hasseMinkowskiInvAux.eq_of_equivalent` by creating
`Pptc/HasseMinkowski/Chain.lean`, namespace `Pptc.HasseMinkowski`, importing
`Pptc.HasseMinkowski.HasseInvariantWellDef`. No `sorry`. No other file edits.

Plan:
1. Read `HasseInvariantWellDef.lean` to extract exact `hconn` type.
2. Read `HANDOFF-wellDef.md`, `Basic.lean`, `Prod.lean`, `RankCriteria.lean`, `HasseInvariant.lean`.
3. Port sorry-free part of upstream Chain.lean; state residual precisely if needed.
4. Deliver `hconn` theorem, then unconditional `eq_of_equivalent` corollaries.
5. `lake_check` once at end.

- [step 0] created this log.
- [step 1] Read `HasseInvariantWellDef.lean`. Exact `hconn` (lines 236-238, 293-295, 307-309,
  338-340):
  `hconn : ∀ {n : ℕ} (w w' : Fin n → kˣ), (weightedSumSquares k w).Equivalent
     (weightedSumSquares k w') → Relation.ReflTransGen (Step n) w w'`
  under `[Invertible (2:k)] [HasBilinHilbertSym k]`. `Step` (line 217) = permutation OR
  `u = cons a w ∧ v = cons a w'` with `w ~ w'`.
- [step 2] KEY FINDING: upstream WiN7 `Chain.lean` is 2 `sorry` (definitions `IsContiguous`,
  `Chain` are the only sorry-free part); upstream `HasseMinkowskiInvariant.lean`'s
  `eq_of_equivalent` is ALSO `sorry`. So nothing to port for the proof.
- [step 3] **`hconn` IS FALSE.** Counterexample at rank 1 over ℝ (instance
  `HasBilinHilbertSym ℝ` exists in `HilbertSymbol/Real.lean`): `w = ![1]`, `w' = ![4]`.
  `weightedSumSquares ℝ ![(1)] ~ weightedSumSquares ℝ ![(4)]` (scale by 1/2, using
  `weightedSumSquares_mul_squares_equivalent`). But `Step 1 u v → u = v` (permutation only id;
  cons keeps the single entry), so `ReflTransGen (Step 1) w w' → w = w'`, yet `1 ≠ 4`.
  Consequence: `hconn` cannot be discharged / is not a theorem; no diagonal-only `Step`
  relation can be complete (general isometries mix coordinates). The genuine residual is the
  basis-level `chainOfNondegenerate`.
- [step 5] Wrote `Pptc/HasseMinkowski/Chain.lean`; `lean_diagnostic_messages`: SUCCESS, no
  errors/warnings. Contents:

  * `Module.Basis.IsContiguous`, `Module.Basis.Chain` (ported WiN7; contiguity field corrected
    from upstream's vacuous `⟨i⟩,⟨i⟩` to the intended consecutive `⟨i⟩,⟨i+1⟩`, documented).
  * `Pptc.HasseMinkowski.DiagonalConnectivity k` := exact `hconn` shape.
  * `Pptc.HasseMinkowski.ChainHypothesis k` := named residual (`Nonempty (Chain Q b b')` for
    dim ≥ 3 nondegenerate) — the genuine missing piece.
  * `step_one_eq`, `reflTransGen_step_one_eq`, `diagonalConnectivity_false : ¬ DiagonalConnectivity ℝ`.
- [step 6] Final `lake_check` next.
- [step 6] `lake_check Pptc/HasseMinkowski/Chain.lean` → `OK - no errors or warnings`.
  `lean_verify diagonalConnectivity_false` → axioms `{propext, Classical.choice, Quot.sound}`
  (no `sorry`/`admit`/`axiom` in the file).

## FINAL STATUS / DECLARATIONS (namespace split, file `Pptc/HasseMinkowski/Chain.lean`)
- `Module.Basis.IsContiguous`                       -- ported WiN7, sorry-free
- `Module.Basis.Chain`                              -- ported WiN7, sorry-free
- `Pptc.HasseMinkowski.DiagonalConnectivity (k)`    -- exact `hconn` shape
- `Pptc.HasseMinkowski.ChainHypothesis (k)`         -- named genuine residual
- `Pptc.HasseMinkowski.step_one_eq`                 -- `Step 1 u v → u = v`
- `Pptc.HasseMinkowski.reflTransGen_step_one_eq`    -- `ReflTransGen (Step 1) u v → u = v`
- `Pptc.HasseMinkowski.diagonalConnectivity_false`  -- `¬ DiagonalConnectivity ℝ` (refutes `hconn`)

## OUTCOME
Deliverable (1) is IMPOSSIBLE as literally requested: `hconn` is false (rank-1, ℝ counterexample;
`1` vs `4`, equivalent but `Step 1` only relates equal tuples). Hence `hconn` does not follow from
the Chain development and `hasseMinkowskiInvAux.eq_of_equivalent` cannot be made unconditional by
this route. Deliverable (2) is therefore not attempted. The exact missing geometric input is now
named `ChainHypothesis` (WiN7 `chainOfNondegenerate`: connectivity of orthogonal bases with
consecutive contiguity), which upstream proves only with two `sorry`s; no axiom was introduced.
NOTE: upstream `Chain`'s `basis_isContiguous` uses the same index `⟨i,_⟩` on both sides (vacuous);
ported here with the intended consecutive `⟨i,_⟩`, `⟨i+1,_⟩` and documented.

--- 

# WORKSTREAM B.4 (first lemma): port WiN7 `Module.Basis.exists_const`

Target file: `Pptc/HasseMinkowski/BasisChain.lean` (append).
Goal (verbatim from WiN7 `QuadraticForm/Chain.lean`):
`exists_const (hdim : 3 ≤ finrank k V) (hQ : Q.Nondegenerate) {b b' : Basis (Fin (finrank k V)) k V}
  (hb : Q.associated.IsOrthoᵢ b) (hb' : Q.associated.IsOrthoᵢ b') (h1 : ...) (h2 : ...) :
  ∃ x, Q (b' 1 + x • b' 2) ≠ 0 ∧ (Q.restrict (span {b 1, b' 1 + x • b' 2})).Nondegenerate`
- [step 0] PLAN: read `Restriction.lean`/`Witt.lean` API; decide on statement adaptions
  (likely need `[Infinite k]`, `Q.associated.IsOrthoᵢ` etc.); build x via polynomial argument.
- [step 0] confirmed no import cycle: `Witt` -> `Restriction`, neither imports `BasisChain`.
- [step 5] `lean_diagnostic_messages Pptc/HasseMinkowski/BasisChain.lean` -> SUCCESS, no errors/warnings.
  Declarations added: `Module.Basis.exists_const` (verbatim WiN7 statement, uses
  `Pptc.HasseMinkowski.restrict`). NO adaptation needed: statement is provable as written, no
  `[Infinite k]` needed. Key facts: `h1`/`h2` plus nondegeneracy force `Q b'₁ = Q b'₂ = Q b₁`
  (all orthogonal-basis vectors are non-isotropic via
  `LinearMap.IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft`); witness `x ∈ {0,1,-1}` because
  the discriminant `φ x = a(c1+x²c2)-(p+xq)²` cannot vanish at all three while `a,c1,c2 ≠ 0` and
  `pq = 0`. Nondegeneracy of `restrict Q (span{b₁,b'₁+x b'₂})` via
  `restrict_nondegenerate_iff_isCompl_orthoCompl` + `Submodule.isCompl_iff_disjoint` +
  `Submodule.disjoint_def` (2x2 system with determinant `φ x ≠ 0`).
- [step 6] next: `lake_check` + `lean_verify`.
- [step 6] `lake_check Pptc/HasseMinkowski/BasisChain.lean` -> `OK - no errors or warnings`.
  `lean_verify Module.Basis.exists_const` -> axioms `{propext, Classical.choice, Quot.sound}`.
  DONE, sorry-free.

## FINAL STATUS B.4 (file `Pptc/HasseMinkowski/BasisChain.lean`, appended)
- Import added: `Pptc.HasseMinkowski.QuadraticForm.Witt` (transitively `Restriction`).
- `Module.Basis.exists_const` -- verbatim WiN7 statement (with `Pptc.HasseMinkowski.restrict`),
  proved sorry-free. NO statement adaptation; no `[Infinite k]` hypothesis needed.
- Existing declarations untouched. `lake_check` clean; axioms standard three.
