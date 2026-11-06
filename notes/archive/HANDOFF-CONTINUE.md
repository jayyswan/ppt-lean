# CONTINUE HERE — next session (Hasse–Minkowski / Meyer, Lean 4.33, `pptc/`)

Read `AGENTS.md` first (LSP-first policy + the `lake-build-guard` resource manager are now
active). Everything below is current as of the crash-recovery session.

**Forward plan:** `PLAN-HasseMinkowski.md` (repo root) = `pptc/Pptc/HasseMinkowski/Plan-next.md` —
the workstreams, dependencies, critical path (Witt/orthocomplement layer is the blocker) and ops rules.

## Objective
Prove, sorry-free, in the `Pptc` package (`C:\dev\Powerpoint\lean\pptc`):
`hasseMinkowski (n ≥ 1) : rank-n nondegenerate Q over ℚ is isotropic iff EverywhereLocallyIsotropic`,
then `meyer`, and finally wire the real `meyer` into `Pptc/Nonic.lean` replacing the `sorry` in
`exists_tschirnhaus9`. Structural blueprint: WiN7 `mariainesdff/HassePrinciple` (rank 3 and rank ≥5
are `sorry` upstream — we must do them ourselves). Details: `pptc/Pptc/HasseMinkowski/Plan.md`.

## Wave-10 update (READ FIRST — supersedes the "Remaining blockers" below)

Progress since the last note: **Workstream A.1 is DONE** (was the #1 blocker, had defeated 3 workers):
`HilbertSymbol/Two.lean` now proves `hilbertSym_padic_two_eq` (Serre's 2-adic formula),
`hilbertSym_padic_two_mul_left`, and **`instance : HasBilinHilbertSym ℚ_[2]`** — sorry-free, verified
(`lake_check` OK, axioms `{propext, Classical.choice, Quot.sound}`).

New files (all sorry-free, LSP-clean, `lake_check` OK):
- `QuadraticForm/Restriction.lean` — B.1/B.2/B.3a: `orthoCompl`, `restrict`, `mem_orthoCompl`,
  `associated_restrict`, `finrank_add_finrank_orthoCompl`, `orthoCompl_orthoCompl_eq_of_nondegenerate`,
  `restrict_nondegenerate_iff_isCompl_orthoCompl`, and the splitting isometry
  `isometryEquiv_prod_of_isCompl` (`IsCompl W Wᗮ ⇒ Q ≅ Q|_W ⊗ Q|_Wᗮ`).
- `QuadraticForm/Witt.lean` — B.3 (base): orthogonal `reflection` (`x ↦ x - 2·(B(x,a)/Q a)·a`),
  `reflection_isometry`, and rank-one transitivity
  `exists_isometryEquiv_of_Q_eq : Q v = Q w ≠ 0 → ∃ φ, φ v = w`.
- `HilbertSymbol/Norm.lean` — `hilbertSym_eq_one_iff_isNorm`
  (`(a,b)=1 ↔ a` is a norm in `QuadraticAlgebra k b 0`), the entry point for uniform bimultiplicativity
  and A.2.

Key recon (`HANDOFF-witt.md`): contrary to the old note, Mathlib 4.33 **has** `QuadraticMap.restrict`,
`QuadraticMap.comp`, `LinearMap.BilinForm.orthogonal` and the whole bilinear orthogonality/finrank API;
Workstream B was therefore not blocked on missing definitions. Mathlib still has **no** Hilbert symbol /
norm group / Hilbert 90, and **no** Witt cancellation or Witt extension (that is the genuine residual).

Infra: subagents were aborting at their hard step caps (`lean-prover` 70, `lean-explorer` 30).
Caps raised to 150 / 60 in `.opencode/agent/*.md` — **requires an opencode restart** to take effect;
worker prompts now also mandate appending to the per-task `HANDOFF-*.md` every ~6 tool calls.

Still open, in rough priority order: **B.4** (`ChainHypothesis`; `exists_const` is now proved,
`chainOfNondegenerate` remains), **B.5** (invariant well-definedness), **C.0** (the real Legendre
descent — see the correction below), then C.1–C.3, D, E.

**Wave-13 additions (read before starting):**
- **A.2 DONE**: `HilbertSymbol/Reciprocity.lean` (1139 lines) now proves `hilbertReciprocity`.
- **B.3 DONE**: `QuadraticForm/Witt.lean` (486 lines) has `reflection`, rank-one transitivity, **Witt
  extension** (`exists_isometryEquiv_of_isometric_embeddings`) and **general Witt cancellation**
  (`isometryEquiv_orthoCompl_of_isometryEquiv_restrict`).
- **B.4 partial**: `Module.Basis.exists_const` proved as stated in `BasisChain.lean`.
- **PLAN CORRECTION (`Plan-next.md` C.0 is wrong)**: the "product-formula route" to
  `HilbertSymLocalGlobal` does not work — under its hypotheses every local symbol is already `1`, so
  reciprocity is vacuous. The target is Legendre's theorem / Hasse norm theorem for quadratic
  extensions of ℚ; it needs Legendre descent (or global CFT), not A.2. `RankThree.lean` now records
  `hilbertSymLocalGlobal_iff_rankThreeDiagonal` and `RankThreeDiagonalLocalGlobal` pinning this down.
- WiN7's `Chain.basis_isContiguous` is vacuous (same index both sides); our `BasisChain.lean`'s
  `ChainHypothesis` uses genuine consecutive contiguity and is the real (harder) statement.

## Current state (all files under `Pptc/HasseMinkowski/`, namespace `Pptc.HasseMinkowski`)

DONE + sorry-free, LSP-clean (`lake_check` final confirmations pending only for the
files checked under low RAM):
- `Basic.lean`, `RatSquares.lean`, `Locally.lean`, `RankTwo.lean`, `Prod.lean`,
  `RatApproximation.lean`, `Padics/Squares.lean`, `Padics/CommonRoot.lean`,
  `HilbertSymbol/Defs.lean`, `HilbertSymbol/Real.lean`, `HilbertSymbol/Padic.lean`
  (full odd-`p` formula `hilbertSym_padic_odd_eq` + `hilbertSym_padic_odd_mul_left`),
  `HilbertSymbol/Two.lean` (UNITS classification only — see the crash note), `HasseInvariant.lean`,
  `HilbertSymbol/Existence.lean`, `HilbertSymbol/Reciprocity.lean`, `RankCriteria.lean` (recent),
  `RankThree.lean` (recent; conditional on `hloc`), `HasseInvariantWellDef.lean` (recent;
  conditional on `hconn`, which is FALSE — see below), `Chain.lean` (recent; refutes `hconn`, names
  the true residual), `BasisChain.lean` (recent; hosts `Module.Basis.Chain` + `ChainHypothesis`),
  `RankCriteriaGeneral.lean` (recent; general rank-2/3 criteria, also carries the false `hconn`).
- `Targets.lean` = INTER-LAYER CONTRACTS, all `sorry` on purpose: `isotropic_of_rank_{one..four}`,
  `isotropic_of_five_le_rank`, `hasseMinkowski`, `meyer` (concrete statements in the file).
- WiFi: `Scratch/win7-reference.md` = upstream WiN7 signatures/status dump; per-task logs
  `HANDOFF-*.md` in the same dir.

## Session crash recovery — know this
1. `HilbertSymbol/Two.lean` was half-overwritten by an interrupted worker. RESTORED to the clean
   units classification (≤ line 694). The abandoned 2-adic mixed-case experiment is saved at
   `Scratch/Two-padic-mixed-experiment.lean.full.bak` (contains `eps`, `omg` characters,
   `isSquare_neg_seven`, mod-8 obstruction `hilbertSym_eq_neg_one_of_zmod8`, `repA_*`/`repB_*`
   tables). 6 `repB_*` `-1` cases are provably wrong under the chosen mod-8 argument (`decide`
   found mod-8 solutions) — reuse only the ε/ω chars and the valid cases; do the rest via the
   Serre formula or a finer modulus.
2. `lake build` / `lake_check` may fail with "failed to read …*.olean(.private)" purely from low
   RAM (the guard's 900 MB floor). Not a source error: kill stale `lean`/`lake` (never python),
   free memory, retry; or trust a clean LSP elaboration + `lean_verify` (axioms =
   {propext, Classical.choice, Quot.sound}).
3. The naive `∏ p, hilbertSym … = 1` is ill-typed and false; correct form:
   `(∏ᶠ p, hilbertSym (a:ℚ_[p]) (b:ℚ_[p])) * hilbertSym (a:ℝ) (b:ℝ) = 1` (already used in
   `Reciprocity.lean`).

## Wave-7 update (latest; files added above)
- `RankThree.lean`: `isotropic_of_rank_three` is PROVED modulo `hloc : HilbertSymLocalGlobal`
  (all local `(A,B)_v = 1` ⟹ global `(A,B)_ℚ = 1` — the Hasse norm theorem for quadratic
  extensions). Diagonalization, the ternary criterion, base change over every place and transfer
  back are all done. Log `HANDOFF-rankthree.md`.
- `HasseInvariantWellDef.lean`: `hasseMinkowskiInv.eq_of_equivalent` is PROVED modulo `hconn`
  (connectivity of diagonalizations: reindexings + splitting off a common rank-one summand with
  equivalent tails = WiN7 `Chain.lean`, itself 2 `sorry`). `LinearMap.separatingLeft_of_equivalent`
  is unconditional. Log `HANDOFF-wellDef.md`.
- Full 2-adic formula: worker aborted without edits; `Two.lean` re-verified clean; **still to do**.

## Wave-8 update — the `hconn` hypothesis is FALSE (important)
- `Chain.lean` (sorry-free, `lake_check` OK) proves **`diagonalConnectivity_false : ¬ DiagonalConnectivity ℝ`**:
  the diagonal-only connectivity relation `hconn` carried by `HasseInvariantWellDef.lean` (and hence by
  `RankCriteriaGeneral.lean` and `RankCriteria.lean`'s `hwell`) is refuted — over ℝ, `![1]` and `![4]`
  give equivalent rank-1 forms but no diagonal `Step` relates them. So those conditional theorems are
  **vacuous as stated**; the theorem (invariant well-definedness) is true, but this proof route is not
  sufficient. `Chain.lean` names the genuine residual `ChainHypothesis` (basis-level `Nonempty (Chain Q b b')`,
  WiN7 `chainOfNondegenerate`, 2 `sorry` upstream).
- `RankCriteriaGeneral.lean` (sorry-free, `lake_check` OK): general `represents_iff_of_rank_two` /
  `represents_zero_iff_of_rank_three` for `Basis (Fin n)` forms — but carries the false `hconn`, so it
  needs its hypothesis swapped to `ChainHypothesis` (and its proof reworked along the basis chain).
- 2-adic formula: a second worker aborted with no edits; `Two.lean` still clean.

## Wave-9 update — `ChainHypothesis` factored out; the reduction is BLOCKED
- Created `BasisChain.lean` (sorry-free, LSP-clean) hosting `Module.Basis.IsContiguous`,
  `Module.Basis.Chain`, and `ChainHypothesis` (WiN7's `chainOfNondegenerate`, stated exactly), moved
  out of `Chain.lean` to break the import cycle. `Chain.lean` now imports it and stays clean.
- `HasseInvariantWellDef.lean`'s module doc now WARNs that its `hconn` is false and the three
  well-definedness theorems are vacuous as stated.
- **The rework cannot be completed sorry-free at present:** reducing `ChainHypothesis` to
  `hasseMinkowskiInvAux.eq_of_equivalent` needs orthogonal-complement / restriction / Witt-cancellation
  machinery that Mathlib 4.33 lacks (no `orthoCompl`, no `QuadraticForm.restrict` — verified by
  `lean_local_search`), which is exactly why upstream leaves `eq_of_equivalent` `sorry`. A future
  session can restate the results with `ChainHypothesis` once Mathlib has that.

## Remaining blockers (localized)
1. Full 2-adic closed formula (`hilbertSym_padic_two_eq` + `mul_left` / `HasBilinHilbertSym ℚ_[2]`).
2. Basis-level `ChainHypothesis` (WiN7 `chainOfNondegenerate`) — replaces the false diagonal `hconn`;
   needed to make `HasseInvariantWellDef` / `RankCriteriaGeneral` / rank-3/4 non-vacuous.
3. `hloc` — Hasse norm theorem (deep, class-field-theoretic; `sorry` upstream — likely out of scope).
4. General (non-diagonal) rank-2/3 criteria: statements exist in `RankCriteriaGeneral.lean` but are
   vacuous until (2) is done.

## Next steps (suggested parallel wave, one worker per file, LSP-first)
1. **Full 2-adic formula** (retry): start from `Scratch/Two-padic-mixed-experiment.lean.full.bak`
   (`eps`/`omg` chars + valid cases only), append to `Two.lean`, keep it compiling at every step.
2. **`hconn`**: prove the WiN7 `Chain.lean` connectivity statement used by
   `HasseInvariantWellDef.lean` (read that file for the exact `hconn` type), or port `Chain.lean`.
3. **General rank-2/3 criteria**: squarefree-units diagonalization to lift
   `represents_zero_iff_of_rank_three_diag` (diagonal) to an arbitrary nondegenerate rank-3 form.
4. **Rank 4**: port WiN7 `RankFour.lean` on top of `Targets.isotropic_of_rank_three` (stub) + our
   `Prod.lean` (`iso_prod_neg`, `prod_isotropic_iff`, base-change bits).
5. **n→n-1 induction (rank ≥ 5 = Meyer)**: `isotropic_of_five_le_rank` per WiN7
   `HighDimensionMeyer.lean`/`HasDimensionFive.lean`.

Then wire `Nonic.lean` (replace `exists_tschirnhaus9`'s `sorry`) using the real `meyer`
(`Pptc.HasseMinkowski.meyer`, `Targets.lean` has the interface). Note the Hermite-signature /
collision layer inside `exists_tschirnhaus9` is a separate remaining `sorry`.

## Do not
- Run whole-project `lake build` (OOM). One narrow target at most, `-j1`.
- Generic process kills (`Get-Process python …`) — kills the lean-lsp MCP for the session.
- Import `Mathlib` wholesale in new files (targeted imports only).