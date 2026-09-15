# PLAN-NEXT — remaining work for Hasse–Minkowski & Meyer (`pptc/`, Lean 4.33)

> **SUPERSEDED — do not follow.** Use `Plan-v3.md`. Workstream B (Witt/chain/invariant
> well-definedness) is off the critical path, and C.0 (rank 3) is Legendre descent, not the
> Hasse norm theorem via class field theory. Kept for history only.

Forward-looking, actionable plan. Supersedes the milestone list at the end of `Plan.md`; the
detailed running history is `HANDOFF.md`, and the quick resume note is `HANDOFF-CONTINUE.md`
(repo root). All paths are relative to the package root `pptc/`.

**Goal.** Sorry-free proofs of
1. `hasseMinkowski` — nondegenerate finite-dim `Q / ℚ` is isotropic iff isotropic over every
   completion (`ℝ`, `ℚ_[p]`);
2. `meyer` — indefinite `Q / ℚ` in `≥ 5` variables is isotropic;
then wire `meyer` into `Pptc/Nonic.lean` (`exists_tschirnhaus9`).
Interfaces are stubbed in `Pptc/HasseMinkowski/Targets.lean`; they must not be imported by
completed layers.

---

## 1. Done, sorry-free (verified LSP-clean; final `lake_check` may have been skipped only for
RAM reasons)

| Layer | File(s) | Key declarations |
|---|---|---|
| 0 | `Basic.lean` | `Isotropic`, `represents`, rank-one isotropy, nondegeneracy lemmas, `Indefinite.isotropic`, base-change of equivalences |
| 1 | `RatSquares.lean`, `Padics/Squares.lean`, `Padics/CommonRoot.lean`, `RatApproximation.lean` | `Rat.isSquare_iff_even_padicValRat`; `PadicInt.isSquare_of_zmod(_zmodPow)`, `Padic.unitSquares`; `exists_padicInt_solution`, `lift_solutions_to_int_first`, `exists_nontrivial_zero`; `Rat.approximation` |
| 2 | `HilbertSymbol/{Defs,Real,Padic,Two,Existence,Reciprocity}.lean` | `hilbertSym`, `HasBilinHilbertSym`, `HasBilinHilbertSym ℝ`; **full odd-`p` Serre formula** `hilbertSym_padic_odd_eq` + `_mul_left`; 2-adic **units** classification; Dirichlet/CRT existence; `almost_all_one`, square-case product formula, `HilbertReciprocity : Prop` |
| 2 | `HasseInvariant.lean` | `hasseMinkowskiInvAux` (+ `_zero/_one/_two/_three/_cons/_prod_rank_one`), `hasseMinkowskiInv`, `_eq_one_or_neg_one` |
| 3 | `RankTwo.lean`, `Prod.lean`, `RankCriteria.lean` | `isotropic_of_rank_one/two`; `iso_prod_neg`, `prod_isotropic_iff`, `nondegenerate_iff_discr_ne_zero`, base-change; `weightedSumSquares_isotropic_iff_hilbertSym_eq_one`, `represents_zero_iff_of_rank_three_diag` |
| 3 | `RankThree.lean`, `RankCriteriaGeneral.lean` | `isotropic_of_rank_three` (mod **C.0**), general rank-2/3 criteria (mod **B.5**) — see caveats |
| — | `HasseInvariantWellDef.lean`, `Chain.lean`, `BasisChain.lean` | `hasseMinkowskiInv.eq_of_equivalent` (mod **B.5**); refutation of the false diagonal `hconn`; the true residual `ChainHypothesis` |

### Caveats that gate downstream use
* **`hconn` is FALSE** (`Chain.lean : diagonalConnectivity_false`). So `HasseInvariantWellDef.lean`,
  `RankCriteriaGeneral.lean` and `RankCriteria.lean`'s `hwell` are **vacuous as stated**. Do **not**
  build on them until Workstream B lands.
* `RankThree.lean` is proved modulo `hloc : HilbertSymLocalGlobal` (Hasse norm theorem). Workstream
  C offers a **more tractable alternative** that avoids `hloc` (the product-formula route).
* `HilbertSymbol/Two.lean` covers only 2-adic **units**; the valuation-bearing formula is **A.1**.

---

## 2. The blockers

| # | Blocker | Root cause | Bites |
|---|---|---|---|
| B1 | full 2-adic Hilbert formula | case analysis not finished | local criteria, product formula, everything local at `p=2` |
| B2 | invariant well-definedness | needs orthogonal complement / restriction / Witt cancellation; **absent from Mathlib 4.33** (`orthoCompl`, `QuadraticForm.restrict` not found), `sorry` upstream | general rank-2/3 criteria, classification, rank 4/5 |
| B3 | global product formula (Hilbert reciprocity) | needs full B1 + QR assembly over all places | rank-3 and rank-4 global steps |
| B4 | rank-3 local–global | currently isolated as `hloc` (Hasse norm theorem, deep) | rank 3, rank 4, Meyer |
| B5 | rank-4 and high-rank (Meyer) | needs B2–B4 + local isotropy `n ≥ 5` | `hasseMinkowski`, `meyer`, Nonic |

---

## 3. Workstreams (tasks, targets, dependencies, deliverable)

Legend: **S** ≈ ≤ half-session, **M** ≈ one session, **L** ≈ multi-session, **XL** ≈ research.

### Workstream A — complete the Hilbert symbol (unblocks B3, and all local computation)
- [x] **A.1** (M) 2-adic closed formula. File: `HilbertSymbol/Two.lean` (append; keep compiling).
  Reuse `Scratch/Two-padic-mixed-experiment.lean.full.bak`: `eps`/`omg` characters,
  `parityPow_neg_one_{even,odd}`, `toZModPow_two_eq_of_three`, `isSquare_neg_seven`, and the valid
  cases. **Do not** reuse the mod-8 obstruction for the 6 `repB_*` cases (a `ZMod 8` solution with a
  unit coordinate exists, e.g. `z=0,x=y=1` for `2x²+6y²=z²`); use explicit rational points, a finer
  modulus, or the closed formula. Deliver `hilbertSym_padic_two_eq` (`two_adic_eq`) and
  `hilbertSym_padic_two_mul_left`, then an unconditional `HasBilinHilbertSym ℚ_[2]`.
- [x] **A.2** (L) **Global product formula** (Hilbert reciprocity): prove `HilbertReciprocity`
  (`(∏ᶠ p, (a,b)_p) * (a,b)_ℝ = 1`), file `HilbertSymbol/Reciprocity.lean`. Use the explicit odd-`p`
  formula + A.1 for `p=2` + `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`. The square
  case is already proved. Deliverable: unconditional reciprocity.
- [ ] **A.3** (S) Corollaries used downstream: `hilbertSym_rat`-normalisation, `(a,·)` multiplicativity
  over ℚ, and any square-class lemmas the classification needs.

### Workstream B — Witt / orthogonal-complement layer (**critical path**, XL)
- [x] **B.1** (L) Define, in a new `QuadraticForm/Restriction.lean`: the orthogonal complement
  `Wᗮ` of a submodule `W` w.r.t. `Q.associated`, and the restriction `Q|_W` (needs
  `Submodule`, `LinearMap.ker`, `QuadraticMap.comp`/restrict). Prove the basic API (`W ≤ Wᗮᗮ`,
  `IsOrtho`, dimension counting, `Q`-orthogonal decomposition `V = W ⊥ Wᗮ` for nondegenerate `Q`).
- [x] **B.2** (M) Nondegeneracy: if `Q` is nondegenerate and `Q v ≠ 0` then `Q|_({v}ᗮ)` is
  nondegenerate; `Q|_W` is nondegenerate when `Q` is and `V = W ⊥ Wᗮ`.
- [x] **B.3** (L) **Witt's cancellation / isometry extension**: two isometric nondegenerate forms
  with isometric "restrictions" have isometric orthogonal complements; and any isometry
  `W₁ ≅ W₂` extends to an isometry of the ambient spaces (Witt's extension theorem).
- [ ] **B.4** (L) Discharge `ChainHypothesis k` (`BasisChain.lean`, WiN7 `chainOfNondegenerate`):
  `exists_const` is now PROVED (as stated, sorry-free); `chainOfNondegenerate` remains. NOTE: WiN7's
  `Chain.basis_isContiguous` is vacuous (same index on both sides), so its `chainOfNondegenerate` port
  is useless; our `ChainHypothesis` is the genuine consecutive-contiguity version, now attackable with
  `Witt.lean`'s extension/cancellation.
  any two `Q`-orthogonal bases of a nondegenerate form in dim `≥ 3` are joined by a chain of
  orthogonal bases with consecutive contiguity. Route: B.1–B.3 + induction, following
  `github.com/mariainesdff/HassePrinciple/.../QuadraticForm/Chain.lean` (`exists_const`,
  `chainOfNondegenerate`) and filling its two `sorry`s.
- [ ] **B.5** (L) **Reduction**: with B.4, prove `hasseMinkowskiInvAux.eq_of_equivalent` and
  `hasseMinkowskiInv.eq_of_equivalent` (replace the vacuous `hconn` in `HasseInvariantWellDef.lean`
  by `ChainHypothesis`, then discharge it). For a contiguous step, `ε = (Q v, disc Wᗮ) · ε(Wᗮ)`:
  the cross term is square-invariant (`disc` determined up to square) and the tail factor is
  handled by strong induction on `finrank` (base cases `n ≤ 2` directly). Then update
  `RankCriteriaGeneral.lean` / `RankCriteria.lean` to the non-vacuous hypothesis. **Definition of
  done:** `RankCriteriaGeneral` proves the general rank-2/3 criteria with no false hypothesis.

### Workstream C — rank criteria & the rank-3 global step (unblocks B5)
- [ ] **C.0** (L, was mis-rated S) `hloc` = `HilbertSymLocalGlobal`. **The "product-formula route"
  is INVALID** (verified by a worker): under `HilbertSymLocalGlobal`'s hypotheses every local factor is
  already `1`, so Hilbert reciprocity reduces to `1 * 1 = 1` and says nothing about the global
  `(A,B)_ℚ`. The target is *exactly* Legendre's theorem / the Hasse norm theorem for quadratic
  extensions of ℚ (WiN7 leaves it `sorry`); the global conic symbol is not multiplicative over ℚ, so
  the norm-group-index-2 shortcut is also out. `RankThree.lean` now records the equivalence
  `hilbertSymLocalGlobal_iff_rankThreeDiagonal` and `hilbertSymLocalGlobal_iff_rankThreeDiagonal`'s
  diagonal form `RankThreeDiagonalLocalGlobal`. A real proof needs **Legendre descent** (Minkowski /
  geometry of numbers) or global class field theory. Lead: prove `RankThreeDiagonalLocalGlobal` by
  Legendre descent using `hilbertReciprocity` + Mathlib's `quadraticReciprocity`.

- [ ] **C.1** (M) General rank-2 criterion `represents_iff_of_rank_two` (exists in
  `RankCriteriaGeneral.lean` modulo B.5 — repoint once B.5 lands).
- [ ] **C.2** (M) General rank-3 criterion `represents_zero_iff_of_rank_three` (same).
- [ ] **C.3** (L) Local classification of quadratic forms over `ℚ_[p]` (square classes,
  determinant, Hasse invariant) using A.1 and Hensel; needed for the local steps of ranks 4–5.

### Workstream D — rank 4 and high rank; assemble Meyer (XL)
- [ ] **D.1** (L) `isotropic_of_rank_four` (port WiN7 `QuadraticForm/RankFour.lean`, using C.0/C.2 +
  orthogonal splitting `Prod.lean`: `iso_prod_neg`, `prod_isotropic_iff`).
- [ ] **D.2** (L) Local isotropy in `≥ 5` variables over each `ℚ_[p]` (Chevalley–Warning /
  classification; `Mathlib` has `char_dvd_card_solutions*`), and over `ℝ` (`Indefinite`).
- [ ] **D.3** (L) Global reduction `n → n-1` (or `n → n-2`) for `n ≥ 5` (Serre Ch. IV §2),
  using `represent` of a chosen value and D.1; assemble `isotropic_of_five_le_rank`.
- [ ] **D.4** (M) `hasseMinkowski` (all ranks) from the rank cases + the reduction.
- [ ] **D.5** (M) `meyer` from `hasseMinkowski` + local isotropy in `≥ 5` variables + `Indefinite`.

### Workstream E — wire into Nonic
- [ ] **E.1** (S) Point `Pptc/Nonic.lean` at the proved `Pptc.HasseMinkowski.meyer`; delete the
  `Targets` import and the `exists_tschirnhaus9` `sorry`.
- [ ] **E.2** (M) Provide the Hermite-signature / collision layer that `exists_tschirnhaus9` still
  needs (separate from `meyer`). Track in `HANDOFF-nonic-meyer.md` / `PLAN-nonic-meyer.md`.
- [ ] **E.3** (S) Delete `Targets.lean` once nothing imports it.

---

## 4. Dependency graph & recommended order

```
A.1 (2-adic) ─┬─> A.2 (product formula) ─┬─> C.0 (rank 3, product route) ─> D.1 (rank 4) ─┐
              │                          │                                              │
B.1─B.2─B.3─B.4─B.5 (Witt / well-def) ───┴─> C.1,C.2 (general criteria) ────────────────┤
                                                                                         v
                                             C.3 (local classification) ─> D.2 ─> D.3 (Meyer) ─> E
```

Recommended waves (each worker one file, LSP-first):
1. **A.1** (2-adic) and **B.1–B.2** (orthocomplement/restriction) in parallel.
2. **A.2** (product formula) and **B.3** (Witt cancellation) in parallel.
3. **C.0** (rank 3 product route) and **B.4** in parallel.
4. **B.5**, then **C.1/C.2**, then **D.1**.
5. **C.3**, **D.2**, **D.3**, **D.4**, **D.5**, **E.1–E.3**.

The single highest-leverage item is **Workstream B**: without it the invariant is not well-defined
and every "criteria" theorem is vacuous. It is also the item upstream does not have (2 `sorry`s),
so scope it explicitly as a major development, not a port.

---

## 5. Risks, decisions, fallbacks

* **B is research-scale.** If B stalls, the whole classification route stalls. Decision point after
  B.1–B.2: if the `Submodule`/restriction API is too costly, consider proving well-definedness only
  in the ranks actually needed (`n ≤ 4`) by explicit case analysis, accepting a higher-rank gap.
* **`hloc` (Hasse norm theorem) is likely out of scope** (global class field theory). The plan
  deliberately avoids it via A.2 (product formula). If C.0 fails, re-evaluate.
* **Local `p = 2` is the technical bottleneck** (A.1, C.3). Budget extra time; the `.bak` salvage
  plus `HANDOFF-hilberttwo.md` contains the working pieces.
* **`Nonic.lean` may not need full `meyer`.** Before D.5, re-read `Pptc/Nonic.lean` and
  `NOTES-nonic-meyer.md`: if `exists_tschirnhaus9` only needs isotropy of one explicit form, a
  direct argument could short-circuit E.
* **Upstream alignment.** WiN7 file/lemma names are mapped in `Scratch/win7-reference.md`; port
  names where possible for easier cross-checking.

---

## 6. Ops & conventions (do not relearn the hard way)

* **LSP-first.** Iterate with `lean_diagnostic_messages` / `lean_goal` / `lean_multi_attempt`
  (~1 s, warm). `lake_check` is the final per-file confirmation only; `lake build Pptc.Foo` only to
  emit an `.olean` for a dependent file. **Never** a whole-project `lake build` (OOMs).
* **Resource manager** (`.opencode/plugins/lake-build-guard.ts`, active after restart): serializes
  shell Lean work (`LEAN_GUARD_HEAVY_CONCURRENCY=1`), caps concurrent local lean-lsp elaborations
  (`LEAN_GUARD_LSP_CONCURRENCY=2`), and waits while free RAM `< 900 MB`.
* **Stale processes.** After every batch of subagents, run
  `Get-Process lean,lake | Stop-Process -Force`. Stale `lean`/`lake` eat all RAM and cause
  "failed to read …*.olean(.private)" errors that look like source errors. **Never** kill
  python/uvx/node (`lean-lsp` MCP).
* **Subagents.** Use `@lean-prover` (one file / one deliverable) and `@lean-explorer`. Keep a
  per-task `HANDOFF-<topic>.md`. Note: large multi-file refactors have repeatedly **aborted with no
  output**; prefer small, single-file, well-specified tasks, and do risky refactors in the main
  session.
* **Conventions.** Targeted imports (never `import Mathlib`); `-- Theorem:` lines; ≤ 100-char lines;
  no `sorry`/`admit`/`axiom` in delivered files; verify axioms with `lean_verify`
  (`{propext, Classical.choice, Quot.sound}` only); CRLF handled by the guard plugin.

---

## 7. References

* WiN7: `github.com/mariainesdff/HassePrinciple` (Lean 4.34-rc2).
  - `QuadraticForm/Chain.lean` (2 `sorry`) — Workstream B.
  - `QuadraticForm/HasseMinkowskiInvariant.lean` (`eq_of_equivalent` `sorry`) — B.5.
  - `QuadraticForm/RankThree.lean`, `RankFour.lean`, `HighDimensionMeyer.lean` — C/D.
  - `HilbertSymbol/Basic.lean` (odd + 2-adic + reciprocity `sorry`) — A.
  - local signature/status dump: `Pptc/HasseMinkowski/Scratch/win7-reference.md`.
* Serre, *A Course in Arithmetic*, Ch. IV (Hilbert symbol, Hasse invariant, Hasse–Minkowski, Meyer).
* Local salvage: `Pptc/HasseMinkowski/Scratch/Two-padic-mixed-experiment.lean.full.bak`.
* Logs: `HANDOFF.md` (master), `HANDOFF-{wellDef,chain,rankthree,rankgeneral,reciprocity,hilberttwo}.md`.

## 8. Verification checklist per delivered file

1. `lean_diagnostic_messages` clean (no errors; warnings only the pre-existing `abel`/long-line kind).
2. No `sorry`/`admit`/`axiom`: `rg -n 'sorry|admit|axiom' Pptc/HasseMinkowski/<file>.lean`.
3. `lean_verify <main theorem>` → axioms `{propext, Classical.choice, Quot.sound}`.
4. One final `lake_check Pptc/HasseMinkowski/<file>.lean` (after killing stale `lean`/`lake`).
5. Append the result to the per-task `HANDOFF-*.md` and to `HANDOFF.md`.
