# HANDOFF: Hasse–Minkowski / Meyer (Pptc)

One line per step. See `Plan.md` for architecture.

- [start] Recon: Mathlib 4.33 has no Hasse–Minkowski/Meyer/Hilbert symbol/Legendre
  3-squares; has abstract `QuadraticMap` theory, `padicValRat`, `hensels_lemma`,
  Chevalley–Warning, quadratic reciprocity. WiN7 `HassePrinciple` (4.34-rc2) leaves
  rank 3 and rank ≥ 5 (= Meyer) as `sorry`.
- [layout] Created `pptc/Pptc/HasseMinkowski/` for all code + docs.
- [M0] `Basic.lean` (Layer 0) DONE, sorry-free, lake_check OK: `Isotropic`, `IsotropicFn`,
  `represents`, `represents_zero_iff_isotropic`, `represents_iff_sub_isotropic`,
  `isotropic_iff_zero_of_rank_one`, `nondegenerate_weightedSumSquares`,
  `nondegenerate_prod`, `nondegenerate_of_anisotropic`, `anisotropic_of_rank_zero`,
  `Indefinite` + `Indefinite.isotropic`, base-change of `IsometryEquiv`/`Equivalent`.
  (Subagent log: HANDOFF-basic.md.)
- [M0] `RatSquares.lean` (Layer 1) DONE, sorry-free, lake_check OK:
  `Rat.isSquare_iff_even_padicValRat : IsSquare q ↔ 0 ≤ q ∧ ∀ p prime, Even (padicValRat p q)`
  + companion `isSquare_of_nonneg_of_even_padicValRat`. (Log: HANDOFF-ratsquares.md.)
- [plan] WiN7 porting survey done: rank ≤2 and rank 4 (modulo rank 3) proved there; rank 3
  and rank ≥5 are `sorry`; the `n→n-1` high-rank reduction bottoms out in rank 4; the only
  Mathlib-4.33 gap they rely on is `Rat.isSquare_iff_even_factorization`, now supplied by
  our `RatSquares.lean`.
- [M1] `Locally.lean` (Layer 2a) DONE, sorry-free: `EverywhereLocallyIsotropic`,
  `isotropic_everywhereLocallyIsotropic`, `baseChange_weightedSumSquares`.
- [M1] `RankTwo.lean` DONE, sorry-free, `lake build` OK: `QuadraticMap.Equivalent.represents_iff`,
  `isotropic_of_rank_one`, `isotropic_of_rank_two`.
- [M2] `HilbertSymbol/Defs.lean` DONE, sorry-free: `hilbertSym` def, `HasBilinHilbertSym`
  class, zero/value/commutation lemmas, `HasBilinHilbertSym.mul_right_eq`. Instances for `ℝ`
  and `ℚ_[p]` NOT yet done.
- [M2] `Padics/Squares.lean` DONE, sorry-free: `PadicInt.p_dvd_iff_toZMod_eq_zero`,
  `pow_p_dvd_iff_toZModPow_eq_zero`, `PadicInt.isSquare_of_zmod`, `isSquare_of_zmodPow`,
  `Padic.isSquare_of_dist_one_lt_one`, `isSquare_of_dist_one_lt_pow`,
  `exists_pow_isSquare_of_dist_one_lt`, `isOpen_squares_sdiff_zero`, `Padic.unitSquares`.
- [scratch] `Targets.lean`: sorry-stubbed contracts (`isotropic_of_rank_{one..four}`,
  `isotropic_of_five_le_rank`, `hasseMinkowski`, `meyer`) so downstream layers can be built in
  parallel; `Scratch/win7-reference.md`: WiN7 declaration signatures/proofs for porting.
- [env] `lake build` transiently failed with `failed to read ... .olean` under memory pressure;
  killing stale `lean`/`lake` and retrying fixed it. `lake_check` remains reliable.
- [next] rank 0 (vacuous) + `baseChange_prod`; `HasBilinHilbertSym ℝ` (easy) and `ℚ_[p]` (Hensel,
  the hard Hadamard/odd+2-adic cases); `almost_all_one`/`prod_eq_one`; then rank 3 (Legendre
  descent, see `Scratch/win7-reference.md`), rank 4, and the `n→n-1` high-rank induction (Meyer).
  M5: wire `Pptc/Nonic.lean` from `Targets.meyer` to the real `meyer`.
- [wave2] `HilbertSymbol/Real.lean` DONE: `hilbertSym_real_eq`, `hilbertSym_real_mul_left`,
  `instance : HasBilinHilbertSym ℝ`.
- [wave2] `Prod.lean` DONE (clean): `baseChange_prod`, `baseChange_neg`, `baseChange_prod_neg`,
  `weightedSumSquares_{toMatrix,discr}`, `baseChange_{toMatrix,discr}`,
  `QuadraticMap.Equivalent.{nondegenerate,nondegenerate_iff}`,
  `mul_unit_isotropic_iff`, `weightedSumSquares_mul_squares_equivalent`. NOT done:
  `nondegenerate_baseChange`, `nondegenerate_iff_discr_ne_zero`, `prod_isotropic_iff`.
- [wave2] `RatApproximation.lean` DONE, sorry-free: `approximation'` (weak approximation) and
  `approximation` (`Dense (Set.range (finiteEmbedding S))`).
- [wave2] `Padics/CommonRoot.lean` NOT delivered (worker hit step limit; scratch deleted before its
  content was saved — must be redone). Findings: `exists_padicInt_solution` is provable;
  `exists_nontrivial_zero` is FALSE as stated unless one assumes `‖v‖ = 1`; `multivariable_hensel`
  needs a sharper Newton bound that Mathlib keeps `private`; `common_root_tfae` needs a
  compactness/inverse-limit argument over `ZMod (p^n)`. See `HANDOFF-commonroot.md`.
- [wave3] launched: `Padics/CommonRoot.lean`, `Prod.lean` continued (`nondegenerate_baseChange`),
  `HilbertSymbol/Padic.lean` (odd-prime bilinearity), `HasseInvariant.lean`.
- [wave3] `Padics/CommonRoot.lean` DONE, sorry-free: `Padic.exists_padicInt_solution`,
  `lift_solutions_to_int_first`, and a CORRECTED `exists_nontrivial_zero` (adds `‖v‖ = 1`; the WiN7
  statement was false). `multivariable_hensel`/`common_root_tfae` omitted with documented blockers.
- [wave3] `Prod.lean` extended, sorry-free: `nondegenerate_iff_discr_ne_zero`,
  `nondegenerate_baseChange` (needs `[IsDomain A] [FaithfulSMul R A]`). `prod_isotropic_iff` is
  FALSE as stated (needs an extra `Q₁.Isotropic ∨ Q₂.Isotropic` disjunct); corrected form recorded.
- [wave3] `HilbertSymbol/Padic.lean` PARTIAL: `hilbertSym_eq_one_of_sol`, `hilbertSym_sq_left/right`,
  `hilbertSym_mul_square_eq`, `zmod_sq_add_sq_eq_one`, `hilbertSym_padicInt_units`,
  `hilbertSym_padic_odd_case00` (both arguments units, `p` odd). Cases `10`/`11`, full odd formula,
  and `HasBilinHilbertSym ℚ_[p]` remain (blocked on p-adic square-class structure); `p = 2` out of scope.
- [wave3] `HasseInvariant.lean` DONE (partial scope), sorry-free: `hasseMinkowskiInvAux` (+ `zero/one/two/three/cons`),
  `hasseMinkowskiInvAux_prod_rank_one`, `hasseMinkowskiInvAux_eq_one_or_neg_one`, `hasseMinkowskiInv` def.
  Well-definedness `eq_of_equivalent` needs the local Hilbert-symbol theory; omitted.
- [env] `lake_check`/`lake build` intermittently fail with unreadable `Mathlib/**/*.olean.private`
  under memory pressure; kill stale `lean`/`lake` (NOT python) and retry.
- [wave4 OOM] Dispatching 4 heavy workers at once OOMed the machine. RECOVERY: run at most ONE
  heavy worker at a time from now on. Salvaged from the aborted workers:
  * `HilbertSymbol/Existence.lean` DONE, sorry-free (Dirichlet/CRT construction of `S`, `T`, `A`, `M`
    and the squareness/valuation lemmas; place-by-place verification deferred — needs the full
    Serre formula).
  * `Prod.lean` extended and clean: corrected `prod_isotropic_iff`
    (`… ↔ Q₁.Isotropic ∨ Q₂.Isotropic ∨ ∃ a ≠ 0, Q₁.represents a ∧ Q₂.represents (-a)`),
    `represents_of_isotropic_nondegenerate`, `exists_ne_zero_represents_of_nondegenerate`,
    `iso_prod_neg`.
  * `HilbertSymbol/Two.lean` was left mid-edit with 8 errors; preserved as
    `HilbertSymbol/Two.lean.partial` (NOT built) for a future session. `Scratch/win7-*.lean`
    foreign sources deleted.
- [next] one-at-a-time: finish odd-`p` `HilbertSymbol/Padic.lean` (`case10/11`, full `padic_odd_eq`,
  `_mul_left`), then 2-adic (resume `Two.lean.partial`), then rank 3/4 and the high-rank induction.
- [wave4] `HilbertSymbol/Padic.lean` extended (clean): all four square-class cases for odd `p` are
  now proved — `hilbertSym_padic_odd_case10` (unit vs valuation-1, = `quadraticChar (ZMod p) (toZMod u)`),
  `hilbertSym_padic_odd_case11` (`= χ(-1)`), `hilbertSym_padic_odd_case11_units` (`= χ(-uv)`), on top
  of `case00`. Remaining: package into the full `hilbertSym_padic_odd_eq` via `a = p^α u` + reducing
  `α,β` mod 2 (`hilbertSym_mul_square_eq`), then `hilbertSym_padic_odd_mul_left`. Roadmap in
  `HANDOFF-hilbertpadic.md`.
- [wave4] odd-`p` Hilbert symbol COMPLETE, sorry-free, built: `padicUnit`, `parityPow`,
  `hilbertSym_padic_odd_eq` (the full Serre formula `(-1)^{αβ(p-1)/2} χ(u)^β χ(v)^α` in
  `parityPow` form), and `hilbertSym_padic_odd_mul_left`. Unconditional
  `HasBilinHilbertSym ℚ_[p]` not added because `mul_left` requires `p ≠ 2`.
- [next] resume the 2-adic case (`HilbertSymbol/Two.lean.partial`), then well-definedness of
  `hasseMinkowskiInv`, then rank 3/4 and the high-rank induction.
- [wave4] 2-adic Hilbert symbol (units) DONE, sorry-free: `HilbertSymbol/Two.lean` proves
  `hilbertSym_padic_two_units : hilbertSym (u:ℚ_[2]) (v:ℚ_[2]) = if u ≡ 1 (mod 4) ∨ v ≡ 1 (mod 4) then 1 else -1`
  for `u v : ℤ_[2]ˣ`, plus `_of_isSquare`, `_of_toZModPow_eq_one`, `_eq_neg_one_of_mod4` and the
  mod-4/mod-8 residue facts. `.partial` removed. Remaining: the full valuation-bearing `two_adic_eq`.
- [next] full 2-adic formula; `hasseMinkowskiInv` well-definedness (`eq_of_equivalent`);
  rank 3 (Legendre descent) and rank 4 (WiN7 `RankFour.lean` port — its prerequisites
  `prod_isotropic_iff`, `iso_prod_neg`, `baseChange_prod_neg`, `exists_rat_with_two_prescribed_hilbertSym`,
  `represents_iff_of_rank_two`, `isotropic_of_rank_three` are now partly in hand / stubbed in `Targets.lean`).
- [wave5] `RatApproximation.lean` DONE, sorry-free: `Rat.approximation` (Dense image of ℚ in the
  product of p-adic spheres) + `approximation'`. `Padics/CommonRoot.lean` DONE, sorry-free
  (`exists_padicInt_solution`, `lift_solutions_to_int_first`, `exists_nontrivial_zero` with the
  `‖v‖ = 1` correction). `HasseInvariant.lean` DONE, sorry-free (`hasseMinkowskiInvAux` +
  `_zero/_one/_two/_three/_cons` + `hasseMinkowskiInv` def + `_eq_one_or_neg_one`).
  `HilbertSymbol/Existence.lean` DONE, sorry-free (Dirichlet/CRT `S`/`T`/`A`/`M` construction;
  `is_unit_ai_of_p_notMem_S` fixed). `Padics/Squares.lean` extended, sorry-free.
- [wave6] `HilbertSymbol/Reciprocity.lean` DONE, sorry-free (LSP-clean; final `lake_check` failed
  only environmentally — RAM below the 900 MB guard floor → random `*.olean.private` read errors;
  not a source error. `lean_verify` on the theorems: axioms `{propext, Classical.choice, Quot.sound}`):
  `almost_all_one`, `finite_nontrivial_hilbertSym`, `hilbertSym_rat_eq_one_of_isSquare_left`,
  `prod_eq_one_of_isSquare_{left,right}` / `prod_eq_one_of_isSquare` = Hilbert reciprocity in the
  square case, and `HilbertReciprocity : Prop` (general Hilbert reciprocity statement; NOT proved —
  needs the full 2-adic formula + quadratic-reciprocity assembly; upstream WiN7 has it `sorry`).
  NOTE: the naive `∏ p, (·)_p = 1` is ill-typed (no `Fintype Nat.Primes`; must be `∏ᶠ`) and FALSE
  without the archimedean factor (`a = b = -1`); the correct form is `(∏ᶠ p, (·)_p) * (·)_ℝ = 1`.
- [wave6] `RankCriteria.lean` DONE, sorry-free, LSP-clean: `Equivalent.isotropic_iff`,
  `hilbertSym_eq_one_iff`, `hilbertSym_right_neg_self`, `hilbertSym_neg_one_mul_self`,
  `hilbertSym_self`, `hilbertSym_self_eq_left_neg_one`, `hilbertSym_left_neg_mul`, `hilbertSym_mul_mul`,
  `weightedSumSquares_isotropic_iff_hilbertSym_eq_one[_']`, `weightedSumSquares_units_coe`,
  `hilbertSym_mul_mul_neg`, `mul_eq_one_iff_eq_of_signs`, `represents_zero_iff_of_rank_three_diag`
  (the diagonal rank-three criterion `⟨a,b,c⟩ isotropic ↔ (-1, -abc) = ε(⟨a,b,c⟩)`).
  File header documents the `hwell` hypothesis standing in for `hasseMinkowskiInv.eq_of_equivalent`.
- [wave6-crash] `HilbertSymbol/Two.lean` was corrupted mid-session by an interrupted worker
  (off-script 2-adic binary-form experiment; 17 errors, incl. 6 `decide`-refuted wrong assumptions).
  RESTORED to the clean sorry-free units classification (lines ≤ 694). The experiment is preserved
  at `Scratch/Two-padic-mixed-experiment.lean.full.bak`: `eps`, `omg`, `parityPow_neg_one_{even,odd}`,
  `toZModPow_two_eq_of_three`, `isSquare_neg_seven`, `hilbertSym_eq_neg_one_of_zmod8`, `repA_*` and
  `repB_*` tables. KEEP: the ε/ω-char definitions and the mod-8 obstruction lemma (valid where the
  mod-8 «no solution» claim holds). 6 `repB_*` `-1` cases fail because a `ZMod 8` solution with a
  unit coordinate exists (e.g. `2x² + 6y² = z²` has `z=0, x=y=1` mod 8): those need a finer argument
  (higher modulus / unit-coordinate condition) or the closed Serre formula `(-1)^{ε(u)ε(v)+α·ω(v)+β·ω(u)}`.
- [next] full 2-adic formula (resume from the backup above); `hasseMinkowskiInv` well-definedness;
  rank 3 (Legendre descent); rank 4 (WiN7 `RankFour.lean` port). Reminder: the resource manager in
  `.opencode/plugins/lake-build-guard.ts` (→ HEAVY/LSP semaphores + 900 MB free-RAM floor, read at
  startup) is ACTIVE since the last restart — iterate with `lean_diagnostic_messages`, one worker per
  file, `lake_check` only as the final confirmation. See `HANDOFF-CONTINUE.md` at the repo root.
- [wave7] parallel wave after the crash; machine health: stale `lean`/`lake` procs (11, then 9) were
  eating all RAM (328 MB free) — killing only `lean`/`lake` restored 4.2 GB; do this whenever
  `lake_check` fails with random `*.olean.private` read errors.
  * `RankThree.lean` DONE, sorry-free, LSP-clean: `weightedSumSquares_fin3_eq`,
    `hilbertSym_neg_mul_of_isotropic`, and `isotropic_of_rank_three` — proved conditional on
    `hloc : HilbertSymLocalGlobal` (all local `(A,B)_v = 1` ⟹ global `(A,B)_ℚ = 1`, i.e. the
    Hasse norm theorem for quadratic extensions). `hloc` is the only missing input; everything else
    (diagonalization, ternary criterion, base change over all `ℚ_[p]`/`ℝ`, transfer back) is done.
    Log: `HANDOFF-rankthree.md`.
  * `HasseInvariantWellDef.lean` DONE, sorry-free, LSP-clean (`lean_verify`: axioms
    `{propext, Classical.choice, Quot.sound}`): `LinearMap.separatingLeft_of_equivalent`
    (unconditional), `hasseMinkowskiInvAux_comp_equiv`, `hilbertSym_prod_eq_of_equivalent`,
    `hasseMinkowskiInvAux.eq_of_equivalent`, `hasseMinkowskiInv.eq_of_equivalent[_weightedSumSquares]`
    — conditional on `hconn` (connectivity of diagonalizations: reindexings + splitting off a common
    rank-one summand with equivalent tails = WiN7 `Chain.lean`, itself 2 `sorry`). `hconn` carries no
    invariant-theoretic info and is non-circular. Log: `HANDOFF-wellDef.md`.
  * full 2-adic formula: worker aborted with no edits (`Two.lean` re-verified clean); RE-QUEUED.
- [blockers] the remaining gaps are now precisely localized: (1) 2-adic closed formula;
  (2) `hconn` = Witt cancellation / chain connectivity (port WiN7 `Chain.lean`);
  (3) `hloc` = Hasse norm theorem (deep; likely out of scope — WiN7 has it `sorry` upstream);
  (4) general (non-diagonal) rank-2/3 criteria via squarefree-units diagonalization.
- [wave8] `Chain.lean` DONE, sorry-free, `lake_check` OK: `Module.Basis.IsContiguous`/`Chain`
  (upstream WiN7 `Chain.lean` has 2 `sorry`), `DiagonalConnectivity` (= exact `hconn` shape),
  `ChainHypothesis` (named genuine residual = `Nonempty (Chain Q b b')`, WiN7 `chainOfNondegenerate`),
  `step_one_eq`, `reflTransGen_step_one_eq`, and **`diagonalConnectivity_false : ¬ DiagonalConnectivity ℝ`**.
  KEY: the diagonal-only `hconn` carried by `HasseInvariantWellDef`/`RankCriteriaGeneral`/`RankCriteria`
  (its `hwell`) is **FALSE** — rank-1 over ℝ, `![1] ~ ![4]` (equivalent) yet `Step 1` relates only equal
  tuples. So those conditional theorems are vacuous as stated; the honest residual is the basis-level
  `ChainHypothesis`. Log `HANDOFF-chain.md`.
- [wave8] `RankCriteriaGeneral.lean` DONE, sorry-free, `lake_check` OK: general `represents_iff_of_rank_two`
  and `represents_zero_iff_of_rank_three` for nondegenerate `Q` with `Basis (Fin n)`, carrying
  `[HasBilinHilbertSym k] [Invertible 2]` + the (now-known-false) `hconn`; plus diagonal reductions,
  `hilbertSym_neg_discr_eq_neg_prod`, `separatingLeft_of_nondegenerate`. Log `HANDOFF-rankgeneral.md`.
- [wave8] 2-adic formula: worker ABORTED AGAIN (no edits; `Two.lean` re-verified clean). Two attempts,
  both empty — do not re-delegate blindly; tackle in-session or from `Scratch/Two-padic-mixed-experiment.lean.full.bak`.
- [wave9] rework onto the basis-level chain (user-directed). Created `BasisChain.lean` (sorry-free,
  LSP-clean): `Module.Basis.IsContiguous`, `Module.Basis.Chain`, `ChainHypothesis` moved out of
  `Chain.lean` to break the import cycle; rewired `Chain.lean` to `import …BasisChain` (still clean,
  no duplication). Updated `HasseInvariantWellDef.lean`'s module doc with a WARNING that its `hconn`
  is FALSE and the three theorems are vacuous as stated.
  **CONCLUSION: the reduction `ChainHypothesis → hasseMinkowskiInvAux.eq_of_equivalent` is BLOCKED.**
  It needs the orthogonal-complement / restriction / Witt-cancellation machinery, which Mathlib 4.33
  lacks (`orthoCompl`, `QuadraticForm.restrict` both absent per `lean_local_search`), the same reason
  upstream leaves `eq_of_equivalent` `sorry`. So the well-definedness results cannot be restated on
  `ChainHypothesis` sorry-free yet. (3 subagent attempts at this rework all aborted with zero output;
  the factoring was done manually.)
- [blockers final] (1) full 2-adic closed formula; (2) invariant well-definedness = needs Witt /
  `orthoCompl` (absent in Mathlib 4.33; true residual is `ChainHypothesis` in `BasisChain.lean`);
  (3) `hloc` Hasse norm theorem (deep, likely out of scope); (4) general rank-2/3 criteria (stated in
  `RankCriteriaGeneral.lean`, vacuous until (2)).
- [wave10 / orchestrated] **A.1 DONE, sorry-free, verified** (`HilbertSymbol/Two.lean`, now 1598 lines):
  `hilbertSym_two_mul_unit`, `hilbertSym_two_mul_two_mul` (the mixed valuation cases, incl. the identity
  `(a,b) = (a,-ab)`), `hilbertSym_padic_two_eq` (Serre's closed formula), `hilbertSym_padic_two_mul_left`,
  and **`instance : HasBilinHilbertSym ℚ_[2]`**. Axioms `{propext, Classical.choice, Quot.sound}` all.
  This was blocker (1) and had defeated three earlier workers; split into three small checkpointed
  subagent tasks (mixed cases → closed formula → multiplicativity) per the plan's small-task rule.
- [wave10] **B.1 DONE** (`QuadraticForm/Restriction.lean`, new, 264 lines, sorry-free, `lake_check` OK):
  `orthoCompl`, `restrict`, `mem_orthoCompl`, `le_orthoCompl{,_orthoCompl}`, `associated_restrict(_eq)`,
  `finrank_add_finrank_orthoCompl`, `orthoCompl_orthoCompl_eq_of_nondegenerate`,
  `restrict_nondegenerate_iff_isCompl_orthoCompl`, `restrict_orthoCompl_span_singleton_nondegenerate`.
  KEY DISCOVERY: the plan's premise was wrong — Mathlib 4.33 **does** have `QuadraticMap.restrict`,
  `QuadraticMap.comp`, `LinearMap.BilinForm.orthogonal` and the whole bilinear orthogonality/finrank
  API; only the quadratic-form packaging was missing. B.1–B.2 were therefore cheap, not XL.
- [wave10] **B.3 (first half) DONE, same file**: `isometryEquivProdOfIsCompl`,
  `isometryEquiv_prod_of_isCompl` (`IsCompl W Wᗮ ⇒ Q ≅ Q|_W ⊗ Q|_Wᗮ`), plus nondegenerate-restrict and
  finrank corollaries — Mathlib has `QuadraticMap.IsometryEquiv`/`prod` but no such splitting lemma.
- [wave10] Mathlib recon (read-only worker, `HANDOFF-witt.md`): Mathlib has NO Hilbert symbol,
  `IsNorm`, Hilbert 90/Kummer, norm-group-index-2 theorem, and no quaternion↔`QuadraticMap` bridge
  (so A.1 had to stay case-based). It also has NO Witt cancellation, NO Witt extension, no
  `LinearMap.BilinForm.prod`, no `IsCompl ⇒ prod` decomposition — the genuine residual in Workstream B.
- [wave10 / infra] Diagnosed the repeated subagent aborts: hard step caps (`lean-prover` 70, now 150;
  `lean-explorer` 30, now 60; `general` 50) plus a silent-empty-final-message mode when the working
  context is large. Worker guidance now mandates appending to the per-task log every ~6 tool calls and
  reading big files narrowly. The new caps take effect after an opencode restart.
- [wave10] **B.3 (Witt layer, first ingredient) DONE** — new `QuadraticForm/Witt.lean` (182 lines,
  sorry-free, LSP-clean, `lake_check` OK): `polar_eq_two_mul_associated`, `map_add/sub_eq_associated`,
  `reflectionLinearMap` + `reflection` (`x ↦ x - 2·(B(x,a)/Q a)·a`) with `_apply`, `associated_`,
  `_involutive`, `_self`, `reflection_isometry : IsometryEquiv Q Q`, and the rank-one transitivity
  **`exists_isometryEquiv_of_Q_eq : Q v = Q w ≠ 0 → ∃ φ : IsometryEquiv Q Q, φ v = w`**. (Note: the
  naive reflection `x - (B(x,a)/Q a)·a` is wrong — it kills `a` and is not an isometry; the factor `2`
  is required.) This is the base of Witt's extension/cancellation.
- [wave10] **Norm criterion DONE** — new `HilbertSymbol/Norm.lean` (75 lines, sorry-free, clean):
  `hilbertSym_eq_one_iff_sol` and `hilbertSym_eq_one_iff_isNorm`
  (`hilbertSym a b = 1 ↔ ∃ t : QuadraticAlgebra k b 0, a = QuadraticAlgebra.norm t`, for `a,b ≠ 0`,
  `b` nonsquare). Confirms Mathlib 4.33 has `QuadraticAlgebra`/`norm` with norm form `x² - b y²`
  (WiN7's `hilbertSym.eq_one_iff`). This is the entry point for a uniform (non-case-based) proof of
  bimultiplicativity and for Hilbert reciprocity (A.2).
- [wave10 / status] Workstreams A.1, B.1, B.2 complete and verified; B.3 has reflections +
  rank-one transitivity + splitting isometry. Remaining: **A.2** (global product formula),
  **B.3** (Witt cancellation/extension), **B.4** (`ChainHypothesis`, WiN7 `exists_const` +
  `chainOfNondegenerate`), **B.5** (invariant well-definedness), then C/D/E. Next natural step:
  build `HasBilinHilbertSym`-free bimultiplicativity from `Norm.lean` + the index-2 norm-group fact,
  or start A.2 with the odd/2-adic formulas now in hand.
- [wave11] **B.3 proper DONE (rank-one Witt cancellation)** — `QuadraticForm/Witt.lean` now 266 lines,
  sorry-free, clean, `lake_check` OK: `associated_isometryEquiv_map` (an isometry of `Q` preserves
  `Q.associated`), `isometryEquivOrthoComplSpanOfQeq`, and
  **`isometryEquiv_orthoCompl_span_of_Q_eq`** (`Q v = Q w ≠ 0` `⟹` `Q|_{⟨v⟩ᗮ} ≅ Q|_{⟨w⟩ᗮ}`), built on
  `exists_isometryEquiv_of_Q_eq`. Axioms `{propext, Classical.choice, Quot.sound}`. Remaining in B.3:
  general Witt cancellation/extension by induction on `finrank` (stretch, not started).
- [wave11] **A.2 Phase 1 DONE** — `HilbertSymbol/Reciprocity.lean` now 514 lines, sorry-free, clean:
  `hilbertProd` (the global product), `IsGen` (= `{-1} ∪ primes`), multiplicativity/inverse/square
  lemmas for `hilbertProd`, `exists_gen_prod_mul_sq`, and
  **`hilbertReciprocity_of_generators : (∀ g h, IsGen g → IsGen h → hilbertProd g h = 1) → HilbertReciprocity`**
  — the reduction of reciprocity to the four generator cases. `HilbertReciprocity` itself is NOT yet
  proved; Phase 2 (the `(-1,-1)`, `(-1,p)`, `(p,p)`, `(p,q)` cases via quadratic reciprocity and the
  supplementary laws) is   recorded as a `TODO` block. Note `hilbertProd_gen_left`, `hilbertProd_eq_one`
  already handle the square/generator-left reductions.
- [wave12] **A.2 COMPLETE (Hilbert reciprocity proved)** — `HilbertSymbol/Reciprocity.lean` now 1139
  lines, sorry-free, clean: **`theorem hilbertReciprocity : HilbertReciprocity`** (line 1127),
  axioms `{propext, Classical.choice, Quot.sound}`. All four generator cases are proved
  (`hilbertProd_neg_one_neg_one`, `hilbertProd_neg_one_prime`, `hilbertProd_prime_self`,
  `hilbertProd_two_prime`, `hilbertProd_prime_prime`), the `(p,q)` case being genuine quadratic
  reciprocity (`legendreSym.quadratic_reciprocity`) plus the 2-adic sign. This is the last of the
  "global" Hilbert-symbol inputs.
- [wave12] **B.3 COMPLETE** — `QuadraticForm/Witt.lean` now 486 lines, sorry-free, clean:
  `exists_isometryEquiv_of_isometric_embeddings` (**Witt extension**: two isometric embeddings of a
  nondegenerate space into `V` differ by an ambient isometry, by strong induction on `finrank`),
  `exists_isometryEquiv_of_Q_eq_fixing`, and
  **`isometryEquiv_orthoCompl_of_isometryEquiv_restrict`** (general **Witt cancellation**: isometric
  nondegenerate restrictions have isometric orthocomplements). Axioms
  `{propext, Classical.choice, Quot.sound}`.
- [wave12 / WiN7 finding] Fetched WiN7's actual `QuadraticForm/Chain.lean` and `RankFour.lean`.
  WiN7's `Chain.basis_isContiguous` compares `basis ⟨i,_⟩` with `basis ⟨i,_⟩` (SAME index), hence is
  **vacuous**; so their `chainOfNondegenerate` is trivially satisfiable and its port would not help.
  Our `BasisChain.lean`'s `ChainHypothesis` uses the meaningful *consecutive* contiguity and is the
  genuine content (Serre IV.1 Thm 2) — B.4 must prove that stronger statement (now feasible with
  Witt extension). `exists_const` (WiN7) additionally assumes two "discriminant-vanishing" hypotheses
  `h1`, `h2` that the scratch reference had omitted.
- [wave13] **B.4 first lemma DONE** — `Module.Basis.exists_const` proved AS STATED in `BasisChain.lean`
  (now 249 lines; appended, sorry-free, `lake_check` OK; axioms `{propext, Classical.choice,
  Quot.sound}`). No `[Infinite k]` needed and WiN7's `h1`/`h2` are exactly what make it work (they
  force `Q b₁ = Q b'₁ = Q b'₂`, after which the discriminant polynomial cannot vanish at `x ∈ {0,1,-1}`).
  Import added: `Pptc.HasseMinkowski.QuadraticForm.Witt`. Remaining in B.4: the genuine
  `chainOfNondegenerate` (our consecutive-contiguity `ChainHypothesis`).
- [wave13 / PLAN CORRECTION] **C.0 as written in `Plan-next.md` is mathematically INVALID.** A worker
  investigated `HilbertSymLocalGlobal` and showed that under its hypotheses every local factor is
  already `1`, so Hilbert reciprocity's conclusion collapses to the tautology `1 * 1 = 1`; reciprocity
  gives **no** information about the global symbol `(A,B)_ℚ`. The target is exactly Legendre's theorem
  / the Hasse norm theorem for quadratic extensions of ℚ (WiN7 has it as `sorry`); the global conic
  symbol also fails to be multiplicative over ℚ (e.g. `(2,3)_ℚ=(2,5)_ℚ=(2,15)_ℚ=-1`), so the
  norm-group-index-2 shortcut is out too. A real proof needs Legendre descent (geometry of numbers) or
  global class field theory. New declarations in `RankThree.lean` (now 241 lines, sorry-free):
  `RankThreeDiagonalLocalGlobal` and `hilbertSymLocalGlobal_iff_rankThreeDiagonal` (pins the gap to
  Legendre's theorem) plus `hilbertProd_eq_one_of_local_eq_one` (formal witness that reciprocity is
  vacuous under the target's hypotheses). `Plan-next.md` C.0 has been updated accordingly.





