# HANDOFF — Pptc/TotallyReal/Certificate.lean (mechanical fixes + b-lift + exists_chain_roots)

Goal (Lean syntax):
```
-- (1) clear ~20 mechanical errors (rw before unfolding defs, "no goals to be solved")
-- (2) ChainB.yvec_conicPt, ChainB.yvec_V, chainBLift_yvec
-- (3) exists_chain_roots (Lemma C, PLAN 2.5): sorry -> proof (Continuity helpers first)
```
Target file: `pptc/Pptc/TotallyReal/Certificate.lean`, decls
`yConicY_add_left`, `yConicY_smul_left`, `yConicY_add_smul_eq`, `yBdotY_add_left`,
`psumY_cube_eq`, `psumY_one_eq`, `chainConicPt_on_conic`, `yNBY_add_left`,
`yNBY_smul_left`, `yNBY_sub_left`, `chainProjN_mem_N`, `psumY_13_line`,
`ChainB.yvec_D`, `ChainB.yvec_conicPt`, `ChainB.yvec_V`, `chainBLift_yvec`,
`exists_chain_roots`.

Plan: use ONE uniform style for the unfolding pattern
(`simp only [...] <defs>; rw [...]` or explicit `unfold` list), then the b-lift,
then the IVT argument for exists_chain_roots.

## Log
- STYLE CHOSEN: `simp only [<defs>, Pi.add_apply / Pi.smul_apply / Pi.sub_apply, smul_eq_mul]` FIRST, then `rw [hsum]`; trailing `simp only` deleted.

## Session 4 (re-proof of the algebra section after the restore)
Goal: the 16 `sorry`s at lines 116-216 (`chainStep3Cleared_eq`, `chainStep3Cleared_eq'`,
`yConicY_add_left`, `yConicY_smul_left`, `yConicY_add_smul_expand`, `yConicY_add_smul_eq`,
`yBdotY_add_left`, `psumY_cube_eq`, `psumY_one_eq`, `yConicY_sub_smul`,
`chainConicPt_on_conic`, `yNBY_add_right`, `yNBY_sub_right`, `yNBY_smul_right`,
`chainProjN_mem_N`, `psumY_13_line`). Plan: key/sum_congr/simp only/rw, as in session 1.
- s4 step 1: orientation done. Defs re-read (YSpace 752-785, Newton 256). `Finset.sum_mul`
  used to pull a scalar out (`∑ f i * a = (∑ f i) * a`), then `mul_comm` + `rfl`.
- s4 step 2: **`yConicY_add_smul_eq` is FALSE as stated** (see entry below). Not proved.
- s4 step 3: **`Finset.sum_congr` needs the DOUBLE-binder hypothesis**:
  `Finset.sum_congr rfl (fun i _ => key i)` — `rfl` first, then `∀ x ∈ univ, …`.
  `Finset.sum_congr rfl key` with a single-binder `key` is a type error.
- s4 step 4: **`Finset.sum_add_distrib`/`sum_sub_distrib`/`sum_mul` all point the OTHER
  way** from what one wants here: they rewrite `∑(f+g) → (∑f)+(∑g)` and
  `(∑f)*a → ∑(f*a)`. To *build* the unfolded RHS from a pointwise `key` you must
  `Finset.sum_congr rfl` FIRST, then distribute, and to pull a scalar out you need
  **`← Finset.sum_mul`** with the scalar as the syntactically LAST factor of the
  summand (else the metavariable `?a` tries to capture the bound index and unification
  fails). `← Finset.mul_sum` does not work for `3 * s * (∑ …)` (not a single `Mul`).
- s4 step 5: `simp only […defs, Pi.add_apply, …]` then `exact hsum` works if hsum's
  stated RHS is *character-identical* to the unfolded goal RHS. `rw [hsum] <;> ring`
  is the robust alternative when the two differ by commutativity/associativity only.
- s4 step 6: 15/16 proved; LSP diagnostics clean. Waiting on `chainProjN_mem_N`
  (`mul_div_cancel₀`'s pattern in this Mathlib is `b * (a / b)`, not `a * b / b`).

## Session 4 — FINAL
- chainStep3Cleared_eq: DONE — `hpt` (pointwise, `field_simp [hden]`) then `key` via a `calc`
  through `hpt i`, then a 2-step `calc` hsum (`sum_congr` + `← Finset.sum_mul`), then
  `simp only [chainStep3Cleared, psumY, psumFinY]; rw [hsum, mul_comm]`.
- chainStep3Cleared_eq': DONE — one line, `exact chainStep3Cleared_eq hden` (defeq on `chainStep3`).
- yConicY_add_left: DONE (calc hsum; `sum_congr` then `sum_add_distrib`; `exact hsum`).
- yConicY_smul_left: DONE (`← Finset.sum_mul` + `ring`).
- yConicY_add_smul_expand: DONE (2 × `sum_add_distrib`, 2 × `← sum_mul`, `ring`).
- yConicY_add_smul_eq: **STUCK — the statement is FALSE.** `sorry` kept, WARNING doc comment
  added with an exact counterexample. Independently confirmed with Wolfram
  (backend `wolfram_WolframLanguageEvaluator`, exact `Integer` arithmetic):
  `n = 3`, `P = ![1,0,-1]`, `u = ![1,0,0]`, `s = 1` gives
  `yNBY P P = 0` (so `hN` HOLDS) while `yConicY P u = 1` and `yConicY P (u + 1 • P) = 3`.
  Root cause: `hN` kills the `s²·⟨P,P,P⟩` term of `yConicY_add_smul_expand` but NOT the middle
  term `2s·yNBY P u`. **The hypothesis that would make it true is `yConicY P P = 0`
  (= `psumY P 3 = 0`), not `yNBY P P = 0`.** A one-line change of `hN` fixes it; left
  unchanged because statement edits are out of scope.
- yBdotY_add_left: DONE. psumY_cube_eq: DONE (3 × `sum_add_distrib`, 3 × `← sum_mul`, `ring`).
- psumY_one_eq: DONE. yConicY_sub_smul: DONE (`sum_add_distrib` + `sum_sub_distrib`, 2 × `← sum_mul`).
- chainConicPt_on_conic: DONE — `simp only [chainConicPt]; rw [yConicY_sub_smul, hq₀]; field_simp [hden] <;> ring`.
- yNBY_add_right / yNBY_sub_right: DONE. yNBY_smul_right: DONE.
- chainProjN_mem_N: DONE — `rw [chainProjN, yNBY_sub_right, yNBY_smul_right, div_mul_cancel₀ _ hden]; ring`.
  NOTE `div_mul_cancel₀` (not `mul_div_cancel₀`) is the one stated as `a / b * b = a` here.
- psumY_13_line: DONE — `refine ⟨?_, ?_⟩`; `rw [psumY_one_eq, …]` / `rw [psumY_cube_eq, hP3, hN, hQ, hv3]; ring`.
- FINAL `lake_check Pptc/TotallyReal/Certificate.lean`: **exit 0, no errors.** In my range the only
  remaining diagnostics are the intended `sorry` at 235 and one `unnecessarySeqFocus` style
  warning at 329. All other warnings/sorries (572, 1068, 1082, 1477, 1703, 1723, 1741, 1755,
  1771, 1813, and the unused-`hden`/unused-simp-arg ones) are the other agents' ranges.
- `lean_verify` (axioms = propext / Classical.choice / Quot.sound, no `sorryAx`) checked on
  `psumY_13_line`, `chainStep3Cleared_eq'`, `chainConicPt_on_conic`, `yConicY_add_smul_expand`.
- NO new helper lemmas were added; every proof is self-contained in the theorem body.
- yConicY_add_left / yConicY_smul_left / yConicY_add_smul_expand / yBdotY_add_left / psumY_cube_eq / psumY_one_eq / yConicY_sub_smul: DONE (style above; 7 sites)
- yNBY_add_left/_sub_left/_smul_left: FALSE statements (yNBY is quadratic in arg 1). REPLACED by yNBY_add_right / yNBY_sub_right / yNBY_smul_right (same key/hsum style). Documented.
- chainProjN_mem_N: DONE (rw [chainProjN, yNBY_sub_right, yNBY_smul_right]; key: field_simp [hden]; ring)
- psumY_13_line: was FALSE - needed S₁(v)=0. ADDED hypothesis (hv1 : psumY v 1 = 0), doc comment explains. Not used elsewhere in the project.
- chainProjN_B / yvec_P / yvec_D / yvec_conicPt: DONE (deleted stray trailing tactics; simp already closed)
- ChainB.yvec_D: DONE (simp only [chainW1, chainW3, chainWt] closes; no rfl needed)
- ChainB.yvec_V: DONE (rw [yvec_conicPt _ _ _ h2', yvec_P, yvec_Q0 αs I lam x h1, yvec_D αs I lam mu h1])
- diagnostics 1..1450: 0 errors.
- ChainB.yvec_conicPt: DONE (existing proof was complete; deleted stray `rfl`)
- chainBLift_yvec: DONE (verified: axioms = propext/Classical.choice/Quot.sound, no sorryAx)
- ChainB.yvec_V: DONE (verified no sorryAx)
- Continuity helpers added before Lemma C: continuous_yNBY, continuous_yConicY,
  continuous_yBdotY, continuous_chainStep1' (all `Continuous`, no sorry). NOT yet
  type-checked: the other agent is rebuilding Pptc/TotallyReal/YSpace (its .olean was
  temporarily missing) so the LSP reports "Imports are out of date".
- exists_chain_roots: STUCK/FALSE. The statement is FALSE as written (h2/h3/h4 are asserted
  only at the CENTRE values of the earlier params, but the conclusion needs a step-k root on
  top of a step-(k-1) root that moves with I; shrinking eps1 does not close the gap). Added a
  long WARNING doc comment with the counterexample shape and the two possible fixes
  (uniformity over the box, or simplicity + IFT). `sorry` left in place as instructed.
- open question for the caller: `exists_open_good7/8` (other agent's range) are stated with
  NO hypotheses at all, so they are false for the same reason; they cannot be derived from
  `exists_chain_roots` as stated.
- Continuity helpers: ABANDONED (documented in the `exists_chain_roots` WARNING instead).
  Root cause: `Continuous.comp`'s result is NOT definitionally recognised against the
  target (Function.comp does not unfold at the defeq check), so every composition must be
  `have h := a.comp b; simpa only [Function.comp_apply] using h` with all args typed; and
  the elaborator's postponed-metavariable handling then makes the outcome depend on the
  elaboration order of neighbouring `have`s — byte-identical proofs passed in one run and
  failed in the next. Not worth committing. Scratch file used for the experiment:
  %TEMP%\opencode\contcheck.lean (deleted; it mirrored the defs and imported only Mathlib).
- FINAL lake_check Pptc/TotallyReal/Certificate.lean: **exit 0, no errors**. Warnings only:
  pre-existing `sorry`s (231, 241, 374=yConicY_add_smul_eq, 917=exists_chain_roots, and the
  other agent's 1005-1657 range), unused `hden` at 1365/1458 and unused simp arg at
  1373/1466 (pre-existing lines, not mine).
- NOTE: a concurrent agent had Pptc/TotallyReal/YSpace.lean in a NON-COMPILING state for
  ~20 min (its .olean deleted repeatedly), which blocked LSP diagnostics and lake_check on
  Certificate.lean. Coordinate with it before re-checking.

## Session 2 (exists_chain_roots, re-stated TRUE by orchestrator)
Goal: `exists_chain_roots` in `pptc/Pptc/TotallyReal/Certificate.lean`, plus continuity
helpers ABOVE it. Plan: per-coordinate `Continuous` lemmas first (explicitly typed
statements, each its own theorem), then an "IVT in a closed box" helper, then assemble.
- session2 step 1: file has 0 errors; statement on disk is a HYBRID (binders `c₁…eps₄` Unicode
  but h2/h3/h4/hden1/hden2 quantify over ASCII `c1 c2 c3`, which are implicit auto-bound
  variables). PLAN: prove a helper `exists_chain_roots_box` with Unicode throughout, then
  `exists_chain_roots` = one `exact` with `c1 := c₁, c2 := c₂, c3 := c₃` by unification. So
  the existing statement is NOT edited.
- session2 step 2: plan settled. IVT is 1-D (earlier roots are fixed once I is fixed);
  uniformity in I over a compact parameter box via a TUBE LEMMA helper built from
  `ContinuousAt` + `Filter.Eventually` + `𝓝` basis for products + `IsCompact` finite
  subcover. Stricter-than-strict boxes avoided by shrinking eps_k top-down (step 1 needs
  no uniformity at all since it has no earlier parameter).
- session2 step 3: BLOCKER ~10min. `Pptc/TotallyReal/YSpace.olean` deleted by the concurrent
  YSpace agent, so ALL diagnostics on Certificate.lean return
  "diagnostics_unavailable: Lean did not finish". Worked around by running
  `lake build Pptc.TotallyReal.YSpace` myself (one narrow target).
- session2 step 4: MATH SETTLED. (a) IVT is 1-D only. (b) shrink radii `d_k` in the order
  step1, step2, ...; step 1 needs no uniformity (no earlier parameter) so `d1` is free
  (bounded only by the denominator openness from hden1 => NON-circular). (c) for step k,
  `h_k` is uniform on the whole OPEN box, so the signs at `c_k ∓ eps_k` hold on ANY closed
  sub-box `K_1 × … × K_{k-1}` with `d_j < eps_j` => `d_k` is free, no uniform margin needed.
  (d) the ONLY thing needing care: to force the step-(k-1) root into the CLOSED box `K_{k-1}`
  I IVT on `[c_{k-1}-d_{k-1}, c_{k-1}+d_{k-1}]`, which needs the sign change at
  `c_{k-1} ∓ d_{k-1}` UNIFORMLY over `K_{k-2} × …` — that uniformity needs a uniform
  margin over a compact box, i.e. `IsCompact` + "positive continuous ⇒ uniformly positive".
  (e) IVT on `[a,b]` with `f a < 0 < f b` returns a root in the OPEN interval (endpoints ≠ 0),
  so `|· - c_k| < eps_k` is automatic. `f` must be continuous on the closed interval.
- session2 step 5: the one genuinely uncertain ingredient is the TUBE LEMMA
  (`∃ U open ∋ x₀, ∀ u ∈ U, ∀ k ∈ K, f u k ≠ 0` for compact `K`), which needs the
  product-neighbourhood decomposition `T ∈ nhds (x₀,k) → ∃ A B, A.prod B ⊆ T`.
  Probing for its Mathlib name next; isolating it in ONE small theorem so it can be swapped.
- session2 step 6: added imports to Certificate.lean (allowed, in my region):
  Mathlib.Topology.Order.IntermediateValue, Mathlib.Topology.Algebra.Order.Field,
  Mathlib.Topology.Separation.Basic, Mathlib.Topology.ContinuousFunction.Bounded.
- session2 step 7: YSpace.lean went BROKEN again (other agent). Worked around by rebuilding
  it once it went green; it has oscillated.
- session2 step 8: **TOOLKIT CONFIRMED** (all verified by `lake env lean`; probe removed).
  Names/signatures for this Mathlib build (Lean 4.33 / Mathlib v4.28-ish):
  * `mem_nhds_prod_iff : s ∈ 𝓝 (x,y) ↔ ∃ u ∈ 𝓝 x, ∃ v ∈ 𝓝 y, u ×ˢ v ⊆ s` (use `.mp`)
  * `mem_nhds_iff : s ∈ 𝓝 a ↔ ∃ t ⊆ s, IsOpen t ∧ a ∈ t` (use `.mp`)
  * `IsOpen.mem_nhds : IsOpen s → a ∈ s → s ∈ 𝓝 a`
  * `IsCompact.elim_finite_subcover (hc : IsCompact s) (f : ι → Set α)
      (hf : ∀ i, IsOpen (f i)) (hcover : s ⊆ ⋃ i, f i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, f i`
  * `IsCompact.exists_forall_le' (h : IsCompact s) (hf : ContinuousOn f s)
      (h0 : ∀ x ∈ s, 0 < f x) : ∃ d > 0, ∀ x ∈ s, d ≤ f x`  -- `f` is IMPLICIT
  * `ContinuousOn.continuousAt (hf) (h : s ∈ 𝓝 a) : ContinuousAt f a`  (2nd arg is nhds!)
  * `ContinuousAt.eventually_ne (hf : ContinuousAt f a) (hne : f a ≠ c) :
      (f ⁻¹' {y | y ≠ c}) ∈ 𝓝 a`   (in Mathlib.Topology.Separation.Basic)
  * `ContinuousOn.div (hf) (hg) (h : ∀ x ∈ s, g x ≠ 0) : ContinuousOn (f / g) s`
  * `continuous_finsetSum (s : Finset ι) (h : ∀ i ∈ s, Continuous (f i)) :
      Continuous fun a => ∑ i ∈ s, f i a`
  * `intermediate_value_Icc (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
      Icc (f a) (f b) ⊆ f '' Icc a b`  -- apply to `hz : 0 ∈ Icc (f a) (f b)`
  * `continuous_apply`, `continuous_fst`, `continuous_snd`, `mem_nhds_iff`
  * DOES NOT EXIST: `IsCompact.exists_forall_ge/le/lt_add`, `IsCompact.isLeast`,
    `isOpen_setOf_ne`, `ContinuousAt.eventually_gt/lt`, `isOpen_setOf_ne`. Use
    `eventually_ne` and `{y | y ≠ 0}` instead of the latter.
- session2 step 9: imports added: IntermediateValue, Algebra.Order.Field, Separation.Basic,
  Order.Compact. (`Mathlib.Topology.ContinuousFunction.Bounded` does NOT exist in this build.)

## !! URGENT — FILE DAMAGE, session 2 !!
- **I DESTROYED `pptc/Pptc/TotallyReal/Certificate.lean`**: a PowerShell line-filter script ran
  with `$start = -1` (the `section Probe` marker had already been removed by an earlier
  script), so the filter deleted **lines 0–1031** of the file. The file is now TRUNCATED:
  it begins part-way through, in the middle of the Lemma C region. There is no git repo
  (`C:\dev\Powerpoint\lean` is not a git repository), so `git checkout` cannot restore it.
- **What is lost**: the file header/imports through the whole of the algebra section
  (`chainStep1`..`chainStep4`, `yConicY_add_left`, `yConicY_smul_left`,
  `yConicY_add_smul_expand`, `yConicY_add_smul`, `yConicY_add_smul_eq`,
  `yBdotY_add_left`, `psumY_cube_eq`, `psumY_one_eq`, `yConicY_sub_smul`,
  `chainConicPt_on_conic`, `yNBY_add_right/_sub_right/_smul_right`, `chainProjN_mem_N`,
  `psumY_13_line`, the `ChainYInputs` abbrev/namespace/accessors, `chainP`, `chainWt`,
  `chainW1..3`, `chainQ0`, `chainD`, `chainV`, `chainY`, `chainStep1'..4'`, `ChainGood`).
- **What survives**: from old line 1032 on, i.e. the `/-! ### Lemma C` doc comment, the
  (ASCII/Unicode mixed) `exists_chain_roots` statement with its `sorry`, and everything from
  `/-! ### The rational certificates` onwards (centre7*/centre8*/exists_open_good7/8) and the
  ChainB / step-polynomial region — i.e. the other three agents' ranges are INTACT.
- **RECOVERY**: the lost 1032 lines have to be re-entered (they are all reproduced in the
  transcript of this session, and `chainStep3Cleared_eq` / `chainStep3Cleared_eq'` /
  `yConicY_add_smul_eq` in them were `sorry`s anyway). A compiled `Certificate.olean` from
  22:46 still exists under `.lake/build/lib/lean/Pptc/TotallyReal/`, and
  `HANDOFF-totallyreal-certificate.md` (earlier session) records which lines were DONE.
  The exact loss is lines 1–1031 of the pre-session-2 file.
- sorry, this is my error; I should have used the `edit` tool with a verified anchor instead
  of a positional line filter.

## Session 3 (me, the eight `centre7*` / `centre8*` numerical lemmas)
Goal: `centre7_solves/denom1/denom2/inj/signs` and the `centre8` twins, all in
`pptc/Pptc/TotallyReal/Certificate.lean` lines 999-1187. Plan: exact `norm_num` on the
ℝ-valued step functions, with Wolfram (exact `Rational`) as the independent check.

- START. Log of Wolfram verification of the plan's numbers (exact Rational arithmetic,
  backend = wolfram_WolframLanguageEvaluator; no python/py on this box).
- **CRITICAL: `centre7_solves` and `centre8_solves` are FALSE, and so are
  `centre7_signs` / `centre8_signs`.** Root cause located exactly, see below.
  * `centre7roots.2.2.2` (= -9136536/1150016105) and `centre8roots.2.2.2`
    (= -160325/27427952) are NOT roots of `chainStep4'`; the true root is `-1` in
    both cases. At kappa = -1, `chainStep4' = 0` AND
    `chainY centre7 0 1/2 (8064/617) (-1) = ![1,-1,2,-2,3,-3,0] = beta*` and
    `chainY centre8 0 5/3 (-5322/2915) (-1) = ![1,2,3,4,-1,-2,-3,-4] = beta*`
    (matching the two docstrings).
  * The plan's kappa_0 is the root of the step-4 polynomial computed with the
    DENOMINATOR-CLEARED conic point `v* = <P,d,d>*v = q0*<P,d,d> - 2*<P,q0,d>*d`
    (i.e. the vector inside `chainStep3Cleared`), instead of `chainV`. Verified:
    `B*v == vclear` with `B = <P,d,d>`, and `sum (P + kapPlan * vclear)^5 = 0` exactly,
    for both n = 7 and n = 8.
  * Confirmed by the plan's own numbers: its stated step-4 derivative
    `-5750080525/761378` is exactly `d/dk sum (P + k*vclear)^5` at kappa_0, not of the
    true step 4. Steps 1 and 2 are untouched: d/dlam step1|0 = -582 and
    d/dx step2|_{1/2} = 21595/111, both matching the plan's derivative list to the digit.
  * The sign claims are separately wrong (radius 1 is too big / directions reversed):
    n=7 step1(-1) = +2388 (claim: < 0), step3(mu0+1) < 0 (claim: > 0),
    step4(kap-1) > 0 (claim: < 0). n=8 step1(-1) = +252 and step1(1) = -144
    (claim: < 0 <), step4(kap-1) > 0 (claim: < 0). The plan's own step-1 derivative
    -582 < 0 already contradicts `step1(0-1) < 0 < step1(0+1)`.
  * I am instructed not to change `centre*roots` and not to change any statement, so
    the four unprovable lemmas stay `sorry` with a WARNING doc comment recording the
    exact correct value (`-1`) and the failing clauses. Reporting loudly to the caller.
- centre7_denom1: DONE — `norm_num [yNBY, ymoment2Y, psumY, psumFinY, chainP, ChainYInputs.a,
  ChainYInputs.b, centre7, centre7roots, centre7a, centre7b, centre7g, Fin.sum_univ_succ]`.
  Value 244, matches the plan.
- centre8_denom1: DONE — same one-liner with `centre8*`. Value 71/2, matches the plan.
- centre7_denom2: DONE — `norm_num [yBdotY, ymoment3Y, yNBY, ymoment2Y, psumY, psumFinY,
  chainProjN, chainD, chainW1, chainW3, chainWt, chainP, ChainYInputs.a, ChainYInputs.g,
  ChainYInputs.w1, ChainYInputs.w3, centre7, centre7roots, centre7a, centre7b, centre7g,
  centre7w1, centre7w3, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
  smul_eq_mul]`. Value 1150016105/9136536.
- centre8_denom2: DONE — same with `centre8*`. Value 27427952/160325.
  **KEY TRAP (cost me ~15 steps): the `![...]` literal defs of the *data* vectors
  (`centre7a`, `centre7b`, `centre7g`, `centre7w1`, `centre7w2`, `centre7w3`) must appear
  EXPLICITLY in the `norm_num [...]` simp set.** Otherwise simp expands the
  `∑ i : Fin n, _` (via `Fin.sum_univ_succ`) but the `Fin.cons` applications at the
  resulting indices never reduce, and norm_num silently leaves the goal unsolved.
  `ChainYInputs` as a bare *namespace* in the simp set does nothing either — list
  `ChainYInputs.a`, `.b`, `.g`, `.w1`, `.w2`, `.w3` individually.
- centre7_solves / centre8_solves: STUCK — statement is FALSE (see the CRITICAL entry).
  `sorry` kept, WARNING doc comment added.
- centre7_signs / centre8_signs: STUCK — statement is FALSE (3 of 8 clauses each).
  `sorry` kept, WARNING doc comment added with the failing clauses and their values.
- centre7_inj / centre8_inj: STUCK — statement is TRUE, `sorry` kept, but a route note is
  in the doc comment. What was established:
  * `fin_cases` IS available (no extra import) and `norm_num [centre7a]` after it does
    evaluate `![...] ⟨k, h⟩`; 49 goals for n = 7, 64 for n = 8.
  * Brute force (`fin_cases i <;> fin_cases j <;> norm_num [full chain] at hij`) blows the
    200000-heartbeat budget after ~12 goals, ~15 s per goal.
  * The three projections are TRIVIAL: `yNBY (chainP centre7 0) centre7w1 = = centre7w2 =
    = centre7w3 = 0` (same for n = 8), each a single cheap `norm_num`. So
    `chainProjN P g wⱼ = wⱼ`.
  * `yBdotY P (chainQ0 …) (chainD …) = 0` too, so `chainV centre7 0 (1/2) (8064/617) =
    chainQ0 centre7 0 (1/2) = w₁ + x₂w₂ = (-6,-5,3,2,3,-4,7) = v*` — the "second
    intersection" is DEGENERATE at both centres. Same for n = 8 with v* = (-5,-4,-1,-5,2,6,4,3).
  * Hence `chainY = a + κ₀ (w₁ + x₂ w₂)`, and with `κ₀ = -1` the output is exactly β*.
  * The remaining obstacle is only the order in which `simp only` unfolds `chainProjN`
    relative to rewriting with the `yNBY … wⱼ = 0` facts; `ring` then closes.
- FINAL lake_check Pptc/TotallyReal/Certificate.lean: **exit 0, no errors**. Warnings only:
  the remaining `sorry`s (mine: 1091 centre7_solves, 1163 centre7_inj, 1211 centre7_signs,
  1295 centre8_solves, 1331 centre8_inj, 1354 centre8_signs; others' at 235, 245, 378, 981,
  1408, 1714-1838) and the pre-existing unused-`hden`/unused-simp-arg warnings at 1546/1554
  and 1639/1647.
- SESSION 4 (me: step polynomials + odd Tschirnhaus). START: 7 targets exists_step1_poly, exists_step2_poly, exists_step3_poly, exists_step4_poly, stepRoots_Pconstructible, chainBLift_Pconstructible, exists_oddTschirnhaus at lines 1128-1264, all sorry. Plan: psumY_line_poly for 1 and 4; binomial expansion of yConicY for 2; explicit triple-sum expansion for 3; root_Pconstructible_le_six_coeffs for 5; yBdot/yConicB/yNB_Pconstructible for 6; exists_open_good7/8 + exists_b_Pconstructible_near for 7.

## Session 4 (me again: the eight centre7*/centre8* lemmas, now that kappa0 = -1)
- session4 step 1: KEY WIN. A single giant
  `refine <_,?_,?_,?> <;> norm_num [chainStep1', chainStep1, chainStep2', chainStep2,
  chainStep3', chainStep3, chainStep4', chainStep4, psumY, psumFinY, yConicY, yNBY, yBdotY,
  ymoment2Y, ymoment3Y, chainProjN, chainConicPt, chainP, chainQ0, chainD, chainV, chainY,
  chainW1, chainW2, chainW3, chainWt, ChainYInputs.a/.b/.g/.w1/.w2/.w3, centre7, centre7roots,
  centre7a, centre7b, centre7g, centre7w1, centre7w2, centre7w3, Fin.sum_univ_succ,
  Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`
  closes ALL FOUR clauses of centre7_solves (verified with lean_multi_attempt, no timeout).
  So the previous session's heartbeat trouble was the plan's kappa; at kappa0 = -1 the numbers
  stay small and no denominator-clearing detour is needed.
- session4 step 1 note: the previous agent's `Fin 3` `match` worry is unfounded - chainWt is
  in the same simp set as chainW1/2/3 and simp closes it.
- session4 step 2: centre7_solves / centre8_solves: WRITTEN (one big norm_num per clause, split over
  8 lines to respect the 100-char linter). diagnostics on 495-760: 0 errors.
- session4 step 3: SIGN VALUES obtained (backend wolfram_WolframLanguageEvaluator, exact Rationals;
  two Wolfram gotchas: P is a PROTECTED symbol in Mathematica - use p; and p.p is ONE symbol
  named "p.p", not the dot product - use Dot[p,p]; also Total[scalar] is a no-op, use Plus @@).
  * n=7, radius 1: (+2388, +252, -157.5298, +231.5693, -0.0761571, -0.0181318, 0, 0)
  * n=7, radius 1/3: (+358.6667, -65.3333, -60.73655, +68.96315, -0.07998354, +0.24283831,
    +59.25926, -331.85185)  <-- ALL EIGHT STRICT
  * n=8, radius 1: (+252, -144, -169.59, +52.5049, -27.91829, +1.776126, +9000, 0)
  * n=8, radius 1/3: (+18.66667, -6.666667, -43.52062, +30.51112, -31263.26507, +34.73317,
    +1111.11111, -51.851852)  <-- ALL EIGHT STRICT
  => radius 1/3 works uniformly for BOTH n, so the restatement keeps a single radius and only
  flips steps 1 and 4 (step 1 runs +,- not -,+; step 4 runs +,- not -,+). Steps 2,3 keep -,+.
- session4 step 3 note: at kappa0 = -1 step 4 has ROOTS at kappa = -2, -3/2 (n=8: also -1/2) and
  kappa = 0, because sum a_i^5 = 0 at both centres, so kappa = 0 is a root; that is why radius 1
  can never work for step 4. Likewise step 1 has an extra cubic root in (-1,0) (n=7) resp. (0,1)
  (n=8), and step 2's second root is at x = 1 (n=7) resp. x ~ 3.563 (n=8), so radius 1/2 is bad.
- session4 step 3 note: n=8 step 3's sign change does NOT survive radius 1/4 (both endpoints
  positive: +163201.92 and +28.06) - chainStep3 has a pole at mu0 - 1/4. Only radius >= ~1/2 works.
- SESSION 4 step 1: **MAJOR FINDING � all 7 statements in my range lack the root hypotheses** (hmon hn hnat hsep hcoef halpha hnd). exists_step1_poly has only (ha)(hb): FALSE (n=2, alphas=[t,0] outside the class, a=[0,1], b=0 forces the constant poly t^3). Same for 2,3,4,5,6; exists_oddTschirnhaus lacks hnat AND hsep. YSpace.lean:505 states the class is countable. I did NOT change any statement (per instructions) and left the 7 sorrys with WARNING doc comments; I added PROVED helpers with the root hypotheses: exists_step1_poly_of_roots DONE, exists_step4_poly_of_roots DONE, exists_step2_poly_of_roots in progress.
- session4 step 4: ALL EIGHT WRITTEN AND GREEN. diagnostics 640-1060: **0 errors**.
  * centre7_solves / centre8_solves: one 
orm_num per clause (big shared simp set).
  * centre7_inj / centre8_inj: have key : chainY ... = ![(1:R), ...] by
    unext i; fin_cases i <;> norm_num [chainY, chainP, chainV, chainConicPt, yBdotY,
    ymoment3Y, yNBY, ymoment2Y, chainQ0, chainD, chainW1/2/3, chainWt, chainProjN, psumFinY,
    ChainYInputs.*, centre*, Fin.sum_univ_succ, Pi.*_apply, smul_eq_mul], then
    w [key]; intro x y hxy; fin_cases x <;> fin_cases y <;> first | rfl | (norm_num at hxy).
  * centre7_signs / centre8_signs: RESTATED, radius 1 -> 1/3, step 1 and step 4 flipped to
      < f(k-1/3) and (k+1/3) < 0; steps 2, 3 keep < 0 then   <. Same 
orm_num.
- session4 step 4 GOTCHA: ![((1:R), -1, 2, ...)] parses as Matrix.vecCons applied to a TUPLE
  (the extra parens make a Prod, not a list). Write ![(1 : R), -1, 2, ...] exactly as the
  centre7a-style data defs do. Diagnostic: "Application type mismatch ... Matrix.vecCons
  (1, -1, 2, -2, 3, -3, 0)".
- session4 step 4: the whole file elaborates in well under the LSP timeout with these proofs;
  the previous session's heartbeat problem was entirely the plan's kappa.
- SESSION 4 step 2: exists_step2_poly_of_roots DONE. Also added yConicY_add_smul_right /
  yConicB_add_smul_right. NOTE: `yConicY P u = sum_i YP_i*(Yu_i)^2` is QUADRATIC in u, so the
  caller's suggested `yConicB_add_right`/`yConicB_smul_right` are FALSE (cross term 2*sum_i
  YP_i*Yu_i*Yv_i). The right lemma is the full line expansion with the mixed pairing
  `yBdotY P u w` as the middle coefficient. step 2 is therefore a genuine quadratic
  `C a + C b * X + C c * X^2`, a = yConicB P w~1, b = 2*yBdot P w~1 w~2, c = yConicB P w~2.
- SESSION 4 step 3: DESIGN for exists_step3_poly (recording before attempting).
  `psumY_line_poly` does NOT apply. Cheapest route found � INTERPOLATION AT RATIONAL NODES,
  reusing the (private, hence copied) engine from YSpace.psumY_line_poly:1045-1077:
    (E) if `p.natDegree <= m` and `PConstructible (p.eval r)` for all `r : Fin (m+1)` (the
        nodes 0..m), then every `p.coeff j` is P-constructible (Lagrange basis at rational
        nodes; `basis_coeff_Pconstructible` + `C_mul_coeff_Pconstructible`).
  With (E), the step-3 coefficients need NO hand expansion of the cubic moment: build
  `aff a b = C a + C b * X` (deg 1, `(aff a b).eval s = a + b*s`), then
    Bp = sum_i C (yvec P i) * (aff (yvec w3 i) (yvec w1 i))^2         (deg 2)
    Cp = sum_i C (yvec P i) * C (yvec q0 i) * (aff (yvec w3 i) (yvec w1 i))  (deg 1)
    p  = sum_i (C (yvec q0 i) * Bp - C 2 * Cp * aff (yvec w3 i) (yvec w1 i))^3   (deg 6)
  and `p.eval mu = chainStep3Cleared (yvec P) (yvec q0) (yvec (w3 + mu . w1))` by
  `eval_finsetSum` + two value lemmas `Bp.eval s = yBdotY (yvec P) d d`,
  `Cp.eval s = yBdotY (yvec P) (yvec q0) d` with `d = yvec (w3 + s . w1)`, then `add_comm`.
  PC-ness of `p.eval r` at a rational node: `p.eval r = psumY (yvec (B_r . q0 - 2*C_r . (r.w1+w3))) 3`
  with `B_r`, `C_r` P-constructible by `yBdot_Pconstructible`, so `psum_yvec_Pconstructible`
  applies. Degree lemmas needed: `Polynomial.natDegree_mul_le (R := R)` (NOTE: it IS a
  lemma, implicit p q; passing `_ _` as args is an error, and the `Semiring R` class arg
  must be pinned), `natDegree_pow_le_of_le q hp : (p^q).natDegree <= n*q`,
  `natDegree_sum_le_of_forall_le s n h`, `natDegree_sub_le`, `natDegree_C_mul_X_pow_le`.
- session4 step 5: FINAL lake_check Pptc/TotallyReal/Certificate.lean: **exit 0, no errors.**
  declaration uses sorry warnings now only at 235, 572 (= exists_chain_roots, 3rd agent),
  1068, 1082 (= exists_open_good7/8, other agent), 1477, 1703, 1723, 1741, 1755, 1771, 1813 -
  NONE in the rational-certificate section (599-1045). All eight of my lemmas are real proofs.
- SUMMARY for the caller:
  * centre7_solves: DONE. centre7_denom1/2: DONE (previous session). centre7_inj: DONE.
    centre7_signs: RESTATED + DONE.
  * centre8_solves: DONE. centre8_denom1/2: DONE (previous session). centre8_inj: DONE.
    centre8_signs: RESTATED + DONE.
  * sign terms, EXACT values (Wolfram Rational, re-verified by norm_num):
    n=7 r=1/3: step1 -1/3 = +358.6667, +1/3 = -65.3333; step2 1/6 = -60.73655, 5/6 = +68.96315;
      step3 mu0-1/3 = -0.07998354, mu0+1/3 = +0.24283831; step4 -4/3 = +59.25926, -2/3 = -331.85185
    n=8 r=1/3: step1 -1/3 = +18.66667, +1/3 = -6.666667; step2 4/3 = -43.52062, 2 = +30.51112;
      step3 mu0-1/3 = -31263.26507, mu0+1/3 = +34.73317; step4 -4/3 = +1111.11111, -2/3 = -51.851852
  * restatement: radius 1 -> 1/3 in ALL eight clauses of each lemma; steps 1 and 4 flipped from
    (< 0,   <) to (  <, < 0); steps 2 and 3 keep (< 0,   <).
  * NOTE for whoever proves exists_open_good7/8: it needs the sign changes on a *box* around the
    centre, so it must use the radius 1/3 above, not the plan's 1 - step 1/step 4 are not
    monotone over [c-1, c+1] and step 4 has roots at kappa = 0, -2, -3/2 (-1/2 for n=8).
- session4 step 5 note: lean_verify could not be used for an axiom check (\"Unknown constant
  centre7_signs\" - the LSP env is stale); the absence of any declaration uses sorry warning in
  the section is the evidence used instead, and the proofs reference no sorry'd lemma.
- SESSION 4 FINAL STATE (all in pptc/Pptc/TotallyReal/Certificate.lean, my section only).
  * exists_step1_poly: STUCK/FALSE (no root hypotheses). PROVED helper
    `exists_step1_poly_of_roots` (same statement + the 7 root hypotheses; psumY_line_poly m=3).
  * exists_step2_poly: STUCK/FALSE. PROVED helpers `yConicY_add_smul_right`,
    `yConicB_add_smul_right`, `exists_step2_poly_of_roots`
    (f = C a + C b * X + C c * X^2, a = yConicB P w~1, b = 2*yBdot P w~1 w~2, c = yConicB P w~2).
    NOTE the caller's suggested `yConicB_add_right`/`_smul_right` are FALSE (yConicY is
    quadratic in its 2nd slot).
  * exists_step3_poly: STUCK/FALSE, and NOT proved even with hypotheses. Full design logged
    above (interpolation at nodes 0..6 + p = sum_i (...)^3). This is the gate for items 5 and 7.
  * exists_step4_poly: STUCK/FALSE. PROVED helper `exists_step4_poly_of_roots`.
  * stepRoots_Pconstructible: STUCK/FALSE twice: (i) no root hypotheses; (ii) `ChainGood` does
    NOT give p != 0 � with I.b = 0 the step-1 function is the constant psumY (yvec a) 3 = 0, so
    `lam` is arbitrary. Needs an extra non-degeneracy conjunct (yvec as I.b != 0,
    ChainB.V != 0, step-2 quadratic and step-3 cubic not identically zero). Also needs
    chainStep3Cleared_eq' (still a sorry).
  * chainBLift_Pconstructible: STUCK/FALSE. PROVED helper
    `chainBLift_Pconstructible_of_roots` (7 root hypotheses + hI + hroots; does NOT need
    hchain). First-try success.
  * exists_oddTschirnhaus: STUCK/FALSE: missing `hnat : q.natDegree = n` (and, with the
    present machinery, `hsep`; `hsep` would follow from hnat + distinctness, and a Newton
    identity lemma would give psumRoots without it). Assembly route written out in its
    doc comment; depends on items 3 and 5 and on exists_open_good7/8 (other agent, sorry).
  * No public statement was changed; all 7 `sorry`s kept, each with a WARNING doc comment
    naming the exact missing hypotheses and the proved helper to use.
  * FINAL lake_check Pptc/TotallyReal/Certificate.lean: exit 0, no errors. `sorry` warnings
    only at my 7 theorems (1477/1703/1745/1763/1793/1943/2006 at the time of the run) plus
    pre-existing ones at 235, 572, 1068, 1082; style warnings at 329 (other agent), 1220,
    1228, 1313, 1321 (pre-existing unused hden / unused simp arg).
- SESSION 4 post-check: removed an unused smul_eq_mul from my hproj simp set; 
  w [hsum] <;> ring -> <;> ring_nf in yConicY_add_smul_right. lean_diagnostic_messages 1290-1700: 0 errors. All new declarations carry no sorryAx.

## Session 6 (me: exists_chain_roots + exists_open_good7/8)
- s6 step 1: read log + file. CONFIRMED the binder mismatch is still on disk: `h2`/`h3`/`h4`
  quantify over ASCII auto-bound `c1 c2 c3` (implicit autoImplicit binders), while the
  conclusion and the `c₁…eps₄` binder list are Unicode. This is a statement fix (in scope).
- s6 step 2: the h3/h4 endpoint clauses are written `0 < chainStep3' … (c₃ − eps₃)` /
  `0 < chainStep4' … (c₄ − eps₄)` — i.e. the direction is FLIPPED relative to
  `centre7_signs`/`centre8_signs` (step 3 is `0 < f(mu₀−r) ∧ f(mu₀+r) < 0` there).
  So `exists_chain_roots` with `epsₖ = 1/3` is NOT applicable at either centre as written.
- s6 step 3: BINDER FIX APPLIED (the Unicode names `c₁ c₂ c₃` in `h2`/`h3`/`h4`; this removes
  the three accidental autoImplicit binders). The statement is now TRUE — I proved by hand
  that with (i) the sign data uniform on the whole *open* box and (ii) a uniform margin
  (compactness) the proof goes: tube lemma + root localisation + IVT. The two "obvious"
  counterexamples both die on inspection: the "root drifts to the box boundary" example has
  `f(I₀, c−eps) = 0`, contradicting the strict endpoint signs; and a root set `Z` at `I₀` that
  is non-empty and avoids the end faces is automatically *compactly* inside the interval, so
  nearby roots cannot escape a compact core.
- s6 step 4: **`exists_tube_prod` PROVEN, 0 diagnostics** (in Certificate.lean, before
  `exists_chain_roots`). Statement:
  `theorem exists_tube_prod {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
     {S : Set (α × β)} (hS : IsOpen S) {x₀ : α} {K : Set β} (hK : IsCompact K)
     (hsub : ∀ k ∈ K, (x₀, k) ∈ S) : ∃ W : Set α, IsOpen W ∧ x₀ ∈ W ∧ ∀ x ∈ W, ∀ k ∈ K, (x, k) ∈ S`
  Toolkit facts learned (all in this build, cost ~6 iterations):
  * `IsCompact.elim_finite_subcover hK f (∀ k, IsOpen (f k)) (K ⊆ ⋃ k, f k) : ∃ t, K ⊆ ⋃ i ∈ t, f i`
    — the openness hypothesis is over ALL of the index type, so off-`K` the cover must still be
    open: use `∅` (always open) as the filler, never `Set.univ` (that loses the extraction).
  * `isOpen_iInter_of_finite (s := fun k => …) (h : ∀ i, IsOpen (s i)) : IsOpen (⋂ i, s i)`
    — `ι` is a `Finite` *type*, so index by the subtype `{k : β // k ∈ (t : Set β)}`; there is no
    `Finset.finite` field and `t.finite` does not exist.
  * `𝓝` is NOT in scope in this file (no `open scoped Topology`): write `nhds`.
  * `obtain`/`rcases` CANNOT eliminate `Exists` into a non-`Prop` goal ("`Exists.casesOn` can
    only eliminate into `Prop`"). Workaround used: state the `∃` with a *product* witness
    (`∃ p : Set α × Set β, …`) and get a usable value with
    `⟨Classical.choose h, Classical.choose_spec h⟩`; then projections work.
  * `set f … with hf`: `f k` is only *syntactically* equal to the RHS, so use
    `simp only [hf, dif_pos hk]` / `dif_neg` before `exact`, not a bare `exact`.
  * `Set.prod_mono` is the POINTWISE lemma; for the subset statement use
    `intro p hp; obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp`.
  * projections on a nested `Exists` are illegal; keep witness shapes shallow.

## Session 5 (me: `exists_step3_poly` only)
Goal: `exists_step3_poly` in `pptc/Pptc/TotallyReal/Certificate.lean` (line 1751), plus new
private helpers immediately above it. Statement unchanged. Plan (from the WARNING doc
comment above it): build `p = ∑ᵢ (C (Yq₀ᵢ)·Bp − C 2·Cp·affᵢ)³` with `aff i = C (Yw₃ᵢ) +
C (Yw₁ᵢ)·X`, `Bp = ∑ᵢ C (YPᵢ)·affᵢ²`, `Cp = ∑ᵢ C (YPᵢ·Yq₀ᵢ)·affᵢ`; show `p.degree ≤ 6` and
`p.eval mu = chainStep3Cleared …`; then run the (copied) Lagrange engine of
`YSpace.psumY_line_poly` on the nodes `0..6`, using `chainStep3Cleared` as
`psumY (yvec αs (B • q₀ − 2 • C • b)) 3` so `psum_yvec_Pconstructible` applies.
- s5 step 1: read YSpace 960-1080 (the four `private` helpers + the engine), Certificate
  95-150 (`chainStep3Cleared`), 1415-1465 (the two `_of_roots` step lemmas), 1725-1770.
  Helper signatures confirmed: `psum_yvec_Pconstructible` (7 root hyps + `hb` + `m`),
  `yBdot_Pconstructible` (7 root hyps + hP + hu + hv), `yBdot_eq_yBdotY` (rfl, simp),
  `yvec_add/_smul/_sub`. `chainStep3Cleared P q₀ d = ∑ᵢ (q₀ᵢ·⟨P,d,d⟩ − 2·⟨P,q₀,d⟩·dᵢ)³`.
- s5 step 2: WROTE the whole block (helpers + proof) in one edit. Route: `step3Aff`
  (private def), `Bp`/`Cp` (degree 2 / 1), `p` (degree 6), then the YSpace Lagrange engine
  on nodes `0..6` with the four `private` helpers copied verbatim. Added
  `import Mathlib.LinearAlgebra.Lagrange` (was only transitively available).
- s5 step 3: GOTCHAS fixed (5 diagnostics rounds):
  (a) `yvec_sub` is `ChainB.yvec_sub` (it lives in `namespace ChainB`), NOT plain `yvec_sub`.
  (b) `hCpdeg` needs `le_trans (natDegree_C_mul_le _ _) (step3Aff_natDegree …)` — plain
      `natDegree_C_mul_le` leaves `aff i`'s natDegree unbounded.
  (c) `hCpval`'s `rw` list must include `Pi.add_apply` BEFORE `Pi.smul_apply`
      (`(A + s • B) i` is not a `Pi.smul_apply` instance).
  (d) `natDegree_sum_le_of_forall_le`'s `{n}` is NOT determined by `le_trans`, so
      `hpdeg` needs `(n := 6)` explicitly, else `omega` sees an unbound `?m`.
  (e) **the `2 • C` scalar**: `PConstructible.mul (nat_Pconstructible 2) hCPC` gives
      `PConstructible (↑2 * C)` but the goal has `PConstructible (2 • C)` and neither
      `exact` nor `simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]` reconciles them
      (`•` here is `HSMul`/`NatCast`-flavoured, `smul_eq_mul` does not fire). The fix is
      `convert … using 1 <;> simp <;> ring`, which also disposes of the `Pi.add_apply`
      side goal `2*C*w₃ k + 2*C*(vv i*w₁ k) = 2*C*(w₃ k + vv i*w₁ k)`.
  Also: the node `b`-vector must be written `w₃ + vv i • w₁` (the same order as `hval`),
  otherwise `← yvec_add` lands on the wrong orientation and `add_comm` has to be forced.
- s5 step 4: 0 errors in my range (helpers ~1836-1973, theorem 1975-2105). Remaining
  file-wide errors are OTHER agents' in-progress work: 583-654 (`exists_chain_roots` /
  the tube-lemma scratch) and 2482 (`stepRoots_Pconstructible`). NOTE the file is being
  edited concurrently (2630+ lines and growing) so line numbers shift between calls.
- s5 step 5: **DONE.** `lean_goal` at the last tactic of `exists_step3_poly` returns
  `goals_after: []` and `lean_verify Pconstructible.exists_step3_poly` gives axioms
  `propext / Classical.choice / Quot.sound` — **no `sorryAx`**, so the theorem is fully
  proved. All 3 goals (`refine_1` natDegree, `refine_2` coeffs, `refine_3` values) close.
- s5 step 6: **`lake_check Pptc/TotallyReal/Certificate.lean` could NOT be completed** —
  6 attempts over ~10 min, all failing at `Certificate.lean:19:0` (the `import
  Pptc.TotallyReal.YSpace` line) with `error: failed to read file
  …\mathlib\.lake\build\lib\lean\Mathlib\<random module>.olean.private`, a DIFFERENT module
  each time. This is an environment/I-O problem, not a source problem: every one of the
  named `.olean` files verifiably EXISTS on disk (`Test-Path` = True), and the
  lean-lsp elaborator resolves the same imports fine. Probably file-handle / memory
  pressure from 4 stale zero-working-set `lake` processes (pids 2816/11244/17872/22048,
  started 2026-09-25 16:40 & 16:46) plus 2 live `lean` compiles (1691 MB and 405 MB).
  I did NOT kill anything — two other agents are mid-compile in this file and
  `Get-Process lean,lake | Stop-Process -Force` would disrupt them (and the lean-lsp
  server the `lean_*` tools depend on). SUGGESTED CLEANUP for the caller: once the other
  agents are idle, run `Get-Process lean,lake | Stop-Process -Force` and re-run
  `lake_check`. Also note that even a healthy `lake_check` would exit 1 right now,
  because of the other agents' in-flight errors at 583-654 and ~2482.
- s5 FINAL PROOF TEXT is in the file at lines 1975-2103 of
  `pptc/Pptc/TotallyReal/Certificate.lean` (region shifts as the other agents append).
  New private helpers, all immediately above the theorem:
  * `yBdotY_add_smul_both (P u w : Fin n → ℝ) (s : ℝ) :
     yBdotY P (u + s • w) (u + s • w) = yBdotY P u u + 2 * s * yBdotY P u w + s^2 * yBdotY P w w`
  * `yBdotY_add_smul_last (P q u w : Fin n → ℝ) (s : ℝ) :
     yBdotY P q (u + s • w) = yBdotY P q u + s * yBdotY P q w`
  * `chainStep3Cleared_eq_psumY (αs) (P q₀ b) (B C) (hB) (hC) :
     chainStep3Cleared (yvec αs P) (yvec αs q₀) (yvec αs b)
       = psumY (yvec αs (B • q₀ - (2 • C) • b)) 3`
  * `step3Aff (αs) (w₁ w₃) (i) : ℝ[X] := C (yvec αs w₃ i) + C (yvec αs w₁ i) * X` (def)
  * `step3Aff_natDegree … : (step3Aff αs w₁ w₃ i).natDegree ≤ 1`
  * `step3Aff_eval … (i) (s) : (step3Aff αs w₁ w₃ i).eval s = yvec αs w₃ i + s * yvec αs w₁ i`
  * `prod_coeff_Pconstructible`, `X_sub_C_coeff_Pconstructible`,
    `basisDivisor_coeff_Pconstructible`, `basis_coeff_Pconstructible` — copied VERBATIM
    from the `private` helpers of the same names in `YSpace.lean` (967-999).
  * import added: `Mathlib.LinearAlgebra.Lagrange` (was only transitively available).
 
 - SESSION 5 (me: yConicY_add_smul_eq + stepRoots_Pconstructible). Note: hN is now `yConicY P P = 0` (NOT yNBY), and stepRoots_Pconstructible already carries the 7 root hypotheses.
- yConicY_add_smul_eq: DONE. hN' : yNBY P P = 0 via `simpa only [yConicY, yNBY, ymoment2Y, mul_comm] using hN` (both are psumY P 3, but the summands are `P i ^ 1 * P i ^ 2` vs `P i ^ 2 * P i ^ 1` so NOT defeq), then `rw [yConicY_add_smul_expand, hN', mul_zero, add_zero]`.
  FINAL: the caller's stated hypothesis set (hN : yConicY P P = 0 alone) is STILL FALSE; a second conjunct (hN0 : yNBY P u = 0) was REQUIRED and added. Counterexample n=2, P=![1,-1], u=![1,0], s=1 (Wolfram exact Integer: {yConicY P P, yConicY P (u+P), yConicY P u} = {0, 3, 1}). Proof = `hN' : yNBY P P = 0` (`simpa only [yConicY, yNBY, ymoment2Y, mul_comm] using hN`) + `rw [yConicY_add_smul_expand, hN', hN0]; ring`. NOTE: the caller's suggested one-liner `rw [..., hN, mul_zero, add_zero]` cannot work - the middle term 2*s*yNBY P u is not a multiple of p3(YP).
- yConicY_add_smul_eq: DONE (4-line proof, second correction documented in the doc comment).
- stepRoots_Pconstructible: ORIENTATION DONE. FINDINGS: (a) the statement on disk does NOT yet carry the 7 root hypotheses (the orchestrator's fix is not on disk) - I will add them. (b) The caller's proposed leading-coefficient conjuncts are NOT sufficient: yvec as I.b != 0 does NOT make the step-1 cubic nonconstant, because psumY v 3 = sum v_i^3 vanishes for v = ![1,-1] != 0; explicit degenerate example A = B = ![1,-1] (n=2) gives chainStep1 A B == 0 identically with B != 0 (all four coefficients psumY A 3, yNBY A B, yConicY A B, psumY B 3 vanish). Same for ChainB.V != 0 (step 4) and ChainB.Wt != 0 (step 2). (c) Decision: state the four conditions as the step FUNCTIONS not being identically zero, i.e. the four chainStep*' (or chainStep3Cleared) witnesses of the 7 root hypotheses. These are exactly what centre7_signs/centre8_signs + continuity give on the open good set, and they are the natural extra conjuncts of ChainGood (which I may not edit).
- stepRoots_Pconstructible: **ChainGood SHOULD BE EXTENDED** with the four non-degeneracy conjuncts (step 1/2/3/4 functions not identically zero). Recommended for the orchestrator.
- stepRoots_Pconstructible: statement WRITTEN (7 root hypotheses + 4 non-degeneracy conjuncts hne1..hne4 + long RESTATEMENT doc comment). Proof WRITTEN, iterating on diagnostics. KEY LEAN GOTCHAS hit: (i) the guard plugin re-formats the file inserting a BLANK LINE between every line, so edit oldStrings must contain them; (ii) ChainGood is a 7-fold conjunction - indices are .1/.2.1/.2.2.1/.2.2.2.1 (the four steps), .2.2.2.2.1 (yNBY), .2.2.2.2.2.1 (yBdotY); (iii) chainStep3Cleared_eq' takes only the hden argument explicitly; (iv) rw direction: a have stated stepK' = stepK(yvec) is used FORWARD on a stepK' != 0 hypothesis but BACKWARD when the goal has the yvec form.
- stepRoots_Pconstructible: down to 3 errors, then 0 reported; LSP went temporarily unavailable (concurrent edits in the file). Added a small local helper hgdef : (chainBtoY as I).g = yvec as I.g (`simp only [chainBtoY, ChainYInputs.g]`) to bridge the two spellings of the g slot.
- stepRoots_Pconstructible: proof COMPLETE (all four steps: exists_step1_poly -> g1 != 0 -> root_Pconstructible_le_six_coeffs; same for 2/3/4; step 3 goes through chainStep3Cleared_eq' hden2' with hden2' = hchain.2.2.2.2.2.1 and hcl/hclmu bridges). Last diagnostic pass over MY range (2173-2510) showed exactly 1 error (hg4ne rw direction), now fixed; re-check was blocked by concurrent edits (diagnostics_unavailable).
- stepRoots_Pconstructible: DONE. FINAL lean_diagnostic_messages over the whole theorem (lines 2173-2520): success=true, 0 errors. yConicY_add_smul_eq range (218-260): success=true, 0 errors.
- FINAL lake_check Pptc/TotallyReal/Certificate.lean: COULD NOT COMPLETE. 5 attempts; every one aborted at
  the IMPORT line (19) with 'failed to read file <a DIFFERENT .lake/.../Mathlib/...olean[.private]>' each
  time, i.e. the Mathlib olean cache is being churned by a concurrent process. This is a transient
  environment failure at the import, NOT a diagnostic in the file. The two clean per-range
  lean_diagnostic_messages runs are the evidence that both of my theorems elaborate without errors.

## Session 7 (me: `exists_open_good7` / `exists_open_good8`)
Goal (Lean syntax): prove the two open-good-set existence theorems
`exists_open_good7 : ∃ U : Set (ChainYInputs 7), IsOpen U ∧ centre7 ∈ U ∧
  ∀ I ∈ U, ∃ lam x mu kappa, ChainGood I lam x mu kappa ∧ psumY (chainY …) 1 = 0 ∧ … 3 = 0 ∧ … 5 = 0`
and the `centre8` / `Fin 8` twin. Target file
`pptc/Pptc/TotallyReal/Certificate.lean` (~line 1033 and ~1047).
Plan: box-uniform sign data by `ContinuousAt.eventually_ne` from `centre7/8_signs`; apply
`exists_chain_roots` at `epsₖ = 1/3`; shrink the open set for the two denominators and for
distinctness of the output entries; then `psumY_13_line` for S₁, S₃ (needs `psumY (chainV …) 1 = 0`).
Open question flagged by the caller: whether the S₅ = 0 conjunct is derivable from `ChainGood`.
- s7 step 1: **S₅ is NOT the problem — it is `rfl`.** `chainStep4' I lam x mu kappa` unfolds to
  `psumY (chainP I lam + kappa • chainV I lam x mu) 5`, which is *character-identical* to
  `psumY (chainY I lam x mu kappa) 5`. Proved as `chainStep4'_psumY_eq`.
- s7 step 2: **S₃ is derivable.** Proved as `chainY_psumY_cube_eq`: h1 (step 1) = `psumY P 3 = 0`,
  h3 (step 3) = `psumY v 3 = 0`, h2 read as `yConicY P q₀ = 0`, plus
  `yNBY P v = 0` (from `chainProjN_mem_N` on w₁,w₂,w₃ + `yNBY_add_right`/`_smul_right`) and
  `yConicY P v = 0` (`chainConicPt_on_conic`). So it is `psumY_13_line` with `hP1`/`hv1`
  DROPPED — those two hypotheses are unnecessary.
- s7 step 3: **S₁ is the problem, and it is a genuine fifth equation.** Proved the identity
  `chainY_psumY_one_eq' : psumY (chainY I lam x mu kappa) 1
     = psumY (chainP I lam) 1 + kappa * psumY (chainV I lam x mu) 1`, and the criterion
  `chainY_psumY_one_eq` (S₁ vanishes on all six inputs ⇒ S₁ of the output vanishes; no
  denominator needed). `exists_open_good7` has no such hypothesis ⇒ FALSE as stated. The fix is
  the six input conditions (they hold at both centres) or a `ChainGood` extension with
  `psumY (chainP I lam) 1 = 0 ∧ psumY (chainV I lam x mu) 1 = 0`.
- s7 step 4: other new helpers, all proved (diagnostics clean):
  `psumY_sub_smul_eq`, `chainProjN_of_mem_N` (`chainProjN P g w = w` when `yNBY P w = 0`).
  NOTE `chainProjN_of_mem_N` is REQUIRED: `chainStep2'` applies `chainProjN` to `chainW1`
  *again* (`proj(proj(I.w1))`), so `chainStep2' I lam x = yConicY P (chainQ0 I lam x)` is NOT
  `rfl` — idempotence is a theorem, not a definitional equality.
- s7 step 5: LEAN GOTCHAS in this region (cost ~8 iterations):
  * `Pi.add_apply`/`Pi.smul_apply` do NOT fire on the *top-level* `f + g` / `s • f` inside
    `psumY (…) 1`; they only fire after `psumY, psumFinY` is unfolded and the summand is
    `(f + g) i`. So `simp only [chainQ0, Pi.add_apply, …]` errors with "`simp` made no
    progress". The working pattern is `have key : chainQ0 I lam x = chainW1 I lam + x • chainW2 I lam := rfl`
    followed by `rw [key, psumY_one_eq, …]`, i.e. rewrite the *definition* by an `rfl` equation
    and then use the top-level `psumY_one_eq`/`yNBY_add_right` directly.
  * instantiate `yNBY_add_right P u v` with the ACTUAL `v` appearing (e.g. `x • chainW2 I lam`,
    not `chainW2 I lam`), else `rw [h]` finds no occurrence.
  * `chainD I lam mu = mu • chainW1 I lam + chainW3 I lam` has the smul on the LEFT, so
    `psumY_one_eq` does not match; add `add_comm` to the `rw` list.
  * `exact` uses *guarded* defeq, so a defeq that `have … := rfl` accepts can still be rejected
    by `exact`; normalise both sides with `rw` instead.
  * `unfold chainWt; rfl` leaves the `match 0 : Fin 3 with` unreduced; `rfl`'s whnf does reduce it.
- s7 step 6: `exists_chain_roots` CANNOT be applied at `centre7` with `epsₖ = 1/3` as it stands:
  its `h1`/`h4` want the sign change `−,+` while `centre7_signs` records `+,−` for steps 1 and 4.
  Verified with Wolfram (exact Rational): step 1 is `-582λ + 1320λ² − 486λ³ = −6λ(97 − 220λ + 81λ²)`,
  roots `0, (220−√16972)/162 ≈ 0.5538, (220+√16972)/162 ≈ 2.1622`; step 4 (on `v*`) has roots
  `−2, −6/5, −19/18, −1, 0`. So `−,+` is available at `c₁ = 1/2` (f(1/6) < 0 < f(5/6)) and at
  `c₄ = −2`, but then `h2`/`h3`/`h4` must be re-established at those centres.
- s7 step 7: `exists_open_good_of_s1` ADDED and PROVED (immediately above `exists_open_good7`).
  It is the true form of `exists_open_good7`/`exists_open_good8` with the two missing inputs
  exposed as hypotheses, so the capstone needs nothing else:
  ```
  theorem exists_open_good_of_s1 {n : ℕ} {I₀ : ChainYInputs n}
      (hs1 : ∀ (I : ChainYInputs n), psumY I.a 1 = 0 ∧ psumY I.b 1 = 0 ∧ psumY I.g 1 = 0 ∧
        psumY I.w1 1 = 0 ∧ psumY I.w2 1 = 0 ∧ psumY I.w3 1 = 0)
      (hgood : ∃ U : Set (ChainYInputs n), IsOpen U ∧ I₀ ∈ U ∧
        ∀ I ∈ U, ∃ lam x mu kappa : ℝ, ChainGood I lam x mu kappa) :
      ∃ U : Set (ChainYInputs n), IsOpen U ∧ I₀ ∈ U ∧
        ∀ I ∈ U, ∃ lam x mu kappa : ℝ, ChainGood I lam x mu kappa ∧
          psumY (chainY I lam x mu kappa) 1 = 0 ∧ psumY (chainY I lam x mu kappa) 3 = 0 ∧
          psumY (chainY I lam x mu kappa) 5 = 0
  ```
  Proof = 8 lines: `obtain` the `U` from `hgood`, then per `I` the three power sums from
  `chainY_psumY_one_eq` / `chainY_psumY_cube_eq` / `← chainStep4'_psumY_eq`.
  ChainGood conjunction indices: `.1` step1, `.2.1` step2, `.2.2.1` step3, `.2.2.2.1` step4,
  `.2.2.2.2.1` yNBY, `.2.2.2.2.2.1` yBdotY, `.2.2.2.2.2.2` Injective.
- s7 step 8: WARNING doc comments added to BOTH `exists_open_good7` and `exists_open_good8`
  recording: S₅ is step 4 verbatim (rfl), S₃ follows from the chain's data, S₁ is a fifth
  equation that `ChainGood` does not imply; plus the two equivalent fixes and the
  `exists_chain_roots` sign-direction obstruction. Both theorems keep their `sorry`.
- s7 step 9: `lean_verify`: `chainY_psumY_one_eq`, `chainY_psumY_cube_eq` and
  `exists_open_good_of_s1` all have axioms exactly `propext / Classical.choice / Quot.sound`
  — **no `sorryAx`**. Diagnostics over the whole file: 0 errors in my range (1015–1360);
  the only errors are 2935–3100, in the `exists_oddTschirnhaus` region (another agent,
  `Continuous.prodMk` / `Set.preimage_mem_iff` — in-flight work, not touched).
## Session 9 (me: `exists_oddTschirnhaus` completion)
Goal: `exists_oddTschirnhaus` (line 3210) — replace `sorry` with the case split on `hn` plus two
applications of `exists_b_good_of_PC_roots`. `exists_open_good7/8` now (re)conclude with the four
`PConstructible` conjuncts, but are still `sorry`. Plan from session 8's step 5, adapted to the
now-nested conclusion of `exists_open_good7/8`.
- s9 step 1: read the log + the file. `exists_open_good7`'s conclusion is
  `IsOpen U ∧ centre7 ∈ U ∧ (∀ I ∈ U, psumY I.a 1 = 0 ∧ psumY I.b 1 = 0 ∧ psumY I.g 1 = 0) ∧
  ∀ I ∈ U, ∃ lam x mu kappa, …`, so `obtain` needs FIVE components (`⟨U, hU, hctr, _, hgood⟩`),
  not the four in the log. `exists_b_good_of_PC_roots`'s `hne : U.Nonempty` is `∃ x, x ∈ U`, so
  the membership fact must be paired: `⟨centre7, hctr⟩`. `subst` on `h7 : n = 7` rewrites `hnat`
  to `q.natDegree = 7` automatically, so `hnat` is passed unchanged.
- s9 step 2: WROTE the proof (8 lines, replacing the `sorry` at 3226) + refreshed the doc comment
  (STATUS: proved; the "one missing input" paragraph reworded as "the input that was missing, and
  where it comes from"; the recorded four-line sketch replaced by the two adaptations actually
  needed). Now checking diagnostics.
- s9 FINAL: `lake_check Pptc/TotallyReal/Certificate.lean` = **exit 0, no errors**. Diagnostics
  over the whole file (1-3242, both severities): **0 errors**. Remaining `sorry` warnings in the
  ENTIRE file are only 537 (`exists_chain_roots`), 1390, 1404 (`exists_open_good7/8`) — all other
  agents' ranges, untouched. My range (3153-3234) has no `sorry` and no error; the only warnings
  there are the file-wide `linter.style.emptyLine` ones.
- s9: **exists_oddTschirnhaus: DONE.** Proof is 8 lines (file lines 3226-3234), the log's recorded
  route verbatim apart from (a) the 5-component `obtain` (nested conclusion of
  `exists_open_good7/8`) and (b) `⟨centre7, hctr⟩` / `⟨centre8, hctr⟩` for the `hne : U.Nonempty`
  argument; `hnat` needed no `▸` after `subst`. `exists_open_good7/8` were still `sorry` when I
  used them, so the axiom set is `propext / sorryAx / Classical.choice / Quot.sound` — the
  `sorryAx` is inherited, not mine. `lake_check` output: exit 0, the 3 `sorry` warnings above plus
  pre-existing style warnings at 342, 1540, 1548, 1633, 1641, 1856, 2326, 2327, 2883 — all in
  other regions, all pre-existing, none fixed by me.
- s9 NOTE: `lean_verify Pconstructible.exists_oddTschirnhaus` returns axioms
  `propext / sorryAx / Classical.choice / Quot.sound` — the `sorryAx` is **inherited from
  `exists_open_good7/8`, which are still `sorry`**. My own proof contributes no axiom. So the
  file is *not* fully proved until the other two agents land `exists_chain_roots`,
  `exists_open_good7`, `exists_open_good8`; with those three `sorry`s gone, this capstone becomes
  `sorryAx`-free with no further change.
- s9 step 1 (verified by `lean_multi_attempt` at line 3224, no edit yet): the 8-line tactic
  CLOSES the goal (`goals: []`), only pre-existing `emptyLine` linter warnings.
- s7 FINAL: `lake_check Pptc/TotallyReal/Certificate.lean` = **exit 0, no errors**, and **zero
  warnings in my range** (1015–1440). Remaining file-wide warnings are all pre-existing or other
  agents': 342 (`<;>`), 537 (`exists_chain_roots` sorry), 1408/1433 (my two intended sorries),
  1571/1579, 1664/1672, 1887, 2357/2358, 2914, 2955/2957, 3243.
  `chainProjN_of_mem_N` lost its `hden` hypothesis: the idempotence holds with no denominator
  condition at all (`simp [hw]` closes it), which also removed both style warnings.
- s7 DELIVERABLE SUMMARY (all new declarations in `Pptc/TotallyReal/Certificate.lean`, all with
  axioms `propext / Classical.choice / Quot.sound`, no `sorryAx`):
  * 1040 `chainStep4'_psumY_eq (I) (lam x mu kappa) :
      chainStep4' I lam x mu kappa = psumY (chainY I lam x mu kappa) 5`  (by `rfl`)
  * 1048 `chainY_psumY_one_eq' (I) (lam x mu kappa) :
      psumY (chainY I lam x mu kappa) 1
        = psumY (chainP I lam) 1 + kappa * psumY (chainV I lam x mu) 1`
  * 1060 `psumY_sub_smul_eq (P v) (s) : psumY (P - s • v) 1 = psumY P 1 - s * psumY v 1`
  * 1080 `chainY_psumY_one_eq {I} {lam x mu kappa} (ha) (hb) (hg) (hw1) (hw2) (hw3) :
      psumY (chainY I lam x mu kappa) 1 = 0`  (the six `psumY I.? 1 = 0` conditions; no
      denominator needed)
  * 1174 `chainProjN_of_mem_N {P g w} (hw : yNBY P w = 0) : chainProjN P g w = w`
  * 1192 `chainY_psumY_cube_eq {I} {lam x mu kappa} (h1 : chainStep1' = 0) (h2 : chainStep2' = 0)
      (h3 : chainStep3' = 0) (hden1 : yNBY (chainP I lam) I.g ≠ 0)
      (hden2 : yBdotY (chainP I lam) (chainD …) (chainD …) ≠ 0) :
      psumY (chainY I lam x mu kappa) 3 = 0`
  * 1321 `exists_open_good_of_s1 {n} {I₀} (hs1) (hgood) :` the true form of
    `exists_open_good7`/`exists_open_good8` (statement quoted in step 7 above)
- exists_open_good7: **STUCK/FALSE** — `sorry` kept, WARNING doc comment added (the blocker is
  the `psumY … 1 = 0` conjunct, NOT the `5` one). exists_open_good8: same.

## Session 8 (me: `exists_oddTschirnhaus`)
Goal: `exists_oddTschirnhaus` in `pptc/Pptc/TotallyReal/Certificate.lean` (line 2582), plus
private helpers immediately above it. Plan (revised after reading the file): the six-slice
density argument of the previous plan is UNNECESSARY and in fact demands a non-constancy
argument the goal does not need. Better route: the open set `W := (chainBtoY αs) ⁻¹' U` in
**b-space** is open (chainBtoY is continuous) and nonempty (chainBtoY αs is onto), so ONE
application of the 1-fold `exists_Pconstructible_mem_isOpen` per coordinate (a private 6-fold
version) gives a P-constructible b-input I with `chainBtoY αs I ∈ U`; then `exists_open_good7/8`
applies to `chainBtoY αs I`, and `chainBLift_yvec` + `chainBLift_Pconstructible` finish.
- s8 step 1: FINDING (blocker, documented in the file): `chainBLift_Pconstructible` needs
  `hroots : PC lam ∧ PC x ∧ PC mu ∧ PC kappa`, and **`exists_open_good7/8` does NOT conclude
  P-constructibility of the four step roots** — its conclusion is only `ChainGood` + the three
  power sums. `ChainGood` cannot supply it (it says nothing about the four step *functions*
  being non-identically zero), and the proved `stepRoots_Pconstructible` needs exactly the four
  extra non-degeneracy conjuncts `hne1..hne4` that `exists_open_good7/8` does not provide.
  So the theorem is NOT provable from the current statements. Fix = add to the conclusion of
  `exists_open_good7/8` either (a) `PC lam ∧ PC x ∧ PC mu ∧ PC kappa`, or (b) the four `hne`
  conjuncts (then `stepRoots_Pconstructible` applies verbatim). I may not edit those statements
  (other agent's range), so I prove everything up to that single hypothesis.
- s8 step 2: ROUTE REVISED AGAIN (the plan's six-slice argument in y-space is WRONG, not just
  unnecessary). Two facts found the hard way:
  (a) Working in y-space produces P-constructible *y*-vectors, not P-constructible *b*-vectors:
  `yvecL_surjective` lifts a y-vector to a b-vector but says nothing about its P-constructibility
  (Vandermonde inverse entries are only ratios of rationals). So the density argument MUST be in
  b-space.
  (b) `Continuous (chainBtoY αs)` in b-space is NOT provable by `Continuous.prod`/`continuous_pi`:
  `ChainBInputs n` is a nested product of *function* spaces, so extracting a deep coordinate
  (`I.2.2.2.2.1`) needs a function-valued intermediate and the recursion does not bottom out.
  Fix that works and is short: do the six steps in b-space, one coordinate at a time, where the
  other five coordinates are CONSTANTS — then each step's map is `hyv` in one slot and
  `continuous_const` in the others, composed with `Continuous.prodMk` (note: `Continuous.prod`
  and `Continuous.pi` do NOT exist in this build; `continuous_pi` and `Continuous.prodMk` do).
- s8 step 3: GOTCHAs hit (each cost 1 diagnostic round):
  * `Fin m` has no `OfNat 0`, so `hyv 0` / `continuous_pi 0` fail — write `continuous_pi fun i => ?_`.
  * `hb₁ : (yvecL αs) b₁ = Y.a` will NOT `rw` into a goal mentioning `yvec αs b₁`; ascribe the
    type instead: `obtain ⟨b₁, h₁⟩ : ∃ b : Fin m → ℝ, yvec αs b = A := yvecL_surjective hnd A`,
    and destructure `Y := (A, (B, (C, (D, (E, F)))))` first, else `Prod.mk.injEq` cannot split.
  * `Set.preimage_mem_iff` does NOT exist; the lemma is `Set.mem_preimage`.
  * `IsOpen.preimage (show … by …)` inline is a parse/layout trap — use a separate
    `have gₑ : Continuous … := by`.
  * `unfold chainBtoY` then `exact hyv.prodMk (…)` DOES work (defeq on the projections).
- s8 step 4: **ALL FOUR HELPERS PROVED, 0 diagnostics in 2790-3260**, and lines 1-2790 (the other
  two agents' regions) are also error-free. Helpers added immediately above `exists_oddTschirnhaus`
  (all `private`, all with doc comments):
  * `chainBtoY_surjective {αs : Fin m → ℝ} (hnd) (Y : ChainYInputs m) : ∃ I : ChainBInputs m, chainBtoY αs I = Y`
  * `continuous_yvec (αs : Fin m → ℝ) : Continuous fun b : Fin m → ℝ => yvec αs b`
  * `exists_Pconstructible_lift {αs} {U : Set (ChainYInputs m)} (hU : IsOpen U) (hne : U.Nonempty)
     (hnd : Function.Injective αs) : ∃ I : ChainBInputs m, (∀ k, PC (I.a k)) ∧ … ∧ (∀ k, PC (I.w3 k))
     ∧ chainBtoY αs I ∈ U`   ← the six density steps, in b-space
  * `exists_b_good_of_PC_roots {q} {αs} {U} (hU) (hne) (hgood) (hmon) (hpos) (hnat) (hsep) (hcoeff)
     (hαs) (hnd) : ∃ b, (∀ k, PC (b k)) ∧ Injective (yvec αs b) ∧ psumY … 1 = 0 ∧ 3 = 0 ∧ 5 = 0`
    where `hgood : ∀ Y ∈ U, ∃ lam x mu kappa, ChainGood Y lam x mu kappa ∧ PC lam ∧ PC x ∧ PC mu ∧
    PC kappa ∧ psumY (chainY Y lam x mu kappa) 1 = 0 ∧ 3 = 0 ∧ 5 = 0` — i.e. EXACTLY the
    conclusion of `exists_open_good7/8` with the four `PConstructible` conjuncts added.
- s8 step 5: `exists_oddTschirnhaus`: **STUCK on the last four lines only** (doc comment rewritten
  with the exact missing conjunct and the exact completion, which is
  `rcases hn with h7 | h8; subst; obtain ⟨U, hU, hctr, hgood⟩ := exists_open_good7/8;
  exact exists_b_good_of_PC_roots hU hctr hgood hmon (by omega) hnat hsep hcoeff hαs hnd`).
  Also recorded in the doc comment: the concrete degenerate example (`n = 2`, `I.a = I.b = ![1, -1]`
  makes `chainStep1 I.a I.b · ≡ 0` although `I.b ≠ 0`), which shows `ChainGood` cannot yield the
  roots' P-constructibility, and that `centre7_signs`/`centre8_signs` (strict sign change across
  each step function) is exactly what would yield it inside `exists_open_good7/8`.
- s8 FINAL: `lake_check Pptc/TotallyReal/Certificate.lean` = **exit 0, no errors**. `sorry`
  warnings only at 537, 1408, 1433 (other agents) and 3241 (= `exists_oddTschirnhaus`, the
  documented last step). Diagnostics over lines 1-2790 (both other agents' regions) and
  2790-3266 (mine) are **0 errors**, so their work is intact. The only warnings inside my text
  are the file-wide `linter.style.emptyLine` ones caused by the guard plugin's blank-line
  insertion, plus the pre-existing unused-`hchain` warning on `chainBLift_Pconstructible` (2914).
  Also removed 6 unused-simp-arg warnings of my own by dropping the redundant
  `ChainYInputs.*` entries from the `simp only` in `chainBtoY_surjective`.
- exists_oddTschirnhaus: STUCK on the LAST FOUR LINES ONLY, for a reason outside my region:
  `exists_open_good7/8` must gain the four `PConstructible` conjuncts (or the four `hne`
  conjuncts) in their conclusion. Everything else — the b-space density argument and the whole
  assembly — is proved in `exists_Pconstructible_lift` + `exists_b_good_of_PC_roots`.

## Session 7 (me: `exists_chain_roots`) � BLOCKED, no Lean written
- s7 step 1: baseline `lean_diagnostic_messages` on Certificate.lean: **0 errors** (the other two agents' regions are currently clean).
- s7 step 2: read the statement on disk (lines 537-561) + defs. `chainProjN` divides by `yNBY P g`;
  `chainConicPt` divides by `yBdotY P d d`; so step 2's denominator is `yNBY (chainP I lam) I.g`
  and steps 3/4's is `yBdotY (chainP I lam) (chainD I lam mu) (chainD I lam mu)`.
  `hden1` supplies that only at `(I0,c1)`; `hden2` only at `(I0,c1,c3)`.
- s7 step 3: **THE SETTLED DESIGN IN THE BRIEF IS NOT SUFFICIENT � pole-degeneracy obstruction.**
  The tube / `exists_step_local` route needs, for step 2, an OPEN set
  `S = {(I,lam) | step2' I lam (c2 -+ eps2) signs hold}` in `ChainYInputs n x R` containing
  `{I0} x K1` for a compact interval `K1` containing `c1`. S openness FAILS at any
  `lam*` with `yNBY (chainP I0 lam*) I0.g = 0` (a pole of step 2) inside `K1`, because
  `chainProjN` divides by it, so `I |-> step2' I lam* (.)` and `lam |-> step2' I0 lam* (.)`
  are both O(1/denom) and discontinuous there.
- s7 step 4: `h2` does NOT exclude such a pole, and the brief's suggested fix (choose `K1`
  small enough to avoid the poles AND keep the step-1 sign change) is NOT generally possible:
  the step-1 sign change forces K1's radius into the open range around `eps1`, pole-avoidance
  only gives radii below the distance to the nearest pole, and the two ranges can be disjoint
  (denom pole at `c1 + 0.05` with `eps1 = 1`).
- s7 step 5: the theorem still looks TRUE in that case. With
  `f_x(lam) = Q_P(w1 + x w2) - 2*((n1 + x n2)/denom)*<w1 + x w2, g>_P + ((n1+x n2)/denom)^2 * Q_P(g)`,
  `h2` (opposite strict signs on a whole open box) forces `Q_P(g) = 0` at the pole, then
  `(n1+x_- n2)*<w1+x_- w2,g>_P = (n1+x_+ n2)*<w1+x_+ w2,g>_P = 0`; so `f` has either a
  removable singularity or a one-sided blow-up of the correct sign and the sign set is open in
  `lam`. A rigorous Lean proof needs a full pole-location/degree argument, and I-direction
  openness AT a pole is genuinely false, so the tube argument as stated cannot be made to work
  without extra hypotheses.
- s7 step 6: NOT PROVEN. No edit made to Certificate.lean (file left byte-identical).
  RECOMMENDED FIX for the caller: add a non-degeneracy conjunct, e.g. either
  `hden1' : forall lam, |lam - c1| <= eps1 -> yNBY (chainP I0 lam) I0.g <> 0` or
  `hden2' : forall lam mu, |lam - c1| <= eps1 -> |mu - c3| <= eps3 ->
             yBdotY (chainP I0 lam) (chainD I0 lam mu) (chainD I0 lam mu) <> 0`.
  With that, the settled tube design goes through: shrink the radii `d_j` by a uniform squeeze
  over the compact boxes `K1 x ... x K_{j-1}` (2-fold tube lemma applied to the slab
  `K x [eps-1, eps+1]` with base point `eps`), then four 1-D `intermediate_value_Icc` steps,
  then `U := (intersection of the four W) (openBall I0 1)`.
- s7 step 7: `ChainYInputs n` is a 6-fold product of `Fin n -> R`, so `ProperSpace` /
  `closedBall` are available and compactness of the boxes is free.

## Session 8b (me: `exists_open_good7` / `exists_open_good8` — the current statements are FALSE)
- s8b step 1: read log + file. **`exists_open_good7`/`exists_open_good8` as stated are FALSE**,
  and the `PConstructible` conjuncts are the fatal part (not a missing hypothesis I could add).
  Reason: `U` is open and `∋ centre7`, and `It t := (centre7a + t • e₁, centre7b, centre7g,
  centre7w1, centre7w2, centre7w3)` is continuous with `It 0 = centre7`, so `It '' (-δ, δ) ⊆ U`
  for some `δ > 0`. For a FIXED `lam`, `chainStep1' (It t) lam = ∑ᵢ (aᵢ + t eᵢ + lam bᵢ)³` is a
  cubic in `t` with LEADING COEFFICIENT 1 (`e₀³ = 1`), hence finitely many `t`. The
  P-constructible reals are countable (YSpace.lean:505), so
  `{t | ∃ lam, chainStep1' (It t) lam = 0 ∧ PConstructible lam}` is COUNTABLE and cannot contain
  `(-δ, δ)`. Adding the seven root hypotheses does not help: they constrain `q`/`αs`, not the
  y-vector `I`. The statement needs a **b-space** form — `PConstructible` is only forced for
  `I = chainBtoY αs b` with `b` P-constructible (which is how `exists_oddTschirnhaus` uses it).
- s8b step 2: TWO further blockers, independent of the above (both in the plan's route):
  (a) `ChainGood`'s `Injective (chainY …)` conjunct cannot be obtained from `exists_chain_roots`:
  that lemma only LOCALISES the witnesses to the radius-`1/3` boxes, whereas
  `∏_{i<j} (yᵢ - y_j)² ≠ 0` is continuous and hence only nonzero on a SMALL neighbourhood of the
  centre configuration. "Intersect with the injectivity set" needs the witness to be FIXED, not
  moving with `I`. (A fixed-witness version — witnesses in a small box — would fix this, but the
  box radius is pinned to `1/3` by `centre7_signs`.)
  (b) `h₂/h₃/h₄` of `exists_chain_roots` are box-uniform nonvanishing claims over a CONTINUUM of
  earlier parameters; the value at the centre gives only a NEIGHBOURHOOD, and the box radius is
  pinned to `1/3`. So "h₂/h₃/h₄ follow from continuity" is not formalisable as instructed, UNLESS
  the Step-9 agent's "earlier parameters fixed at their `I₀` values" proof strategy makes the
  `h_k` hypotheses unnecessary — in which case `exists_chain_roots` should be RESTATED with no
  `h₂/h₃/h₄` at all, and the caller should be told.
- s8b step 3: plan: (i) prove the six `psumY I.? 1 = 0` facts at both centres + the open `S₁` set
  (cheap `norm_num` + continuity; substantiates the doc comment's claim, and is what any
  completion of the theorem needs), (ii) formalise the refutation of (s8b step 1) as a lemma,
  (iii) rewrite the two doc comments with the precise diagnosis, (iv) keep `sorry` in both
  theorems. No statement of any other theorem is touched; helpers go immediately above
  `exists_open_good7`.
- s8b step 4: **MAJOR FINDING — the `S₁` middle conjunct of `exists_open_good7/8` is
  IMPOSSIBLE, and this is the reason the whole plan fails.** The statement asks for an open
  `U ∋ centre7` with `∀ I ∈ U, psumY I.a 1 = 0 ∧ psumY I.b 1 = 0 ∧ psumY I.g 1 = 0`. But
  `I ↦ psumY I.a 1 = ∑ᵢ I.aᵢ` is a NONCONSTANT continuous function of the free coordinate
  `I.a`, so its zero set is a proper closed hypersurface and contains no nonempty open set.
  (Perturbing `I.a` alone by `t • e₀` changes the sum by `t`.) **The set is CLOSED, not open**
  — the previous doc comment's "the set is open, so intersecting is free" was exactly
  backwards. Also: only 3 of the 6 conditions `chainY_psumY_one_eq` needs are written down
  (the `w₁, w₂, w₃` ones are missing), and those are closed too. So the `S₁` conditions cannot
  be imposed by shrinking an open set of y-space inputs at all; they must come from the
  `kappa`-dependence of `psumY (chainY …) 1 = psumY (chainP I lam) 1 + kappa * psumY
  (chainV I lam x mu) 1` (`chainY_psumY_one_eq'`), i.e. by choosing the WITNESS. The chain has
  4 degrees of freedom and `S₁ = 0` is one equation in them, so that is one condition on the
  witness, not a condition on the input. (This also shows session 7's `exists_open_good_of_s1`
  is unusable: its `hs1` is `∀ I`, a *closed* condition stated for every input.)
- s8b step 5: **PROVED and added** (all immediately above `exists_open_good7`, diagnostics
  clean, no `sorryAx`):
  * `centre7_s1 : psumY centre7a 1 = 0 ∧ … ∧ psumY centre7w3 1 = 0` — all six hold EXACTLY
    (`refine ⟨?_,…⟩ <;> norm_num [psumY, psumFinY, centre7a, …, Fin.sum_univ_succ]`; verified
    independently with Wolfram exact `Rational` arithmetic: all twelve sums are 0).
  * `centre8_s1` — the same six for `centre8`.
  * `s1_closed {n : ℕ} : IsClosed {I | the six S₁ conditions}` — the formal version of the
    finding in step 4. This REPLACES an `open_s1`/`open_s1_centre7/8` I had drafted and then
    deleted: those were false.
  * private helpers: `continuous_psumY_one`, `cont_comp`, `continuous_slots`, `isClosed_zero`,
    `isClosed_and6`.
- s8b step 6: LEAN GOTCHAS in this region (cost ~8 rounds):
  * **`isOpen_singleton` does NOT exist in this Mathlib** (nor `singleton_isOpen`); only
    `isOpen_singleton_iff_nhds_eq_pure` / `isOpen_singleton_iff_punctured_nhds` /
    `isOpen_compl_singleton` / `isOpen_ne`. For a *closed* zero set use
    `IsClosed.preimage hg isClosed_Icc` with the set equality
    `{x | g x = 0} = g ⁻¹' Set.Icc 0 0` — that works and needs only `Set.mem_Icc`.
  * `IsClosed.preimage` takes **`Continuous` FIRST**, then `IsOpen`/`IsClosed`:
    `IsClosed.preimage (continuous …) isClosed_Icc`. (`IsOpen.preimage` is the other way
    round: `IsOpen.preimage isOpen_… (continuous …)`.)
  * `continuous_fst.snd` / `ha.snd` on a `Continuous (fun p : A × B => p.1)` MISELABELS the
    domain (`Continuous fun (x : (? × ?) × ?) ↦ x.1.2`); use `continuous_snd` with the expected
    type ascription instead.
  * `Continuous.comp`'s conclusion is `Continuous (g ∘ f)` and `Function.comp` does NOT
    unfold at the `isDefEq` check, so a composition has to be stated as a plain lambda
    (`cont_comp`) — but `exact hg.comp hf` for such a statement DOES work, no `simpa` needed.
  * Do NOT state continuity as `Continuous ChainYInputs.b` with the slot accessors: `exact`/
    `simpa only [ChainYInputs.b]` will not match a plain-lambda composition against the
    accessor `def`. State it as `Continuous (fun I : ChainYInputs n => psumY I.b 1)` instead.
  * Lambdas passed to a helper need `(fun I : ChainYInputs n => …)`; without the ascription
    `I.a` cannot be resolved ("Invalid field notation").
- s8b step 7: doc comments of BOTH `exists_open_good7` and `exists_open_good8` REWRITTEN as
  WARNINGs: the statement is false for three independent reasons (the impossible `S₁` conjunct;
  the impossible `PConstructible` conjuncts, by countability of the P-constructible reals +
  "step 1 is a cubic with leading coefficient 1 in the perturbation", so the good-`t` set is
  countable; and `ChainGood`'s `Injective` conjunct not following from `exists_chain_roots`'s
  radius-`1/3` localisation because the witness moves with `I`). Each obstruction is stated
  with its argument, plus what IS proved and plus the correct fix. Both `sorry`s kept.
- exists_open_good7: **STUCK/FALSE — the statement is false, `sorry` kept, WARNING doc comment
  written.** (It is not a missing hypothesis: the middle `S₁` conjunct alone is unsatisfiable,
  and the four `PConstructible` conjuncts are unsatisfiable for a generic point of any open
  `U`.) Delivered instead: `centre7_s1`, `centre8_s1`, `s1_closed` + the diagnosis.
- s8b FINAL: `lake_check Pptc/TotallyReal/Certificate.lean` = **exit 1, with exactly TWO errors,
  both at 586 and 588, i.e. inside `exists_chain_roots`'s proof — the `exists_chain_roots`
  agent's in-flight region (`ContinuousOn.pi` does not exist in this Mathlib, and a `by` with
  no expected type). NOT MINE, NOT TOUCHED.** In my range (1395-1610) the only diagnostics are
  warnings: `Set.mem_setOf_eq` deprecated (1496) and the two intended
  `declaration uses sorry` at 1586 (`exists_open_good7`) and 1606 (`exists_open_good8`).
  `lean_diagnostic_messages` over the whole file agrees: the only errors are those two.
  Everything else (the other two agents' `centre*` lemmas, `stepRoots_Pconstructible`,
  `exists_oddTschirnhaus`, `exists_open_good_of_s1`) still elaborates.
- s8b DELIVERABLE SUMMARY (all in `pptc/Pptc/TotallyReal/Certificate.lean`, immediately above
  `exists_open_good7`; no other theorem's statement touched; no `axiom`; no `sorry` added
  except the two intended ones already present):
  * `centre7_s1`, `centre8_s1`: the six `psumY I.? 1 = 0` conditions hold EXACTLY at both
    centres (Wolfram exact-Rational cross-check: all twelve sums are 0).
  * `s1_closed`: the six `S₁` input conditions define a CLOSED set — the formal refutation of
    the middle conjunct of `exists_open_good7/8` (see s8b step 4).
  * private helpers `continuous_psumY_one`, `cont_comp`, `continuous_slots`, `isClosed_zero`,
    `isClosed_and6`.
  * WARNING doc comments on `exists_open_good7` and `exists_open_good8` giving the three
    independent obstructions and the correct fix for each.

## Session 9 (me: `exists_chain_roots`, the corrected statement)
Goal (Lean syntax), target `pptc/Pptc/TotallyReal/Certificate.lean`:
```
theorem exists_chain_roots (I₀ : ChainYInputs n) (c₁ c₂ c₃ c₄ eps₁ eps₂ eps₃ eps₄ : ℝ)
    (heps : 0 < eps₁ ∧ 0 < eps₂ ∧ 0 < eps₃ ∧ 0 < eps₄)
    (h1 : chainStep1' I₀ (c₁ - eps₁) * chainStep1' I₀ (c₁ + eps₁) < 0)
    (h2 : ∀ lam, |lam - c₁| < eps₁ → chainStep2' I₀ lam (c₂-eps₂) * chainStep2' I₀ lam (c₂+eps₂) < 0)
    (h3 : ∀ lam x, |lam-c₁| < eps₁ → |x-c₂| < eps₂ → chainStep3' … (c₃-eps₃) * chainStep3' … (c₃+eps₃) < 0)
    (h4 : ∀ lam x mu, … → chainStep4' … (c₄-eps₄) * chainStep4' … (c₄+eps₄) < 0)
    (hden1 : yNBY (chainP I₀ c₁) I₀.g ≠ 0)
    (hden2 : yBdotY (chainP I₀ c₁) (chainD I₀ c₁ c₃) (chainD I₀ c₁ c₃) ≠ 0) :
    ∃ U : Set (ChainYInputs n), IsOpen U ∧ I₀ ∈ U ∧ ∀ I ∈ U, ∃ lam x mu kappa,
      |lam-c₁| < eps₁ ∧ |x-c₂| < eps₂ ∧ |mu-c₃| < eps₃ ∧ |kappa-c₄| < eps₄ ∧
      chainStep1' I lam = 0 ∧ chainStep2' I lam x = 0 ∧ chainStep3' I lam x mu = 0 ∧
      chainStep4' I lam x mu kappa = 0
```
Plan (chosen after re-analysing s7's pole objection, see next entry): **no radius
shrinking, and NO continuity in the earlier roots is needed.** Four 1-D IVTs run with the
earlier parameters FIXED at the values they take at `I₀`; only the sign conditions are then
transferred in `I`. Helpers go immediately above `exists_chain_roots` (never above
`exists_open_good7`).
- s9 step 1: **THE SETTLED DESIGN IS STILL NOT SUFFICIENT, but for a different and sharper
  reason than s7 reported.** Two pole obstructions, both real, both in the conclusion at
  `I₀ ∈ U` itself:
  (a) STEP 2: `chainProjN P g w = w - (yNBY P w / yNBY P g) • g`; at a zero of
      `yNBY P g` Lean's total division makes the projection the IDENTITY, so the step-2
      function becomes the quadratic `yConicY P (w₁ + x w₂) = Σᵢ Pᵢ(w₁ᵢ+xw₂ᵢ)²`. I first
      thought `yConicY` positive-semidefinite would kill the pole, but `yConicY YP Yu =
      Σᵢ YPᵢ·Yuᵢ²` has the weight `YPᵢ` LINEAR, so it is sign-indefinite when `P` has mixed
      signs — the pole is NOT excluded. (s7's `hden1'`-style fix is still the right one.)
  (b) **STEP 3 (new, and fatal independently of (a))**: `h3` asserts the sign data only at the
      two endpoints `c₃ ∓ eps₃`; it says nothing at an interior point of the `μ`-interval.
      `chainStep3'` is `psumY (chainConicPt P Q (μw̃₁+w̃₃)) 3`, whose denominator
      `yBdotY P d d = Σᵢ Pᵢ dᵢ²` is a genuine quadratic in `μ` and may vanish INSIDE the
      interval; at such a pole Lean's total division makes the value the reduced
      `psumY Q 3`, and a strict sign change at the two endpoints then does NOT force a zero.
      VERIFIED WITNESS (backend `wolfram_WolframLanguageEvaluator`, exact Rational):
      `P = (1,-1)`, `q₀ = (1,0)`, `w̃₁ = (1,-1)`, `w̃₃ = (1,1)` ⟹ `d(μ) = (μ+1, 1-μ)`,
      `yBdotY P q₀ d = μ+1`, `yBdotY P d d = 4μ`, so
      `chainStep3 = -(3μ⁴+1)/(4μ³)` for `μ ≠ 0` and `= 1` at `μ = 0`.
      Hence `f(-1) = +1 > 0`, `f(1) = -1 < 0` (data holds) and `3μ⁴+1 > 0` on all of `ℝ`, so
      **there is no step-3 root anywhere in the interval.** Since the conclusion quantifies
      over `I = I₀ ∈ U`, no proof is possible from the stated hypotheses.
- s9 step 2: four continuity lemmas ADDED and PROVED (all immediately above
  `exists_chain_roots`, `fun_prop` works, 0 diagnostics):
  * `continuous_chainStep1' (I : ChainYInputs n) : Continuous (chainStep1' I)`
  * `continuous_chainStep2' (I : ChainYInputs n) (lam : ℝ)
       (hden : yNBY (chainP I lam) I.g ≠ 0) : Continuous fun x => chainStep2' I lam x`
  * `continuousOn_chainStep3' (I : ChainYInputs n) (lam x : ℝ) {S : Set ℝ}
       (hS : ∀ mu ∈ S, yBdotY (chainP I lam) (chainD I lam mu) (chainD I lam mu) ≠ 0) :
       ContinuousOn (fun mu => chainStep3' I lam x mu) S`
  * `continuous_chainStep4' (I : ChainYInputs n) (lam x mu : ℝ) :
       Continuous fun kappa => chainStep4' I lam x mu kappa`
  TECHNIQUE NOTES (each cost a round): `fun_prop` is available but needs
  `simp only [psumY, psumFinY, Pi.add_apply, Pi.smul_apply]` first (`psumY` is an *abbrev*
  for `psumFinY`, and `fun_prop` cannot see through an abbrev of a def); for step 3 `fun_prop`
  fails (it asks for continuity of the *coordinates* `chainProjN`, which involve their own
  division) so the proof is manual: `ContinuousOn.div` (NOT `Continuous.div`, whose
  nonvanishing argument is `∀ x : ℝ`, unrestricted), then `ContinuousOn.smul`
  (`Topology/Algebra/MulAction.lean`; `ContinuousOn.const_smul` is `Continuous`-only and has
  the arguments the other way round), then `ContinuousOn.sub` with `continuousOn_const`
  (not `continuous_const`), then `(continuous_finsetSum-style)`.comp_continuousOn with
  `hc : Continuous (fun v : Fin n → ℝ => psumY v 3)` (needs `unfold psumY psumFinY`).
  NOTE `ContinuousOn.pi` does NOT exist in this build; `Continuous.pi` and `continuous_pi` do.
- s9 step 3: replaced the STALE doc comment above `exists_chain_roots` with an accurate
  WARNING (the two pole obstructions, the exact Wolfram witness, and the two extra
  hypotheses `hden1'`/`hden2'` that close them). Added import
  `Mathlib.Topology.Order.IntermediateValue`.
- s9 step 4: FOUR MORE helpers PROVED, first try, 0 diagnostics — these are the crux of the
  obstruction, machine-checked in this file:
  * `chainProjN_of_den_zero {n} (P g w : Fin n → ℝ) (h : yNBY P g = 0) : chainProjN P g w = w`
  * `chainConicPt_of_den_zero {n} (P q₀ d : Fin n → ℝ) (h : yBdotY P d d = 0) :
     chainConicPt P q₀ d = q₀`
  * `chainStep2'_of_den_zero {n} (P g w₁ w₂ : Fin n → ℝ) (x : ℝ) (h : yNBY P g = 0) :
     chainStep2 P g w₁ w₂ x = yConicY P (w₁ + x • w₂)`
  * `chainStep3'_of_den_zero {n} (P q₀ w₁ w₃ : Fin n → ℝ) (mu : ℝ)
     (h : yBdotY P (mu • w₁ + w₃) (mu • w₁ + w₃) = 0) : chainStep3 P q₀ w₁ w₃ mu = psumY q₀ 3`
  (each is a one-line `simp [def, h]`; the last two say the reduced value at a pole is a
  *fixed* number, which is exactly why a strict sign change at the endpoints of the `μ`
  interval need not yield a root.)
- s9 step 5: **TWO MORE PROVED, and they are the `I₀`-half of the theorem.**
  * `exists_zero_of_sign_change_on {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
       (hf : ContinuousOn f (Set.Icc a b)) (hs : f a * f b < 0) : ∃ t ∈ Set.Ioo a b, f t = 0`
    — a strict sign change at the two endpoints of a closed interval gives a root in its
    INTERIOR. Takes `ContinuousOn` on the closed interval (step 3 only has that).
  * `exists_chain_roots_at_centre (I₀) (c₁ c₂ c₃ c₄ eps₁ eps₂ eps₃ eps₄) (heps) (h1) (h2)
       (h3) (h4) (hpole2) (hpole3) : ∃ lam x mu kappa, |lam-c₁| < eps₁ ∧ … ∧
       chainStep4' I₀ lam x mu kappa = 0` — i.e. **exactly the conclusion of
    `exists_chain_roots` with `U := {I₀}` and `I := I₀`**, proved by four
    `exists_zero_of_sign_change_on` applications, with the two extra hypotheses stated on
    the CLOSED box (`≤`, so the end faces are covered):
    `hpole2 : ∀ lam, |lam - c₁| ≤ eps₁ → yNBY (chainP I₀ lam) I₀.g ≠ 0` and
    `hpole3 : ∀ lam x mu, |lam-c₁| ≤ eps₁ → |x-c₂| ≤ eps₂ → |mu-c₃| ≤ eps₃ →
      yBdotY (chainP I₀ lam) (chainD I₀ lam mu) (chainD I₀ lam mu) ≠ 0`.
    `lean_verify`: axioms = propext / Classical.choice / Quot.sound, **no `sorryAx`**.
- s9 step 6: toolkit facts for the IVT route (each cost a round, all now in the file):
  * `Set.Icc` membership is the DIRECT form: `Set.mem_Icc.mpr ⟨h1, h2⟩` with `h1 : f a ≤ 0`,
    `h2 : 0 ≤ f b`, and `Set.mem_Icc.mp` gives `a ≤ t`/`t ≤ b`. It does **NOT** take the
    sorted (min/max) pair, so the case `f b < 0 < f a` cannot be discharged that way — the
    fix used is to apply the oriented case to `-f` (its endpoint values are then oriented).
  * `lt_or_gt_of_ne : a ≠ b → a < b ∨ b < a`, so applied to `f a ≠ 0` the FIRST branch is
    `f a < 0` and the second `0 < f a` (the obvious reading is the other way round).
  * `intermediate_value_Icc hab hf hz` with `hab : a ≤ b`, `hf : ContinuousOn f (Icc a b)`,
    `hz : 0 ∈ Icc (f a) (f b)`; the result is destructured as `⟨t, ht, hft⟩` and `ht` must
    be opened with `Set.mem_Icc.mp`.
  * `Set.Icc`/`Set.Ioo` must be written qualified (no `open Set` in this file, and the bare
    `Icc`/`Ioo` names are unknown).
  * `h.ne' : a < b → b ≠ a` is the convenient "endpoint value is nonzero"; `ne_of_gt` in this
    build is NOT the expected orientation. `mul_pos_of_neg_of_neg` (not `mul_neg_of_...`).
  * `linarith` does NOT split conjunctive hypotheses: `constructor <;> linarith` needs
    `[heps.2.2.1]` style hints when positivity is required.
  * Also: the `Continuous` form of step 2 needs NO denominator hypothesis at all
    (`yConicY P (w̃₁ + x • w̃₂)` is a quadratic in `x` and the projections do not involve
    `x`); I kept the hypothesis as `_hden` for the API, which is why the linter is quiet.
- s9 step 7: FINAL. `lake_check Pptc/TotallyReal/Certificate.lean` = **exit 0, no errors**
  (run twice; the second run is after the cosmetic `_hden` rename). Whole-file LSP
  diagnostics: 0 errors, and the other two agents' declarations are intact
  (`exists_open_good7` 1759, `exists_open_good8` 1779, `exists_oddTschirnhaus` 3587,
  `stepRoots_Pconstructible` 2777, `chainBLift_Pconstructible` 3244, plus their
  `private` helpers). The ONLY warning in my range is the intended `sorry` of
  `exists_chain_roots` (line 778). All other warnings (343, 1669, 1759, 1779, 1915, 1923,
  2008, 2016, 2231, 2701, 2702, 3258) are pre-existing or in other agents' ranges.
## Session 10a (me: `exists_open_good7` / `exists_open_good8`) — BLOCKED: statements are FALSE
- s10 step 1: read the log + `exists_open_good7/8` (1762-1790) + their doc comments. **The
  statements as given in my brief are false, and no hypothesis can repair them**: the middle
  conjunct `∀ I ∈ U, psumY I.a 1 = 0 ∧ psumY I.b 1 = 0 ∧ psumY I.g 1 = 0` cannot hold on any
  nonempty open `U`, because `I.a` is a *free* slot of the 6-fold product `ChainYInputs n` and
  `I ↦ ∑ᵢ I.aᵢ` is a nonconstant continuous function. The brief's item 1 ("the set is open") is
  the one false premise; session 8b already proved the corrected fact (`s1_closed`: the set is
  CLOSED) and the on-disk doc comments still say FALSE, so the brief's claim that "their doc
  comments are current and correct" is out of date. Deliverable in its place: a machine-checked
  refutation (`no_open_s1`, `not_exists_open_s1`, `centre7_not_open_s1`, `centre8_not_open_s1`),
  helpers inserted immediately above `exists_open_good7` as instructed.
- s10 step 2: **REFUTATION PROVED and machine-checked**, helpers inserted immediately above
  `exists_open_good7` (file lines 1716-1841), diagnostics clean over the whole file (0 errors),
  `lean_verify` = propext / Classical.choice / Quot.sound, **no `sorryAx`**:
  * `private def s1_shift (I) (t) := mk (fun i => I.a i + t) I.b I.g I.w1 I.w2 I.w3`
  * `private theorem s1_shift_zero (I) : s1_shift I 0 = I` (`obtain ⟨a,b,g,w1,w2,w3⟩ := I;
    simp only [s1_shift, ChainYInputs.mk, ChainYInputs.a/.b/.g/.w1/.w2/.w3, add_zero]`
    — the six accessors are needed, `mk` alone leaves the goal open, and product eta is NOT a
    simp lemma here so `I` must be destructured first)
  * `private theorem continuous_s1_shift (I) : Continuous fun t => s1_shift I t`
    (`continuous_pi` + `Continuous.prodMk`, nested right, five `continuous_const`)
  * `private theorem sum_fin_const (m) (t) : ∑ _i : Fin m, t = (m : ℝ) * t`
    (induction + `Fin.sum_univ_succ` + `push_cast` + `ring`)
  * `private theorem psumY_s1_shift (I) (t) : psumY (s1_shift I t).a 1 = psumY I.a 1 + (n:ℝ)*t`
    (one `simp only [..., Finset.sum_add_distrib, ← sum_fin_const]`)
  * `theorem no_open_s1 {n} (I₀) (hn : 0 < n) (hzero : psumY I₀.a 1 = 0) (U) (hU) (hI₀) :
    ∃ I ∈ U, psumY I.a 1 ≠ 0` — route: `hU.preimage (continuous_s1_shift I₀)` then
    `IsOpen.mem_nhds` gives the preimage in `nhds 0`; `Metric.mem_nhds_iff` gives `r > 0`;
    take `t = r/2` (`Real.dist_eq` + `abs_of_nonneg`; `abs_of_pos` in this build wants `0 <`,
    not `0 ≤`).
  * `theorem not_exists_open_s1`, `theorem centre7_not_open_s1`, `theorem centre8_not_open_s1`
    (the last two by `not_exists_open_s1 centre7/8 (by norm_num) centre7/8_s1.1`).
  GOTCHA: `Filter.Tendsto` here is `map f l₁ ≤ l₂`, so it does NOT apply to a preimage; use
  `IsOpen.preimage` + `IsOpen.mem_nhds` instead of `Continuous.tendsto`.
- s10 step 3: doc comments updated (3 edits, all in my region): the `/-! #### The S₁ input
  conditions` section header no longer claims the conditions are "open, so intersecting is
  free" (that was the false premise the brief inherited); `exists_open_good7`'s obstruction 1
  now cites `no_open_s1`/`centre7_not_open_s1` as a formal refutation, its "what is proved"
  paragraph and the `exists_open_good8` twin were updated to match. Statements UNCHANGED.
- s10 FINAL: `lake_check Pptc/TotallyReal/Certificate.lean` = **exit 0, no errors**. `sorry`
  warnings only at 778 (`exists_chain_roots`, other agent's) and 1907/1928
  (`exists_open_good7`/`exists_open_good8`, mine and deliberate); everything else is
  pre-existing style noise at 343/1678/2064/2072/2157/2165/2380/2850/2851/3407. Whole-file LSP
  diagnostics: 0 errors. `rg '^\s*sorry$'` finds exactly 3 lines: 804, 1915, 1936.
  `lean_verify Pconstructible.exists_oddTschirnhaus` = propext / **sorryAx** /
  Classical.choice / Quot.sound — the `sorryAx` is inherited from the three remaining sorries
  (`exists_chain_roots`, `exists_open_good7`, `exists_open_good8`), NOT from my work; my new
  declarations are all `propext / Classical.choice / Quot.sound`.
- exists_open_good7: **STUCK — the statement is FALSE, not a missing hypothesis.** Kept the
  `sorry`; the middle conjunct is refuted by `centre7_not_open_s1`, and the on-disk WARNING doc
  comment (three independent obstructions) is correct and now cross-references the proofs.
- exists_open_good8: **STUCK — identical**, refuted by `centre8_not_open_s1`. `sorry` kept.
- WHAT A REPAIR WOULD HAVE TO LOOK LIKE (for the caller): neither obstruction is in the
  hypotheses, so no amount of `hmon`/`hnat`/`hsep`/`hcoeff`/`hαs`/`hnd` helps. The shape that
  `exists_oddTschirnhaus` actually needs is already in the file as `exists_b_good_of_PC_roots`
  (a `hgood` *hypothesis*: `∀ Y ∈ U, ∃ lam x mu kappa, ChainGood Y … ∧ PC … ∧ S₁=S₃=S₅=0`), fed
  by `exists_Pconstructible_lift`. Any true replacement of `exists_open_good7/8` must (i) drop
  the input-side `S₁` conjunct and obtain `S₁` from the witness, and (ii) either restrict `U`
  to inputs of the form `chainBtoY αs b` with `b` P-constructible, or drop the four
  `PConstructible` conjuncts (they are impossible on a generic open set, session 8b's
  countability argument), and (iii) pin the witnesses in a small box for the `Injective`
  conjunct.
- exists_chain_roots: **STUCK — the statement is FALSE, not merely hard.** The four IVTs it
  needs cannot all be run: at a pole of `yBdotY P d d` the step-3 function takes the
  reduced value `psumY q₀ 3`, and there are step-3 configurations with a strict sign change
  at `c₃ ∓ eps₃` and NO root in the interval (exact witness in the s9 step 1 entry, verified
  in Wolfram, and its Lean content is `chainStep3'_of_den_zero`). `I₀ ∈ U` forces a solution
  at `I₀`, so no proof exists. `sorry` kept; the WARNING doc comment above the theorem now
  states the obstruction, the witness, and the exact fix (`hden1'`/`hden2'` on the whole
  box, with `≤` so the end faces are covered). The `I₀`-half of the fixed statement is
  PROVED as `exists_chain_roots_at_centre`; what remains is the input direction
  (`exists_tube_prod` + the sign transfer), which is the design the brief describes and which
  nothing in the stated hypotheses obstructs.

## Session 10 (me: exists_chain_roots, input direction / the tube argument)
- s10 step 0: START. Log + file read. Confirmed: everything up to line 734 is proved (exists_chain_roots_at_centre at 685);
  exists_tube_prod is NOT in the file (lost in the session-2 damage), so it must be re-proved. My helpers go
  immediately above exists_chain_roots (line 778). Plan: generic chain helper with full uniformity in the box
  of earlier parameters + hden1/hden2 on the whole closed box. Not yet written in Lean.

## Session 11 (me: `exists_chain_roots`, the INPUT direction only)
Goal (Lean syntax), target `pptc/Pptc/TotallyReal/Certificate.lean`:
```
theorem exists_chain_roots (I₀ : ChainYInputs n) (c₁ c₂ c₃ c₄ eps₁ eps₂ eps₃ eps₄ : ℝ)
  (heps) (h1) (h2) (h3) (h4) (hden1) (hden2)
  (hpole1 : ∀ lam, |lam - c₁| ≤ eps₁ → yNBY (chainP I₀ lam) I₀.g ≠ 0)
  (hpole2 : ∀ lam x mu, |lam - c₁| ≤ eps₁ → |x - c₂| ≤ eps₂ → |mu - c₃| ≤ eps₃ →
    yBdotY (chainP I₀ lam) (chainD I₀ lam mu) (chainD I₀ lam mu) ≠ 0) :
  ∃ U : Set (ChainYInputs n), IsOpen U ∧ I₀ ∈ U ∧ ∀ I ∈ U, ∃ lam x mu kappa : ℝ,
    |lam - c₁| < eps₁ ∧ |x - c₂| < eps₂ ∧ |mu - c₃| < eps₃ ∧ |kappa - c₄| < eps₄ ∧
    chainStep1' I lam = 0 ∧ chainStep2' I lam x = 0 ∧ chainStep3' I lam x mu = 0 ∧
    chainStep4' I lam x mu kappa = 0
```
Plan: re-prove `exists_tube_prod` (generic), then a uniform-sign transfer over a tube, then
four 1-D IVTs per `I ∈ U`. The `I₀`-half is already proved as `exists_chain_roots_at_centre`.
- s11 step 1: START. Read log (all 10 prior sessions) + the theorem region.
- s11 DESIGN (settled, recorded before writing Lean):
  * tube lemma `exists_tube_prod` + per-step: (a) one-variable compactness at `I₀` over the compact
    parameter box gives a uniform margin `δ>0` (`IsCompact.exists_forall_le'`), (b) the tube
    lemma applied to the open set `{q | δ < φ± q}` gives `∃ W open ∋ I₀` where the margin holds
    uniformly over the box, (c) IVT on `[c_k-eps_k+δ, c_k+eps_k-δ]` puts the step-`k` root in a
    FIXED compact box strictly inside the open box. Step 1 needs NO margin: shrink the box once,
    in ONE VARIABLE, at `I₀`, via `Metric.continuousAt_iff` in `ℝ` (sign preserved on
    `[c₁-eps₁, c₁-eps₁+η]`, take `d₁ = eps₁ - min (η/2) (eps₁/2)`), then the sign sets in `I` are
    open. So NO metric on `ChainYInputs n` is needed anywhere.
  * required continuity: `ContinuousOn` of the ±endpoint functions on the open sets
    `Ω₂ = {yNBY (chainP I lam) I.g ≠ 0}` (steps 2,3,4) and `Ω₃` (steps 3,4).


## Session 12 (me: exists_open_good7 / exists_open_good8 - S1 conjunct removed by orchestrator)
- s12 step 0: START. Targets: exists_open_good7 (1907) / exists_open_good8 (1926), helpers immediately above.
  Statements now have NO S1 conjunct but KEEP the four PConstructible conjuncts. Plan: check the
  countability obstruction (session 8b step 1: step 1 is a cubic in a perturbation of I.a with leading
  coefficient 1, PC reals are countable => the PC conjuncts are unsatisfiable on any open U), then
  certify hpole1/hpole2 at radius 1/3 (hpole1 = positive-definite quadratic in lam; hpole2 =
  2-variable rational, may have a real pole near mu0 - 1/4 per session 4's note).
- s12 step 1: **KEY CORRECTION - yNBY YP Yv = ymoment2Y YP Yv 2 1 = SUM YP_i^2 * Yv_i** (YSpace.lean:785), i.e. the N_P pairing is a QUADRATIC moment, not linear. My first pole arithmetic used SUM P_i g_i^2 and was wrong. Consequence: yNBY (chainP I lam) I.g is a QUADRATIC in lam, not linear.
- s12 step 2: **FOUR NEW MACHINE-CHECKED LEMMAS ADDED (immediately above exists_open_good7, 0 errors, lean_verify = propext/Classical.choice/Quot.sound, no sorryAx):**
  * centre7_hpole1 (lam) : 0 < yNBY (chainP centre7 lam) centre7g - the quadratic is
    378*lam^2 - 544*lam + 244, disc -72992 < 0, so **hpole1 holds at EVERY radius** (not just 1/3).
    Proof: one norm_num for the polynomial identity + 4A(Q) = (2A*lam+B)^2 + (4AC-B^2) + nlinarith.
  * centre8_hpole1 (lam) : 0 < yNBY (chainP centre8 lam) centre8g - 14*lam^2 - lam + 71/2, disc -1987.
  * private continuous_centre7_denom2' / continuous_centre8_denom2' : the step-3 DENOMINATOR is
    Continuous in mu on all of R (its only division is by the CONSTANT Ng(c1) = 244 / 71/2).
  * centre7_step3_pole : exists mu in Ioo (mu0 - 1/3) (mu0 + 1/3), yBdotY (chainP centre7 0) (chainD centre7 0 mu) (chainD centre7 0 mu) = 0;
    centre8_step3_pole the n=8 twin; and the corollaries centre7_hpole2_false / centre8_hpole2_false,
    which REFUTE exists_chain_roots's hpole2 at the certified radius 1/3 at BOTH centres.
- s12 step 3: DOC COMMENTS REWRITTEN for both theorems (in scope). The stale S1-input-conjunct obstruction 1 is replaced by: (1) the four PConstructible conjuncts, countability argument written out in full (I t, cubic in t with leading coefficient 1, countable union of finite sets, interval vs countable); (2) NEW - exists_chain_roots is inapplicable because hpole2 is refuted (centre7_hpole2_false / centre8_hpole2_false) with the two concrete quadratics and the pole locations, plus the two escapes (chainStep3Cleared, or re-centre c3); (3) the Injective obstruction (kept). Statements UNCHANGED, both sorries kept deliberately. Whole-file diagnostics: 0 errors.
- s12 FINAL: lake_check Pptc/TotallyReal/Certificate.lean = **exit 0, NO ERRORS**. Warnings: 778
  (exists_chain_roots sorry, other agent), 2134/2163 (my two DELIBERATE sorries), 3933
  (exists_oddTschirnhaus sorry, other agent's range - it had been proved in session 9 but is a
  sorry again), 1901/1924 (my two 	ac1 <;> tac2 style warnings), 343/2613/3083/3084 (pre-existing
  <;>), 1678 (Set.mem_setOf_eq deprecated, session 8b's helper), 2297/2305/2390/2398/3640
  (pre-existing unused hden / unused simp arg, other regions). exists_tube_prod is still NOT in
  the file (only mentioned in doc comments), so the exists_chain_roots agent has not landed yet.
- lean_verify: centre7_hpole1, centre7_step3_pole, centre7_hpole2_false,
  centre8_hpole2_false all = propext/Classical.choice/Quot.sound, **no sorryAx**.
  Pconstructible.exists_oddTschirnhaus = propext/**sorryAx**/Classical.choice/Quot.sound - the
  sorryAx comes from the 3 remaining sorries (exists_chain_roots, exists_open_good7/8), not mine.
- ANSWERS TO THE BRIEF'S QUESTIONS (see the report for the long form):
  * RADIUS CERTIFIED: 1/3 in lam is fine (hpole1 holds at EVERY radius); but in mu, the largest
    radius compatible with pole-freeness at lam = c1 is < 0.0825 for n=7 and < 0.2778 for n=8,
    both SMALLER than the 1/3 that centre7_signs/centre8_signs certify. => hpole2 is FALSE at
    the certified radius at BOTH centres, machine-checked. So exists_chain_roots cannot be
    applied at either centre and the plan's route is blocked at step 1.
  * NO root hypotheses added to either statement: the statements are false for reasons about the
    inputs (countability of the P-constructible reals; hpole2), which no hmon/hcoef/has
    hypothesis can affect. Adding them would have been pointless.
  * exists_PC_inputs_s1 NOT added: it is not a local lemma. It needs a P-constructible  lying
    in the CLOSED set {psumY (yvec as b).? 1 = 0} for all six slots, i.e. a genuine
    countability-constrained existence statement, and it belongs to the exists_oddTschirnhaus
    region (line 3915+), not mine.
- exists_open_good7: **STUCK/FALSE - statement is false, sorry kept deliberately.** Not proved, and
  in my judgement unprovable as stated. Two independent obstructions, one of them new and
  machine-checked here: (a) the four PConstructible conjuncts (countability argument, written
  out in full in the doc comment; NOT formalised, it would need a countability theorem for
  PConstructible that does not exist in the project - YSpace.lean:508 only records it in a
  comment); (b) centre7_hpole2_false.
- exists_open_good8: **STUCK/FALSE - identical**, with centre8_hpole2_false.
