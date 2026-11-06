# HANDOFF box B1 (W1+W2) — Pptc/Box.lean

Goal: create `pptc/Pptc/Box.lean` with W1 four-edge API and W2 compactness toolkit.

Target declarations (namespace Pconstructible):
- `box_xmin_Pconstructible`, `box_ymin_Pconstructible`, `box_width_Pconstructible`, `box_height_Pconstructible`
- `isCompact_traced_arc`, `nonempty_traced_arc`

Plan: reflection via `PConstructibleCurve.scale_x/scale_y A (-1)`; `sSup (Neg.neg '' S) = -sInf S`; compactness by `IsCompact.image`; width/height by `.sub`.

- [start] created log; reading PLAN and Defs.
- [info] Mathlib names confirmed: `Real.sSup_neg (s : Set ℝ) : sSup (-s) = -sInf s` (no hyps); `Set.image_neg_eq_neg : (fun x => -x) '' s = -s`; `IsCompact.image`; `IsCompact.image_of_continuousOn`; `isCompact_Icc`; `Set.Nonempty.image`; `Continuous.prodMk`; `ContinuousOn.prodMk`; `ContinuousWithinAt.prodMk`; `Set.nonempty_Icc`.
- [info] Neg-on-Set is scoped `Pointwise` (defined as preimage `{x | -x ∈ s}`), so `open scoped Pointwise` is required.
- [draft] Wrote full Box.lean (W1 4 theorems + helpers, W2 2 theorems). Now diagnosing.
- [fix] `rw [Set.image_image]` only rewrote LHS and was ambiguous on RHS; replaced both scale helpers with direct `ext` membership proofs. `neg_one_Pconstructible` helper: `1-(1+1)` is not defeq `-1`, so convert via `norm_num`.
- [done] `lean_diagnostic_messages` Pptc/Box.lean: success=true, zero errors/warnings. All 6 public lemmas + 3 private helpers elaborate.
- [next] edit Pptc.lean, lean_verify, lake_check, build Pptc.Box.
- [done] Pptc.lean updated: `import Pptc.Box` added after `import Pptc.Tactic`.
- [done] lean_verify x6: each returns only propext, Classical.choice, Quot.sound. Line numbers: xmin 111, ymin 141, width 164, height 173 (attrs at 110/140/163/172); isCompact_traced_arc 184; nonempty_traced_arc 198; helpers fst 71, snd 85, neg_one 100.
- [next] lake_check Pptc/Box.lean then lake build Pptc.Box.
- [done] `lake_check Pptc/Box.lean` -> "OK - no errors or warnings".
- [DONE] `lake build Pptc.Box` -> "Built Pptc.Box (45s) / Build completed successfully (2635 jobs)". Deliverable complete.

## Final state
`pptc/Pptc/Box.lean` (namespace `Pconstructible`), imports: `Pptc.Defs`, `Pptc.Tactic`, `Mathlib.Topology.Order.Compact`; `open scoped Pointwise`.
- private `fst_image_scale` (:71), `snd_image_scale` (:85), `neg_one_Pconstructible` (:100)
- `@[pconstructible_cond] box_xmin_Pconstructible` (:111)
- `@[pconstructible_cond] box_ymin_Pconstructible` (:141)
- `@[pconstructible_cond] box_width_Pconstructible` (:164)
- `@[pconstructible_cond] box_height_Pconstructible` (:173)
- `isCompact_traced_arc` (:184), `nonempty_traced_arc` (:198)
`pptc/Pptc.lean` now imports Pptc.Box after Pptc.Tactic.
True Mathlib names: reflection `Real.sSup_neg (s : Set ℝ) : sSup (-s) = -sInf s` (no hyps), `Set.image_neg_eq_neg : (fun x => -x) '' s = -s`; `IsCompact.image`; `IsCompact.image_of_continuousOn`; `isCompact_Icc`; `Continuous.prodMk`; `ContinuousOn.prodMk`; `Set.Nonempty.image`; `Set.nonempty_Icc`.
Nothing unproved.

## B2 (W3) — monotone endpoint extraction
- [start] Appending 4 theorems below `nonempty_traced_arc`: `arc_xendpoint_Pconstructible`, `arc_yendpoint_Pconstructible`, `arc_xendpoint_antitone_Pconstructible`, `arc_yendpoint_antitone_Pconstructible`.
- [info] `IsGreatest.csSup_eq : IsGreatest s a → sSup s = a` (Mathlib.Order.ConditionallyCompletePartialOrder.Basic); `IsLeast.csInf_eq` is its `to_dual`.
- [draft] Wrote all 4. Diagnosing.
- [done] diagnostics clean (success=true, no errors/warnings). Line numbers: arc_xendpoint 214, arc_yendpoint 233, arc_xendpoint_antitone 251, arc_yendpoint_antitone 270.
- [done] lean_verify x4: only propext, Classical.choice, Quot.sound.
- [next] lake_check + lake build Pptc.Box.
- [DONE B2] `lake_check Pptc/Box.lean` -> OK, no errors/warnings. `lake build Pptc.Box` -> "Built Pptc.Box (142s) / Build completed successfully (2635 jobs)". No `sorry`; nothing unproved.
  Lemma names used: `IsGreatest.csSup_eq`, `IsLeast.csInf_eq` (to_dual). Helpers reused: `isCompact_Icc.image_of_continuousOn`, `nonempty_traced_arc`, `box_xmin_Pconstructible`, `box_ymin_Pconstructible`, `PConstructible.box_xmax`, `PConstructible.box_ymax`.

## B3 (W4 + N1) — inverse arc length
- [start] Adding below W3: private `continuousOn_of_hdiff`, private `xendpoint_of_monotone_or_antitone`, private `yendpoint_of_monotone_or_antitone`, public `arcLength_inverse_Pconstructible`, `arcLength_xendpoint_Pconstructible`, `arcLength_yendpoint_Pconstructible`.
- [decision] N1 folded into the W4 section docstring: W4 *is* N1 (x is the independent variable; b is the parameter with G(b)=x). No separate `arcLength_param_Pconstructible` — a `Function.invFun` phrasing would only add a range/strict-mono side condition, no new content.
- [draft] Wrote W4 + convenience forms. Diagnosing.
- [fix] `(fun ...).prodMk` parsed as field projection; use `ContinuousOn.prodMk (fun ...) (fun ...)`.
- [done] diagnostics clean. Lines: continuousOn_of_hdiff 307, xendpoint_of_monotone_or_antitone 316, yendpoint_of_monotone_or_antitone 328, arcLength_inverse_Pconstructible 341, arcLength_xendpoint_Pconstructible 366, arcLength_yendpoint_Pconstructible 384.
- [done] lean_verify x3 (public W4 theorems): only propext, Classical.choice, Quot.sound. lake_check: OK, no errors/warnings.
- [next] lake build Pptc.Box.
- [DONE B3] `lake build Pptc.Box` -> "Built Pptc.Box (173s) / Build completed successfully (2635 jobs)". No `sorry`; nothing unproved. N1 = W4 (folded into section docstring, no separate theorem).
