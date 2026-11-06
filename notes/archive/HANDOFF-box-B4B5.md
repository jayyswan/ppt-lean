# HANDOFF box B4 (Jacobi W3 application) + B5

## B4 goal
In `pptc/Pptc/Jacobi.lean`:
1. add `import Pptc.Box` next to `import Pptc.Basic`.
2. delete `ellipseCoArc_PConstructibleCurve` (~494-515).
3. rewrite `ellipticEAm_Pconstructible_of_mem_Icc` (~523-574) with box, keeping statement byte-for-byte.
4. rewrite its docstring (~517-522).
5. update `/-! #### Why the first kind resists` (~687-745): four -> five primitives, verdict unchanged.

## Plan
`hA : PConstructibleCurve (ellipseParam b '' Icc 0 φ)`; `arc_xendpoint_Pconstructible` gives `Real.sin φ`; `φ = arcsin (sin φ)`; `arcsin_Pconstructible`.

- [start] created log; reading Jacobi.lean and confirming lemma names.
- [info] `ellipseParam b θ = (Real.sin θ, b * Real.cos θ)` (Basic.lean:3375). `Real.strictMonoOn_sin : StrictMonoOn Real.sin (Icc (-(π/2)) (π/2))`; `StrictMonoOn.mono`, `.monotoneOn` in `Mathlib.Order.Monotone.Defs`; `MonotoneOn.mono`; `Real.arcsin_sin (h₁) (h₂)`; `Real.continuous_sin/cos`; `ContinuousOn.const_mul`; `arcsin_Pconstructible` @[pconstructible] (Basic.lean:2832).
- [done] Added `import Pptc.Box`. Deleted `ellipseCoArc_PConstructibleCurve`.
- [done] Rewrote docstring + proof body of `ellipticEAm_Pconstructible_of_mem_Icc`; kept signature lines identical. Updated §4.1 "four -> five" prose.
- [wait] diagnostics on Jacobi.lean timed out at transport; retrying.
- [fix] `simpa [ellipseParam]` did not unfold for the `hcont` goal; used bare term (defeq). `linarith` needed explicit `ht.1`/`ht.2` from the Icc membership. `set φ := … with hφdef` already rewrites the goal, so `rw [← hφdef]` was removed.
- [done] Whole-file diagnostics clean (success=true, no errors/warnings). Statement `ellipticEAm_Pconstructible_of_mem_Icc` byte-identical (lines 503-505). New proof body lines 506-541.
- [info] File 755 -> 730 lines (net -25 for B4). The `ellipseCoParam` cluster (`ellipseCoParam`, `ellipseCoParam_eq`, `speed_ellipseCoParam`, `arcLengthOf_ellipseCoParam`, lines 431-463) is now DEAD: grep over pptc/Pptc shows no references left after deleting `ellipseCoArc_PConstructibleCurve`.
- [next] lean_verify + lake_check Jacobi.lean.
- [DONE B4] `lean_verify Pconstructible.ellipticEAm_Pconstructible_of_mem_Icc` -> only propext, Classical.choice, Quot.sound. `lake_check Pptc/Jacobi.lean` -> "OK - no errors or warnings".
- §4.1 prose: changed "one of four things" to "one of five", adding the box (coordinate extreme of a compact drawable curve); added that it strengthens arc-length inversion (endpoint recoverable on *open* monotone arcs, no complementary-arc uniqueness argument) and that the load-bearing claim ("`F` is not the arc length of any drawable curve") is untouched, so the verdict is unchanged; final sentence now "only by the fourth and fifth primitives". This is the plan §4.1 wording.
- Files touched: Pptc/Jacobi.lean only (import Pptc.Box added; no other files changed).

## B5 goal
In `pptc/Pptc/Basic.lean`: add `import Pptc.Box`; rewrite `cos_sin_Pconstructible_of_mem_Icc`
(statement byte-identical) via the box endpoint extractor; rewrite the `### Sine and cosine`
docstring; adjust `angle_eq_of_cos_eq_of_sin_eq` docstring; keep `circleArc_PConstructibleCurve`.

## B5 log
- [start] created log section. Read Box.lean (W3 antitone extractor names confirmed:
  `arc_xendpoint_antitone_Pconstructible`). Confirmed callers of
  `cos_sin_Pconstructible_of_mem_Icc`: Basic.lean:2634,2635 and Jacobi.lean:381 (docstring only).
- [done] Added `import Pptc.Box` after `import Pptc.Tactic`. Rewrote section docstring,
  `angle_eq_of_cos_eq_of_sin_eq` comment, and `cos_sin_Pconstructible_of_mem_Icc`.
- [fix] Errors fixed: hanti needed explicit `hsub` + `simpa only` (goal f was the projected
  lambda, not `Real.cos`); `fun_prop` needed `change` to unfold `circleArcParam`/`circleParam`
  first; `PConstructible.mul hcos hcos` not defeq `cos^2`, used `sq_Pconstructible hcos`.
- [ok] Region diagnostics 2570-2620: success, no items.
- [DONE B5] Whole-file `lean_diagnostic_messages Pptc/Basic.lean` -> success, no errors/warnings
  (no regression from exposing Box's `@[pconstructible_cond]` rules to Basic's tactic calls).
- [DONE B5] `lean_verify Pconstructible.cos_sin_Pconstructible_of_mem_Icc` -> only `propext`,
  `Classical.choice`, `Quot.sound`. `lake_check Pptc/Basic.lean` -> "OK - no errors or warnings".
- Proof now: comment 2577-2582, statement 2583-2585 (byte-identical), body 2586-2612.
  Old body was 2580-2607 (28 lines), new body 2585-2612 (28 lines): proof body net 0
  (the ~16-line `hinter`/`inter_x` block is gone, replaced by `hanti`/`hcont`/sqrt setup).
  File 5213 -> 5218 lines: +1 import, +3 section docstring (17 -> 20), +1 theorem comment,
  +0 body.
- [note] `Pptc/Jacobi.lean:381-387` still describes `cos_sin_Pconstructible_of_mem_Icc` as the
  two-abutting-arc `inter_x`/`inter_y` construction, but the lemma is now box-based (B4 already
  switched `ellipticEAm_Pconstructible_of_mem_Icc` to the box). Stale after B4, out of B5 scope
  (`Basic.lean` only); flagging for a follow-up.
- Files touched by B5: `Pptc/Basic.lean` only.
