# HANDOFF WP1 — generalise psi=X trace-form apparatus to arbitrary A

Target file: `pptc/Pptc/NonicMeyer.lean`
Deliverables: `psOf`, `gramOf`, `tzPolOf`, `gramOf_symm`, `trace_tzPolOf`,
`trace_sq_tzPolOf`, `gram_eq_trace_shift`, `tschirnhausDatum_of_signs`
+ specialisation bridges `ps9`, `gramTraceZero`, `traceZeroPol` (keep existing names).

Plan: read PLAN WP1 + current file; generalise existing proofs by replacing
`companion9' q` with `A`; add HasseMinkowski import for `meyer`.

## Progress
- (start) created log.
- Located APIs: `Pptc.HasseMinkowski.meyer` (Main.lean:199), `Indefinite` (Basic.lean:231),
  `Isotropic := ∃ x, x≠0 ∧ Q x=0`, `toQuadraticForm'` = bilinear self-pairing,
  `baseChange_tmul`, `Module.finrank_fin_fun`, `Polynomial.aeval_comp`,
  `Polynomial.le_natDegree_of_ne_zero`, `Polynomial.eq_C_of_natDegree_le_zero`.
- Inserted import `Pptc.HasseMinkowski.Main` and the whole general `psOf/gramOf/tzPolOf`
  block + `tschirnhausDatum_of_signs` before the assembly section. Not yet compiled.
- First diagnostics: (1) `trace_aeval_shift_sqOf` needed `rw [← map_pow, hp2, ...]`;
  (2) `hSt` needed `rw [hp, map_pow]` not `←`; (3) `₋`/`₊` subscripts illegal -> renamed
  vneg/vpos; (4) `TschirnhausDatum` used before its def -> moved the def earlier;
  (5) `hA0` proof clobbered RHS via hψC -> used `conv_lhs`. Re-running diagnostics.
- Second diagnostics: only 2 issues left. `hvgram` rewrote `hvQ` instead of the goal; fixed
  to `rw [← hG, ← hQapply v]; exact hvQ`. Also dropped an unused simp arg on `hrank`.
- `lean_diagnostic_messages`: success=true, zero diagnostics. No `sorry`/`axiom`.
- Only line >100 chars is the pre-existing `TschirnhausDatum` def line (unchanged, no warning).
- Next: final `lake_check`, `lean_verify`, then report.
- DONE. `lake_check Pptc/NonicMeyer.lean`: "OK - no errors or warnings".
  `lean_verify Pconstructible.tschirnhausDatum_of_signs`: axioms
  [propext, Classical.choice, Quot.sound] only.
- Final declaration lines: TschirnhausDatum 505, psOf 511, gramOf 514, tzPolOf 518,
  gramOf_symm 523, aeval_sum_shiftOf 529, trace_aeval_sum_shiftOf 538,
  trace_aeval_shift_sqOf 546, trace_tzPolOf 561, sum_gramOf_eq 569, trace_sq_tzPolOf 588,
  coeff_tzPolOf 627, tzPolOf_natDegree_le 639, gram_eq_trace_shift 647,
  ps9_eq_psOf 657, gramTraceZero_eq_gramOf 660, traceZeroPol_eq_tzPolOf 663,
  gramOf_algebraMap_eq_zero 667, tschirnhausDatum_of_signs 687.
  Old names untouched: exists_tschirnhaus9_of_isotropic 764,
  exists_tschirnhaus9_of_isotropic_comp 781, exists_tschirnhaus9_of_datum 796.
