# HANDOFF: Pptc.TotallyReal.Main — seven sorried theorems

Target file: `pptc/Pptc/TotallyReal/Main.lean` (module `Pptc.TotallyReal.Main`)

Goals (in file order):
1. `recoveryPoly_eval_root : (recoveryPoly αs b β).eval (αs i) = 0`
2. `recoveryPoly_degree_lt : (recoveryPoly αs b β).natDegree < n`
3. `recoveryPoly_ne : recoveryPoly αs b (yvec αs b ⟨0,h0⟩) ≠ 0`
4. `root_Pconstructible_totallyReal_seven` (Thm 7, totally real)
5. `root_Pconstructible_deg7_coeffs` (Thm 7 in full)
6. `root_Pconstructible_totallyReal_eight` (Thm 8, totally real)
7. `root_Pconstructible_deg8_coeffs` (Thm 8 in full)

Plan: read PLAN §2.7/§4.5 + module docstring; prove 1-3 directly; factor a local
`root_Pconstructible_of_seven_shaped`-style helper shared by 4 and 6; reuse
`DegreeSeven.lean` case analysis for 5 and 7.

## Log
- started; creating log
- read PLAN 2.7/4.5 + docstring. YSpace: prodSubY_yvec_eq_charpoly_aeval, prodSubY_yvec_coeff_Pconstructible, trace_pow_eq_psumY, psum_yvec_Pconstructible are all still sorry. Certificate.exists_oddTschirnhaus is sorry. DegreeSeven is imported transitively (via Newton) so nonreal/nonSeparable available. NOTE: theorem 4 stmt has no hsep, so (X-1)^7 shows it needs the non-separable branch too.
- nonreal-root helper FULLY PROVED in scratch: exists_nonreal_root_of_not_splits (map_roots_le_of_injective + Separable.map + splits_iff_card_roots + le_iff_subset). Key gotcha: rw with hz1 : z = ?z.re corrupts z.re subterms; use a fresh w : R with w = z.re.
- WROTE full Main.lean: 1,3 done; 2 sorry (statement FALSE at n=0); 4 done; 5 done; 6 sorry (needs degree-8 nonSeparable); 7 two sorries (needs degree-8 nonreal_root + degree-8 nonSeparable). Now iterating with lean_diagnostic_messages.
- scratch full-body check: found ~15 fixable issues (splits_iff_card_roots .mp not .mpr; Multiset.mem_toFinset rw direction; range_orderEmbOfFin no ?; coeff_C' is coeff_C_of_ne_zero; Polynomial.mul_ne_zero -> mul_ne_zero; as is implicit in helper; hqn needs rw [? hnat]; hdeg6 needs rcases hn; hq0 proof). Applying.
- scratch FULL BODY now CLEAN (0 errors) with stubbed YSpace/Certificate interface. Key: hrec takes p.natDegree < n (not <=6) since n=8 only gives <=7. Porting to Main.lean.
- FINAL: Main.lean complete. BLOCKED on the final lake_check: Pptc/TotallyReal/YSpace.lean (edited in parallel) still has 4 errors at lines 862/886/933/963 and its .olean is missing, so import Pptc.TotallyReal.Certificate cannot resolve. lake_check output: Main.lean:19:0 error: object file ...YSpace.olean does not exist. Scratch harness (Pptc/ScratchCheck.lean, now deleted) compiled the whole Main.lean body with 0 errors against stubs of the YSpace/Certificate interface, so Main.lean itself is type-checked modulo those signatures.
- 9:45pm: YSpace.lean unchanged (4 errors, mtime 9:14pm, worker stalled). Scratch file deleted. Deliverable complete except the final whole-file check, which needs YSpace.olean.
- NEW SESSION 10:05pm: YSpace.lean now CLEAN (0 errors, 13 sorries at 516/525/533/539/641/731/737/743/753/761/768/776/793). Certificate.lean still has ~20 errors (psumY/yNBY/yConicY/yBdotY additivity `rw` not unfolding) and was modified 10:05:10pm -- that agent is mid-edit. Main.lean diagnostics unavailable until Certificate compiles. Proceeding to read Main.lean + YSpace API by hand meanwhile.
- recoveryPoly_degree_lt: DONE. Restated with `(h0 : 0 < n)` (the original is false at n=0), proved as a one-line wrapper over recoveryPoly_degree_lt_of_pos (kept). Sole caller root_Pconstructible_of_odd_shaped updated to call recoveryPoly_degree_lt. No sorry remains there.
- root_Pconstructible_of_nonSeparable_eight: DONE (new helper, direct port of DegreeSeven.root_Pconstructible_of_nonSeparable with the `≤ 6` bounds replaced by `≤ 7` and the engine `root_Pconstructible_le_six_coeffs` replaced by Theorem 7 `root_Pconstructible_deg7_coeffs`). Closes 2 of the 4 sorries.
- root_Pconstructible_totallyReal_eight: DONE (non-separable branch now closed).
- root_Pconstructible_deg8_coeffs: 1 sorry left (separable, non-splitting = degree-8 nonreal root). STUCK: needs the degree-8 Bring-Jerrard reduction; Gram/stereo/p1vec/p3vec/Lcomb/qform/Hmat/hermiteForm/Fin 6/sextic are all dimension-fixed to 7. Comment at the site spells this out.
- WAITING on YSpace: other agent filling yBdot_eq_sum/yConicB_eq_sum/yNB_eq_sum. 7 errors (10:10) -> 3 (10:14) -> 2 (10:16, at 730/766). Main.lean cannot be type-checked until YSpace is clean.
- Certificate.lean still in flux (42k->43.5k bytes, mtime 10:06pm). Polling while editing Main.
- Main.lean now has exactly ONE `sorry` (line ~622, the degree-8 nonreal-root branch of root_Pconstructible_deg8_coeffs). Everything else is proved. The other ~90 lines of new helper root_Pconstructible_of_nonSeparable_eight (lines 468-556) are a verbatim port of the degree-7 gcd proof and have NOT yet been type-checked (blocked on Certificate.lean, which is mid-edit by another agent).
- BLOCKED 10:27pm: Certificate.lean (50.9k, mtime 10:23) and YSpace.lean (60.4k, mtime 10:25) are both mid-edit by parallel agents, so lean_diagnostic_messages cannot elaborate Main.lean ("failed_dependencies"). Polling. Recovery: everything else in this file is done; only a final lake_check is outstanding.
- 10:47pm FINAL: lake_check Pptc/TotallyReal/Main.lean => exit 0, NO ERRORS. 11 linter warnings (9 cosmetic unused-var/unused-simp-arg, all pre-existing) + exactly one `declaration uses sorry` at line 589 = root_Pconstructible_deg8_coeffs (degree-8 nonreal-root branch, intentional and documented).
- Final error list found & fixed this session: (1) `omega` failure at old line 87 in recoveryPoly_degree_lt_of_pos (omega cannot see through `max`) -> replaced with `hmax.trans (max_le h1 (Nat.zero_le _))`; (2) my own re-indentation bug: the MISSING comment at 4 spaces made the inner `· sorry` a branch of the OUTER `by_cases hsep`, so the last `·` became a spurious third branch ("No goals to be solved" at 623) -> re-indented the comment to 6 spaces. No signature drift found: Main.lean's uses of bPoly_natDegree_le, bPoly_coeffs_Pconstructible, yvec_eq_bPoly_eval, companionN_charpoly_aeval_isRoot, prodSubY_yvec_eq_charpoly_aeval (6 args), prodSubY_yvec_coeff_Pconstructible (8 args), exists_oddTschirnhaus (5 args), exists_cubic_seven, exists_quartic_eight all match the current YSpace/Certificate/Newton signatures.
- (superseding the entries above) The old "4 remaining sorries" list is now OUT OF DATE: 3 of those 4 are closed. `root_Pconstructible_deg8_coeffs` has the single remaining `sorry` (degree-8 nonreal-root branch) and nothing else in Main.lean is sorry. recoveryPoly_degree_lt (statement false at n=0), totallyReal_eight non-separable branch (needs degree-8 nonSeparable), deg8_coeffs nonreal branch (needs degree-8 nonreal_root), deg8_coeffs non-separable branch (same degree-8 nonSeparable). Theorems 1,3,4,5 are fully proved; 6 and 7 are proved in their totally-real / degree<=7 branches.
