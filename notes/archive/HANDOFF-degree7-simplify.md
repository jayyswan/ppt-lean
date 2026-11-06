# HANDOFF: simplify Pptc/DegreeSeven.lean

Baseline committed: 98d94a6 (start size 304518 bytes, ~? lines).
Reach script baseline: 245 reachable, 56 unreachable, 846 lines.

## Phase A — delete dead code  DONE
- [x] deleted all listed declarations + lightCone_cubic_no_projective_zero + stale Route-to-E2 doc
- 6146 -> 5406 lines (-740). Compiles (lake_check exit 0).
- Reach after: only deferred neg_/smul_entries_Pconstructible + pivotEquiv_* remain (32 lines).

## Phase B
- [x] B1 factor four trace-value lemmas into `trace_eq_of_value`/`exists_value_trace`/`exists_value_pair`. 5406 -> 5331 lines. Compiles, committed.
- [x] B2 moved `ofReal_multiset_sum` and `eq_zero_of_vanishes_on_roots` up, deleted private duplicates. 5331 -> 5304 lines. Compiles, committed.
- [x] B3 Mathlib replacements (`Matrix.sum_apply`, `Polynomial.finsetSum_coeff`), inlined `traceH_Pconstructible`. 5304 -> 5279 lines. Compiles, committed.
- [x] B4 unify real `companion7` with generic `companion7'` eigenvectors; deleted real duplicates. 5283 -> 5226 lines. Compiles, committed.

## Phase C — shorter s>=2 argument  DONE
- [x] C1 move Tschirnhaus engine to new section after `stereo_Pconstructible`.
- [x] C2 expose isotropic parameter `t` (`exists_pos_isotropic_param`).
- [x] C3 add `exists_cone_point_Pconstructible`, `exists_orth_projection`,
      `exists_orth_neg_Pconstructible`, `exists_isotropic_orth_Pconstructible`.
- [x] C4 rewrite `exists_tschirnhaus_traces`; reuse cone point in `root_..._one_conjugate_pair`.
      Compiles, committed.

## Phase D — second dead-code sweep  DONE
- [x] deleted all 44 remaining unreachable decls (ScratchC2 diagonalisation, hyper, pivot,
      two_neg/two_pos, bilin_congr/diag, mulVec_*). 5370 -> 4532 lines.
- [x] removed 4 now-unused imports; updated header docstring and stale section header.
- Reach after: 0 unreachable.

## Follow-up cleanup (beyond plan)  DONE
- added `qform_neg`/`bilin_neg`; removed 3 inline `(-A)` unfolding proofs and the unused
  `_hAsym` argument of `exists_orth_neg_Pconstructible`.
- dropped unused `[DecidableEq *]` args from `Finset.sum_Pconstructible`,
  `trace_pow_eq_sum_eigen`, `companion7'_trace_pow`, `companion7'_trace_aeval`.
- removed unused simp args, `show`→`change`/deleted no-op lines, split two long lines.
- `lake build Pptc.DegreeSeven`: **zero warnings**; axioms still allowed set; ScratchQuad clean.
- Final size 4528 lines / ~225 KB. Committed.

## Final verification  DONE
- Full-file `lake_check`: exit 0 (only pre-existing warnings at lines ~486–541).
- `lake build Pptc.DegreeSeven`: Build completed successfully.
- Axioms of `Pconstructible.root_Pconstructible_of_nonreal_root`: [propext, Classical.choice,
  Quot.sound] — exactly the allowed set.
- `lake env lean Pptc/ScratchQuad.lean`: compiles clean.
- Final size: 4526 lines / 225161 bytes (from 6146 lines at start; ≈ -1620 lines, -26%).
- Reachability: 0 unreachable declarations.
- 11 local commits on `main`; **not pushed**.
