# HANDOFF: TotallyReal/Certificate.lean dead-end cleanup

Goal: delete abandoned refutation scaffolding (pole-cluster + S₁-closed cluster) from
`Pptc/TotallyReal/Certificate.lean`, rewrite the two section notes that introduce them,
fix dangling docstring refs. No `sorry`, no errors. Do NOT touch other files.

Plan:
1. `rg` every candidate name in `Pptc/TotallyReal` to confirm unused by live decls.
2. Read the two section-note regions and the declaration regions.
3. Delete in reverse line order (bottom-up) to keep line numbers stable.
4. Rewrite section notes.
5. `lean_diagnostic_messages` iteratively, then `lake_check` both files.

Keep list (per task): centre7_hpole1, centre8_hpole1, centre7_s1, centre8_s1,
centre7_denom1/2, centre8_denom1/2, exists_zero_of_sign_change_on,
exists_chain_roots_at_centre, continuous_chainStep1'/2'/3'/4', centre*_chain_signs,
exists_open_good_of_centre machinery, exists_PC_inputs_s1.

## Log
- (start) created log.
- rg confirmed all 21 candidate names appear only inside their own cluster + docstrings
  in Certificate.lean; nothing else in Pptc/*.lean. centre7roots/8roots and
  exists_zero_of_sign_change_on still used by live code -> kept.
- Ran anchored Node deletion (unique-anchor asserts): note1 rewritten; S1-cluster
  removed (10337 chars); note2 rewritten; pole-cluster removed (5976 chars). File now
  221726 chars.
- lean_diagnostic_messages (severity=error): EMPTY (no errors). File has zero `sorry`
  (only a docstring mentions the word). Line-length OK on new notes.
- Next: final lake_check Certificate.lean + Main.lean, and axiom_check.

## Final results
- lake_check Pptc/TotallyReal/Certificate.lean: exit 0, ZERO errors (only pre-existing
  style/`<;>`/unused-variable warnings).
- `lake build Pptc.TotallyReal.Certificate`: "Build completed successfully (2943 jobs)"
  -> refreshed stale olean so the downstream check is meaningful.
- lake_check Pptc/TotallyReal/Main.lean: exit 0, ZERO errors.
- axiom_check Main.lean on Pconstructible.root_Pconstructible_totallyReal_seven and _eight:
  [propext, Classical.choice, Quot.sound] — NO sorryAx.
- All 21 named declarations deleted; all KEEP-list declarations intact. No dangling
  references to any deleted name remain (rg clean). Note1 and note2 rewritten as specified;
  the second S1 note ("cannot be imposed on an open set") was deleted with its cluster.
- DONE.
