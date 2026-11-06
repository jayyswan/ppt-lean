# HANDOFF nonic-lean-C

Target: `pptc/Pptc/NonicPowerLaw.lean`
Goal: `resolvent_powerLaw9` and `resolvent_y_Pconstructible9`.

Plan: mirror DegreeSeven map lemmas for companion9; pass charpoly root from Q to R;
define p = X^9 - RQ; show degree <=6 via hkill; transfer evaluation.

- [start] created log
- probed lemma names: Matrix.charpoly_map, Polynomial.eval_map, map_aeval_eq_aeval_map confirmed
- wrote first draft of Pptc/NonicPowerLaw.lean
- fixed final eval step: `map_pow` in a rw chain caused kernel deep recursion; replaced with
  `Polynomial.aeval_def` + `eval₂_sub`/`eval₂_pow`/`eval₂_X`/`eval₂_eq_eval_map`, then hroot2
- fixed condition simp to `simp [h, Matrix.algebraMap_matrix_apply]` (RingHom.mapMatrix_apply unused)
- DONE: lake_check Pptc/NonicPowerLaw.lean -> OK no errors/warnings; lake build target OK
- axioms of both declarations: [propext, Classical.choice, Quot.sound]; no sorry

