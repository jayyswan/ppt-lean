# HANDOFF jacobi L3 (local-to-global)

Goal: extend Pptc/JacobiAddition.lean with
- `jacobiAm_Pconstructible_nsmul {c u : R} (hcP : PConstructible c) (hc : c < 1) (hu : PConstructible (jacobiAm c u)) (n : N) : PConstructible (jacobiAm c (n * u))`
- `jacobiAm_Pconstructible_of_near_zero {c ε : R} (hcP : PConstructible c) (hc : c < 1) (hε : 0 < ε) (hloc : forall u, PConstructible u -> |u| < ε -> PConstructible (jacobiAm c u)) {u : R} (huP : PConstructible u) : PConstructible (jacobiAm c u)`

Plan: nsmul by induction using jacobiAm_zero + jacobiAm_Pconstructible_add; near_zero by picking n with |u|/eps < n, using u/n.

## Log
- read PLAN overview + L3 brief; created log.
- verified lemma names (div_lt_iff₀, div_mul_cancel₀, exists_nat_gt, abs_div, abs_of_pos).
- wrote both theorems + module doc update into Pptc/JacobiAddition.lean; running lake_check.
- lake_check Pptc/JacobiAddition.lean: OK no errors/warnings.
- added one sentence to Jacobi.lean outlook block; lake_check Pptc/Jacobi.lean: OK.
- axiom check via `lake env lean`: depends on [propext, Classical.choice, Quot.sound]; temp line removed.
- final lake_check Pptc/JacobiAddition.lean: OK no errors/warnings. Committed 8609d6d (not pushed).
- no auxiliary lemmas added; both theorems proved directly. Module doc updated; one sentence added to Jacobi.lean outlook.
