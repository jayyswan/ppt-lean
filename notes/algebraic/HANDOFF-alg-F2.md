# HANDOFF F2 (families in W_2)

- 2026-11-13 step 1: checked notes for overlap (P1prime §4.2, P2prime, H1, F1 §2): none treat curves in W_2.
- step 2: F2_arith.py, Takeuchi criterion validated on Takeuchi's list; arithmetic iff d in {5,6}.
- step 3: F2_genus_bound.py, Goursat + RH bound; g(Y) >= 2 for non-isomorphism curves at d in {8,9}; fails at d <= 7.
- step 4: F2_d5_hecke.py, (4,4,5) in (2,4,5) and (2,4,10): not a family (4120/13375 mismatches, no twist); lambda1 is the F20 resolvent.
- step 5: F2_lowbideg.py, (2,3),(3,2),(3,3) at l = 101..113: 75 runs, 0 passing; control with constant table passes all.
- step 6: F2.md written; pointers in PLAN-forward-search.md, PLAN-algebraic.md, F1.md.
