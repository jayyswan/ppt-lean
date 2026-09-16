# HANDOFF — R2 (explicit cubic/sextic signature reductions, H5)

Research only. No `.lean` edits. Deliverable: `NOTES-hypergeometric-R2.md`.
Scripts: `archived files/hypergeometric-scripts/R2-*.py` (mpmath, run with `py`).

- [step 1] Read AGENTS.md, PLAN overview (§2 V7, §4 H5, §5 B1, wave table R2), L1 contract
  (`Hypergeometric/Basic.lean`), `Nonic/Nonic.lean`. Confirmed: algebraic degree ≤ 9 ⇒
  PConstructible. Environment: mpmath 1.3.0 via `py` works.
- [step 2] Read R1 note (do not duplicate B1/B6). Read Nonic outline: `root_Pconstructible_of_rat_nonic_nonreal`
  handles roots of degree-<=9 rational polys. Re-ran `R2-01-quartic-v7.py`: V7 holds to 59.3 digits
  (worst 4.7e-60) at z=1/5,1/3,3/4,1/2,...
- [step 3] Identified sources: RBBG Theorem 5.6 (Berndt-Bhargava-Garvan 1995) for the cubic
  reduction; Robinson arXiv:2009.07069 Thm 8 (after Shen, Ramanujan J. 30 (2013)) for the sextic.
  Verified both parametrically at 50 dps (cubic err ~1e-50, sextic 0/1e-50).
- [step 4] Wolfram elimination: cubic relation R(k^2,z)=0 is palindromic bidegree (6,4);
  invariant k^2+1/k^2 satisfies an irreducible cubic. Prefactors: cubic gamma^4 deg 3,
  gamma^2 deg 6, gamma deg 12; sextic prefactor deg 12. Writing scripts R2-02/03/04.
- [step 5] Wrote/ran R2-02-cubic-rbbg.py (worst err 7.2e-80), R2-03-sextic.py (worst 4.2e-80),
  R2-04-degrees.py (sympy resultants/factorisations). Found exact special values:
  2F1(1/3,2/3;1;1/2) = (3^(3/4)/2) 2F1(1/2,1/2;1;(2-sqrt3)/4) and
  2F1(1/6,5/6;1;1/2) = (3/4)^(1/4) 2F1(1/2,1/2;1;1/2), both exact at 80 dps.
- [step 6] Wrote deliverable NOTES-hypergeometric-R2.md. Key caveat: argument maps have
  degree 6 (Nonic-OK) and invariants cubic, but generic prefactors have degree 12 (> Nonic's 9);
  at z=1/2 (B1 value) all degrees drop to <=4. Handoff complete.
