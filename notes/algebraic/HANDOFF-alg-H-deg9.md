# HANDOFF-alg-H-deg9: rational sextic × rotated rational sextic (PLAN-degree9, row H)

Backend: Wolfram (wolfram MCP).

- 2026-11-13 start, after D1. Read D0 row H and H1 §"graph against rotated graph".
- Formulation: a pair of generators sigma, tau, each in Q[other]_{<=6}.
- Census:
  - all coefficients free: r = 9, reproducing D0;
  - P, R fixed rational with P-affine moves (P0 = u^6-2u^5+3u^3-u+1, R0 = u^6+u^4-3u^3+2u-1):
    r = 6, so c_tau = 3 over F.
- Fibre over tau: 9x8 matrix with column degrees (0..6, 0), rank <= 7, so codim 2 in P^5.
  - Thom-Porteous h_2 = 266; Hilbert-Burch agrees.
  - The P-cubic case has a finite fibre (266) and the P-quadratic case reduces to E's
    sub-condition, so both are dominated.
- Wrote H-deg9.md; updated PLAN-degree9 and PLAN-algebraic.
