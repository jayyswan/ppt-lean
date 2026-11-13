# HANDOFF-alg-D1E: row E (PLAN-degree9, D1 sub-stream)

Backend: Wolfram (wolfram MCP) for every number. Python not used. The MCP gateway times out
near 60 s, so long runs were chunked (8 chunks per field at height 2).

- 2026-11-13 start. Read PLAN-degree9, D0 (row E, §3-§5), SUMMARY §3, §9.
- Hankel: D0's 4x4 determinant = c1 c3 - c2^2 for A/B = sum c_k u^-k (chi = A(t^2) + t B(t^2)),
  exact symbolic in e1..e7.
- A/B = -t tanh(S), S = sum_{k odd} p_k/(k t^k). Hence 4725 s_{4321} = H(p1,p3,p5,p7), checked as
  an exact polynomial identity with p2, p4, p6 free. Centred: 25 p3 p7 = 21 p5^2.
- Normal form: chi in the E locus iff chi = sigma(t) E(t^2) + r(t) (sigma, E monic cubics, r linear).
  Proof written in D1E §2. Dominance: Jacobian rank 8. s_lambda is irreducible. D0's control
  decomposes this way.
- New integer control q_c = prod_{a in A}(x-a) + x + 1, A = {-10,-9,-8,-7,1,6,8,9,10}.
  - Totally real; S9 by Frobenius types (9), (4,5), (1,8).
  - N = q_c * (-(t-7)(t+1)(t+6)), with integral Y and g.
- Search: LLL-reduced trace-zero lattice of Z[beta], c in {-2..2}^8 (195312 directions), shift h
  free over Q.
  - Filter: root of f_tau(h) mod 14 primes 13..73, then FactorList.
  - Control: only the planted tau = 9beta (and 2x). q3: null.
- Correction to D0 §3.4: with g fixed rational, tau in K⊗F and Y in F[t] are valid. This gives
  c_tau >= 3 over F, dominated by M1/G/J.
- Local solubility of X_{q3}:
  - smooth F_p points for every odd p <= 97 and for p = 271;
  - p = 2 via Hensel on F/2 (v = 13 > 2*6).
  - No local obstruction found.
- Wrote D1E.md. Updated PLAN-degree9 and PLAN-algebraic Phase D9.
