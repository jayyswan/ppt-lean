# HANDOFF-alg-D1: cubic Bézier × rational sextic (PLAN-degree9 D1)

Backend: Wolfram (wolfram MCP). Python not used.

- 2026-11-13 start, after D1E.
- Over F with g fixed rational (g = x^6-3x^5+2x^4+5x^3-x^2-4x+1), X, Y, c in F: root-Jacobian rank
  r = 8 (seeds 1, 2), so c_tau = 1.
- Over Q, on q3 along tau = beta + s beta^2, exact dets at 67 points, interpolated: degree 66 =
  36 (sum resolvent, divides exactly) + 30, and the 30 is irreducible. Same for X = t^3 and
  X = t^3 + t.
- Weighted count: P(1^9, 2), degree 30, K = O(19), so dominated by E.
- Real capacity 18, attained by T6(T3) = T18.
- Hypersurface degree over F not measured (needs homotopy continuation; too big for the MCP).
- Wrote D1.md; updated PLAN-degree9 and PLAN-algebraic.
