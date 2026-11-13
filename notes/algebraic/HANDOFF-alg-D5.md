# HANDOFF-alg-D5: B3's leftovers on the line surface (PLAN-degree9 D5)

Backend: Python (numpy, mpmath), user-approved because the Wolfram MCP times out at 60 s.

- 2026-11-13 start, after D4. Read B3.
- sigma11 count (good lines of X cap H) by Newton from random complex starts, seeds 1-5:
  - 1466 distinct, 952 real, still growing;
  - all refined at 45 digits to residual < 1e-38, so nonsingular and isolated;
  - hence deg S >= 1466.
- Serrano: C^2 = m^2 deg S > 81, so any F-rational g^1_k (k <= 8) on a smooth curve in |mH|
  extends to a pencil on S with D.H <= 8.
- Classes: Gamma_7 in |42H|, Gamma_{2,4} in |8H|.
- q(S): the cylinder source H^3(X) = 0, so q = 0 is expected (heuristic).
- Open: does S have a pencil with fibres of Pluecker degree <= 8? Wrote D5.md; scripts in
  scripts/D5_*.py.
