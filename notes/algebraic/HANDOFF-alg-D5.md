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
- Second pass (user: finish D5):
  - intended a Castelnuovo + adjunction kill of pencils (p_a <= (d-1)(d-2)/2 against 1 + 13d/2);
  - jump locus on pairing components: a curve J' plus 2-dim special loci; the latter explain B3's
    -8460;
  - branch probe with +/- controls: S passes through generic J' points (ratio constant ~1), not
    through the 2-dim loci;
  - so K_S = 13H - 3R (R = sum J'_pi), and the kill fails: a pencil would need
    R.D >= d(16-d)/3, which upper bounds do not exclude;
  - deg J'_pi >= 52.
- D5 still open; needs NS(S) or the components of R (Macaulay2/Singular, not installed).
