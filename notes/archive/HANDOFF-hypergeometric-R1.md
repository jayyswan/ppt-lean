# HANDOFF hypergeometric R1 (research note, no Lean edits)

Deliverable: `NOTES-hypergeometric-R1.md` at the repo root — "origin problem for
`power_law`; hyperelliptic route to new `Γ` (B1, B6)".
Research only: no `.lean` file may be edited/created/deleted. Numeric scripts in
`archived files/hypergeometric-scripts/R1-*.py`. Every identity labelled
numerically-checked (digits) vs classical vs speculative.

## Log
- [start] read AGENTS.md, PLAN-hypergeometric-00-overview.md (S2 V4, S4 H6, S5 B1/B6, R1 row),
  `Pptc/Defs.lean` (all six base curves + closure ops), existing wave-0 HANDOFFs. Confirmed
  `py` has mpmath 1.3.0 / scipy 1.12.0.
- [read] `Pptc/Basic.lean` lines 3300-4010: the `ellipticF` construction (`firstKindQuartic`,
  `firstKindCurve`/`firstKindTanParam`, the two integration-by-parts identities). This is the
  template for "make an integral an arc length", and it is genus-1 specific.
- [scripts] wrote and ran `R1-q1-origin-complete-period.py` (Q1): V4 to 45+ digits; piece is
  `G(X)-G(x0)`; integer exponents m=6,8,10 reach x=0 via `poly_graph`; density-sharing graphs
  are power laws; `offset` density is not `sqrt(1+Cx^m)`; second-kind diverges ~ (2/(m+2))U^(m/2+1);
  first-kind `= (1/m)B(1/m,1/2-1/m)` (diff 0).
- [scripts] `R1-q2-b1-gauss-second.py` (Q2): Gauss second to 50 digits for a=1/2,1/3,1/4,1/6 and
  new a=1/5,1/8,3/10,2/5,3/7,3/8,0.37,0.123; V6 at z=1/2 and V7 at z=1/5 diff 0;
  **Bailey z=1/2 formula `2F1(a,1-a;c;1/2)=G(c/2)G((c+1)/2)/(G((c+a)/2)G((c+1-a)/2))`
  verified over 172 (a,c) pairs to 50 digits**; Euler transform verified at interior points.
- [scripts] `R1-q3-hyperelliptic-periods.py` (Q3): complete periods `(1/m)B(p/m,1/2-p/m)` diff 0;
  m=10 Gamma arguments (1/10,1/5,3/10,2/5) are NEW vs the 24-family; cubic Bezier speed^2 is a
  quartic (genus 1); poly_graph degree d gives speed^2 degree 2d-2 (genus up to 4); incomplete G(X)
  is not any Beta period.
- [scripts] `R1-q4-newgamma-cm.py` (bonus): CM/Chowla-Selberg test at tau=i sqrt5 (disc -20).
  Method validates on d=-4 (ratio exactly 1). No small-coefficient algebraic relation between
  K(tau) and Gamma(k/5) or Gamma(k/20) products was found -> Gamma(1/5) not reached this way;
  flagged speculative/open in the note.
- [next] write `NOTES-hypergeometric-R1.md` (repo root) and finalise.
- [done] wrote `NOTES-hypergeometric-R1.md` (repo root), sections 0-5: Q1 negative with exact
  reachable curve for integer b and genus/differential obstruction; Q2 verified correspondence +
  blocked frontier; Q3 new m=10 Gamma(1/10)Gamma(2/5) target, unclosable; strongest candidate §4
  (m=10 period, missing first-kind-differential primitive); label ledger. No `.lean` file touched.
