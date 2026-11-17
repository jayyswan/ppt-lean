# HANDOFF-alg-D0: degree-9 linear-dial census (PLAN-degree9 §2)

Backend: Wolfram (wolfram MCP, Wolfram Language 15.0.1) for every number. Python not used.

- 2026-11-13 start. Read PLAN-degree9, PLAN-algebraic §1-2, R2 §1-2, N2, W1 §0, WARP §2-5, H1 §4,
  N4 summary, NOTES-general census. Framework: crossing polynomial family Λ (linear dials) over
  nonlinear dials V; c_lin = 10 - F; r = rank of (all dials) -> 9 chosen crossing roots; s = dim of
  solution set in (τ, V); fibre over a fixed generator = s - r.
- Census run (Wolfram, root-Jacobian at 90-150 digits): linear rows A,B,C,L,D1,E,F,K,G,H,I,J,N and
  nonlinear rows M1-M4. Reproduced: odd engine r=6, Bezier x Bezier r=8, y=x^3 x Bezier r=7.
- D1 check: fibre curve for q1 at tau=beta has total degree 20 (not 19), irreducible over Q.
- Row E (Bezier with X=t^2 x Q-sextic): condition is s_{4321}(tau_1..tau_9)=0, degree 10 (line
  restriction 10 + 36; the 36 is the non-generator locus). Jacobi-Trudi: linear in e7; contains
  {p1=p3=p5=0}. Positive control: explicit totally real S9 nonic solved, chi | Y(t)-g(t^2).
- CAUTION: q1 = prod(x-i)+1 and any prod(x-a_i)+c are degenerate test fields for E (condition
  sees only e1..e7). q1 is an odd-engine field. Test field q3 (perturbed) used instead.
- Box search on q3, tau in {-1,0,1}^8 (3280 classes), shift exact over Q: no hit; control found.
- Wrote D0.md; updated PLAN-degree9 status/order and PLAN-algebraic (Phase D9 pointer).
