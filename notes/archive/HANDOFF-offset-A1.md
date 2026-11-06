# HANDOFF-offset-A1 (append-only progress log)

- [start] Read PLAN-offset-00-overview.md and PLAN-offset-A1-atlas.md in full; read all of pptc/Pptc/Offset.lean (829 lines).
- [setup] Creating HANDOFF, NOTES, scripts dir; will compute offset algebra with sympy + Wolfram MCP.
- [key] Offset of a degree-n poly_graph crossed with the x-axis: crossing polynomial p(t)^2(1+p'^2)-d^2 has degree 4n-2 and the crossing coordinate X=t+p p' has the SAME degree (irreducible), because inter_x reads coordinates directly. Verified [sympy + Wolfram] n=4 -> 14, n=5 -> 18, n=6 -> 22. This is far beyond the advertised degree 10.
- [key] For n=4, p=t^4+t+1, d=-1: both real crossings genuine (p*w=1), recovery polynomial Q(z)=X-z-p(z)p'(z) is degree 7 with non-real roots -> septic engine applies; X0~-1.594883196255767380274759074200 (30 digits).
- [gaps] Wrote scripts A1-09/10/11: hyperbola offset implicit degree 8 (fixed D=1-t^2); power-law recovery degs (5,5,5,5,4,6); graph recovery 3,5,7,9,11; cusp poly deg = 6(n-1) for polynomial degree n (parabola 6, cubic 12, deg4 18, deg5 24, deg6 30); n=5 (deg18) and n=6 (deg22) 40-digit genuine crossings + Chebotarev (n=6 has a 22-cycle and 19/17-cycles).
- [DONE] Wrote full deliverable C:\dev\Powerpoint\lean\NOTES-offset-A1.md: summary, master table, degree-4n-2 headline with degree-14/18/22 instances, degree-7 septic recovery, genuinely-new checklist, per-curve derivations, cusps, ranked list, Side discoveries, Leads.
- [todo] optionally add pptc/Pptc/Scratch/OffsetA1.lean headline statement; verify conic/power ranks.
- [ranks] A1-12 exact ranks: x^(-1) monic rank 4 codim 4; x^(-2) monic rank 4 codim 8; ellipse monic rank 6 codim 2 (inflated degree 16; genuine degree 8). NOTES updated.
- [lean] Created pptc/Pptc/Scratch/OffsetA1.lean: `offsetPolyGraphArc_PConstructibleCurve` (general poly-graph offset arc legality). lean_diagnostic_messages: only warning "declaration uses sorry" -> UNPROVED, reported as such.
- [status] COMPLETED (deliverable NOTES-offset-A1.md final; no sorry in library; scratch file sorry reported).
