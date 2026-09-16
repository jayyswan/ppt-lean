# HANDOFF-hypergeometric-R4a

Task R4a: inbound survey — cubic Bézier arc length as ₂F₁?

- [step 1] Created HANDOFF. Read AGENTS.md, PLAN §1/§2/§4 H6/§5 B1/B6/§6 R4, R1 notes.
- [step 1] Next: read Defs.lean (speed/arcLengthOf/bezierParam/cubic_bezier) and ThirdKind.lean.
- [step 2] Read Defs.lean: speed = sqrt(x'^2+y'^2); cubic_bezier constructor; bezierParam Bernstein.
- [step 2] Read ThirdKind.lean: moment reduction (integral_sqrt_quartic), thirdKindQuartic,
  bezierParam_thirdKind, thirdKindMoment_one, thirdKind_sum_key, ellipticPiInc_Pconstructible_gt_one.
  h=0 = firstKindQuartic (ellipse/F family). Plan: numeric+symbolic Wolfram checks.
- [step 3] Wolfram (MCP) verified to >=15 digits: moment reduction (60d), pullback to
  Legendre t=sin/(cos+h sin) (60d), moment0=EllipticF (59d), thirdKindMoment_one (60d),
  Pi=F+nA (59d), thirdKind_sum_key symmetrised (99d), h=0 int dt/sqrtQ=F (50d),
  graph-cubic m=4 2F1 (59d), K=(pi/2)2F1(1/2,1/2;1;c) (59d), quadratic-graph elementary (49d).
  Closed-loop Bezier Q has only complex roots; generic Bezier Q>0. Verdict: NO new 2F1 source.
- [step 4] Next: write R4a-bezier-checks.wl and NOTES-hypergeometric-R4a-bezier.md.
- [step 5] Wrote archived files/hypergeometric-scripts/R4a-bezier-checks.wl and
  pptc/Pptc/Hypergeometric/NOTES-hypergeometric-R4a-bezier.md. Fixed h=0 4th control point
  to (T − mT³/3, (1+m)T²/2) per bezierParam_firstKind. No .lean touched. DONE.
  Verdict: general cubic Bézier arc length = incomplete F/E/Π (Appell), NOT ₂F₁; the only
  ₂F₁ cases (m=4 cubic graph; h=0/ellipse K) are already landed. No new source.
