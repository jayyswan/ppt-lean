# HANDOFF-hypergeometric-R4c

Task R4c — inbound survey: `sine` / `exp_two` / `rectangle` arcs as ₂F₁?

Research task. No `.lean` file edited, created or deleted. No lake / lean-lsp used.

Deliverable: `pptc/Pptc/Hypergeometric/NOTES-hypergeometric-R4c-sine-exp.md`
Scripts: `archived files/hypergeometric-scripts/R4c-*.wl`

Progress log (append one line per step):

- [step 1] Read AGENTS.md, PLAN-hypergeometric-00-overview.md (§1, §2, §4 H6, §5 B1/B6, §6 R4), NOTES-hypergeometric-R1.md, Defs.lean (speed, arcLengthOf, sine, exp_two, rectangle, restrict, scale_x/y, translate_x/y). Created this HANDOFF.
- [step 2] Confirmed endpoint lemmas in Basic.lean: `sin_Pconstructible` (2650), `cos_Pconstructible` (2645), `rpow_two_Pconstructible` (1744). Confirmed class signatures `hyp_elliptic_class_Pconstructible` (EllipticClass.lean:521, params `(1/2+i,1/2+j,1+k)`) and `hyp_graphFamily_class_Pconstructible` (GraphsClass.lean:765, `b=1/(2n-2)+j`, n∈{3..6}).
- [step 3] Wolfram checks (backend: Wolfram Language): sine incomplete arc = `Sqrt[2](E(b|1/2)-E(a|1/2))` vs quadrature diff 0 at 40 digits; Appell F1 form of incomplete E diff 0; complete `Sqrt[2]E(1/2)=(pi/Sqrt[2])2F1(-1/2,1/2;1;1/2)` diff 0; affine sine closed form vs quadrature diff 0; `E(k2)=(pi/2)2F1(-1/2,1/2;1;k2)`; exp_two antiderivative `Sqrt[1+u^2]-ArcSinh[1/u]` FullSimplify residual = 0, closed form vs quadrature diff 0. Script written: `archived files/hypergeometric-scripts/R4c-01-sine-exp-rect.wl`.
- [step 4] Wrote `NOTES-hypergeometric-R4c-sine-exp.md`. Verdict: no new ₂F₁ source.
