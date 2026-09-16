# HANDOFF — R4b (offset-curve arc length as ₂F₁?)

Research task (non-Lean). Deliverable: `NOTES-hypergeometric-R4b-offset.md`.
No `.lean` file is created, edited or deleted. No lean-lsp / lake calls.

- [start] Read AGENTS.md, PLAN overview (§1, §2, §4 H6, §5 B1/B6, §6 R4),
  R1 notes (§1.5 offset density), Defs.lean (`speed`, `arcLengthOf`,
  `unitNormal`, `offsetParam`, `offset` constructor), Offset.lean.
- [step 1] wolfram: general symbolic identity proven — `|Γ'|² = (1 − dκ)²w²`,
  κ = (x'y''−y'x'')/w³, `unitNormal` = left (+90°) normal. Residual exactly 0.
- [step 2] Key structural identity: speed(offset) = |1 − dκ|·speed(γ) and
  ∫κ·speed = Δ(tangent angle); so offset arc length = base arc length − d·Δφ.
  Δφ = arctan/atan2 of the (elementary) tangent direction for every base curve.
- [step 3] wolfram numerics, all residuals ~0: ellipse (60 digits), monomial
  n=5 (60), monomial n=3 (60), cubic pair of Offset.lean (49 digits), and the
  elementary ∫dθ/(a²sin²+b²cos²)=(1/ab)arctan((a/b)tanθ) symbolically.
- [step 4] Confirmed the task's curvature guess for y=Cxⁿ is wrong by C^{3−n};
  correct κ = n(n−1)Cx^{n−2}/(1+n²C²x^{2n−2})^{3/2}.
- [step 5] ThirdKind.lean: offset inherits the base cubic's incomplete Π, adds
  only an elementary arctan term; no complete case lowers Π to a ₂F₁. No new source.
- [step 6] Wrote `R4b-offset-checks.wl` and
  `NOTES-hypergeometric-R4b-offset.md`. DONE.
