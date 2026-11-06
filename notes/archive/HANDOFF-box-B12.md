# HANDOFF — B12: BoxOffset.lean (offset arc reachability half of N6)

Target file: `pptc/Pptc/BoxOffset.lean` (new). Namespace `Pconstructible`.
Goal (1): `continuousOn_offsetParam` — continuity of the offset tracing on a regular window.
Goal (2): `offsetArc_{xmax,xmin,ymax,ymin}_Pconstructible` thin wrappers around `box_*`.
Goal (3): concrete instance at cubic pair `(0,0,6,-3,0,6,-12,6)`, `d=1`, window `[1/2,1]`.

## Log

- Read NOTES-offset-cusps-lean.md and Offset.lean in full. `exists_rat_window_cubicPair`,
  `offsetCubicPairArc_PConstructibleCurve` located. `offsetParam`, `unitNormal`, `speed`
  need checking in Defs.lean.
- Plan for (1): derive `ContinuousOn γ` from differentiability hypotheses (or take
  differentiability of the two coordinates as hypotheses), then
  `unitNormal = (-y'/speed, x'/speed)`, speed continuous nonzero; `offsetParam = γ + d•N`.
- DONE (1): `continuousOn_offsetParam` landed. Honest bundle = `hdiff` + `hreg` + `hC1`
  (continuity of `γ` genuinely needs `hdiff`; `hC1` alone does not give it). Signature at
  ~line 76 of `Pptc/BoxOffset.lean`.
- DONE (2): four wrappers `offsetArc_box_{xmax,xmin,ymax,ymin}_Pconstructible`, all
  `@[pconstructible_cond]`, thin over `Box`. Diagnostics clean.
- Now (3): cubic pair `(0,0,6,-3,0,6,-12,6)`, d=1, window `[1/2,1]`. `x'=3t(4-3t)>0` on
  the window ⇒ regular + injective; `cubicDer` continuous. `numTac`/`pconstructible`
  literal handling to verify.
- DONE (3): `offsetCuspAbscissa` (`noncomputable def`, ~line 190) and
  `offsetCuspAbscissa_Pconstructible` (~line 199) both landed; diagnostics clean, no sorry.
  Proof: `hder` (3t(4-3t) ≠ 0 on [1/2,1]), `hreg` via `speed_cubicPairParam_ne_zero`,
  `hC1` via `cubicDer` continuous, `hdiff` via `hasDerivAt_cubicVal`, `hmono` via
  `strictMonoOn_of_deriv_pos`, then `offsetCubicPairArc_PConstructibleCurve` +
  `offsetArc_box_xmax_Pconstructible`. No root isolation.
- Added `import Pptc.BoxOffset` to `Pptc.lean`. Next: `lake_check Pptc/BoxOffset.lean`.
- Also added optional `offsetArc_box_xmax_of_offsetHyp` (line 143): consumes the `offset`
  constructor hypotheses directly, builds `PConstructibleCurve.offset` and
  `continuousOn_offsetParam`, then the xmax wrapper.
- FINAL `lake_check Pptc/BoxOffset.lean` → "OK - no errors or warnings". No sorry. No
  scratch files. Deliverable complete (1)(2)(3).
- Final declaration map (Pptc/BoxOffset.lean, 239 lines):
  * `continuousOn_offsetParam`            line 69  (bundle: hdiff + hreg + hC1)
  * `offsetArc_box_xmax_Pconstructible`   line 96  (@[pconstructible_cond])
  * `offsetArc_box_xmin_Pconstructible`   line 106 (@[pconstructible_cond])
  * `offsetArc_box_ymax_Pconstructible`   line 115 (@[pconstructible_cond])
  * `offsetArc_box_ymin_Pconstructible`   line 125 (@[pconstructible_cond])
  * `offsetArc_box_xmax_of_offsetHyp`     line 143
  * `noncomputable def offsetCuspAbscissa` line 170
  * `offsetCuspAbscissa_Pconstructible`   line 179
- `lean_verify offsetCuspAbscissa_Pconstructible`: axioms = propext, Classical.choice,
  Quot.sound only (the PConstructible constructors are inductive constructors, not axioms).
- (3) blocker note: none — the instance landed. The identification with the degree-12
  cusp abscissa is out of scope and explicitly not claimed (docstring says so).


