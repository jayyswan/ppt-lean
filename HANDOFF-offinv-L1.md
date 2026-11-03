# HANDOFF offinv L1 — Speed.lean (curvature, deriv_offsetParam, speed_offsetParam, arcLengthOf_offsetParam)

- def `curvature` + `hasDerivAt_speed` (s' = (x'x''+y'y'')/s) compile clean.
- `offset_coord_deriv_algebra`, `deriv_offsetParam`, `speed_offsetParam` compile clean (no warnings).
- next: `arcLengthOf_offsetParam` (FTC + interval-integral linearity).
- ALL FOUR PROVED, no sorry: curvature, hasDerivAt_speed, offset_coord_deriv_algebra,
  deriv_offsetParam, speed_offsetParam, arcLengthOf_offsetParam.
- `lake build Pptc.OffsetInversion.Speed` -> Build completed successfully (2787 jobs).
- lean_verify on the 4 headline decls: axioms only propext/Classical.choice/Quot.sound
  (no sorryAx, no warnings).
- added `import Pptc.OffsetInversion.Speed` to Pptc.lean (single edit, at end).
- DONE.

