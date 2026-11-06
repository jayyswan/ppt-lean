# HANDOFF-offset-A3

Progress log for task A3 (offset × offset, self-crossings, cusps). Append one line per step.

- [01] Read PLAN-offset-00-overview.md, PLAN-offset-A3-offset-offset.md, pptc/Pptc/Defs.lean, pptc/Pptc/Offset.lean in full. Starting.
- [02] Created offset-scripts dir, Scratch dir, NOTES skeleton. Python 3.12 sympy 1.12 ok. Starting offset x offset resultant degree computation.
- [03] Offset x offset two cubics: affine elimination ideal over GF(p) has degree 96 = q1 (deg4 cusp-spurious) * f92 (deg92 genuine, irreducible over Q). f92 has Galois evidence for S_92 (47- and 89-cycles + odd permutations). Verified a real crossing to 45 digits in mpmath: t1=1.22231179911457674266169305600314168498362206, point (11.4021856741..., 6.8334367955...), distances exactly 1, perp residuals 1e-60.
- [04] Self-crossing: saturated Groebner gives degree 36 = q1(4)*f32(32), f32 irreducible over Q but IMPRIMITIVE (all cycle lengths even; t<->s blocks of size 2). Real bitangent center for cf1 d=2 verified to 45 digits: center=(7.87715009600341450889889780106580084769897677, 2.80686039268423686425593528826127510749194291), radius 2 exact, t=0.599337433861129445146424851688373373150798571, s=0.0476717005369934433997256730706413981860966541. Center degree 16 (resultant factor (16)^2*(32)).
- [05] Wrote NOTES-offset-A3.md (full deliverable) and 5 scripts A3-01..A3-05. Cusp verdict: not extractable (evolute rational but not a legal curve; no forced curve through cusp; degree-12 curvature equation unusable). Next: Lean scratch file.
- [06] Created pptc/Pptc/Scratch/OffsetA3.lean: defines the offset x offset rationalised equations offsetOffsetE1/E2; theorem offsetOffsetE1_eq_zero_of_cross stated with sorry (UNPROVED); theorem offsetOffset_cross_root_Pconstructible PROVED by exact application of offsetCubicPair_cross_root_Pconstructible. LSP diagnostics: success, only the sorry warning. Task essentially complete.
