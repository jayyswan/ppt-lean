# HANDOFF-jacobi-L1

Task: phase 1 of Jacobi addition theorem. Create `pptc/Pptc/JacobiAddition.lean` with four
theorems (all `{c : ℝ} (hc : c < 1) (u : ℝ)`):
- `hasDerivAt_jacobiAm : HasDerivAt (jacobiAm c) (jacobiDn c u) u`
- `hasDerivAt_jacobiSn : HasDerivAt (jacobiSn c) (jacobiCn c u * jacobiDn c u) u`
- `hasDerivAt_jacobiCn : HasDerivAt (jacobiCn c) (-(jacobiSn c u * jacobiDn c u)) u`
- `hasDerivAt_jacobiDn : HasDerivAt (jacobiDn c) (-(c * jacobiSn c u * jacobiCn c u)) u`

Plan: inverse function theorem for `am`; chain rule for sn/cn/dn. Verify via LSP.

- Created log; read both PLAN files.
- Wrote JacobiAddition.lean; all four theorems typecheck via LSP (zero errors/warnings). continuous_jacobiAm auxiliary proved via orderIsoOfSurjective + OrderIso.continuous. Imports added: Deriv.Inverse, Topology.Order.MonotoneContinuity.
- lake_check Pptc/JacobiAddition.lean => OK - no errors or warnings. #print axioms Pconstructible.hasDerivAt_jacobiDn => [propext, Classical.choice, Quot.sound]; line removed.
- Committed 64ac44b in pptc/ (message notes LSP verification); no sorry/admit/#print remain. Aux: continuous_jacobiAm. Imports: Mathlib.Analysis.Calculus.Deriv.Inverse, Mathlib.Topology.Order.MonotoneContinuity. DONE.
