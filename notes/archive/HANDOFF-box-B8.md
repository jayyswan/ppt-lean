# HANDOFF — B8 (BoxGraph inverse arc length)

Goal (Lean):
```
theorem graphArcLength_inverse_Pconstructible
    {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (f : ℝ → ℝ) (hmem : ∀ t : ℝ, (t, f t) ∈ S)
    (hdiff : ∀ t : ℝ, DifferentiableAt ℝ f t) (hC1 : Continuous (deriv f))
    {a : ℝ} (ha : PConstructible a) (hfa : PConstructible (f a))
    {L : ℝ} (hL : PConstructible L) (hL0 : 0 ≤ L) :
    ∃ b : ℝ, a ≤ b ∧ arcLengthOf (fun t : ℝ => (t, f t)) a b = L ∧ PConstructible b
```
Target file: `pptc/Pptc/BoxGraph.lean` (new). Part 1: move 3 lemmas from Jacobi.lean to Box.lean.

Plan: log first; read Jacobi §Inversion + Box.lean endpoints; move lemmas; prove speed_graph; apply surjective_of_hasDerivAt_ge d=1; build b via arc_of_length + arc_xendpoint_Pconstructible.

## Log
- [step 0] Created handoff log.
- [step 1] Part 1 done: added imports to Box.lean, moved 3 lemmas into new §Inverting section,
  replaced Jacobi §Inversion with pointer. Box.lean diagnostics CLEAN. Jacobi diagnostics CLEAN.
- [step 2] Created BoxGraph.lean, added import to Pptc.lean. First draft had 5 errors
  (hfcont projection, stronglyMeasurableAtFilter arg order, comp_const_add, rw on beta-reduced
  hF0, monotoneOn_id vs let γ). Fixed. BoxGraph.lean diagnostics CLEAN.
- [step 3] Refactored: private graph_xendpoint_Pconstructible; added supplied-b form
  graphArcLength_endpoint_Pconstructible. Diagnostics CLEAN.
- [step 4] lean_verify both main thms: axioms = propext, Classical.choice, Quot.sound only.
- [step 5] lake_check Pptc/Box.lean OK; Pptc/Jacobi.lean OK; Pptc/BoxGraph.lean OK.
- [step 6] `lake build Pptc.BoxGraph` OK (olean written). DONE.

## Final status
- Part 1: Box.lean imports added: Mathlib.Analysis.Calculus.Deriv.MeanValue,
  Mathlib.Topology.Order.IntermediateValue. Three lemmas at Box.lean:410,416,435 in new
  §Inverting an increasing antiderivative. Jacobi.lean §Inversion replaced by pointer; green.
- Part 2: `speed_graph` BoxGraph.lean:47;
  `graphArcLength_endpoint_Pconstructible` (supplied-b) :103-111;
  `graphArcLength_inverse_Pconstructible` :116-156 — exactly the requested signature.
  Pptc.lean now imports Pptc.BoxGraph. Nothing unproved, no sorry.

## B9 (continuation)
- [b9 step 0] Plan: private `monomialArc_exists n hdeg L hL hL0` applying B8 at a=0 for
  `fun t => t^n`; three witnesses (parabola L=1/2 n=2, cubic L=1 n=3, quartic L=1 n=4),
  each def/spec/Pconstructible. Key lemmas: deriv_pow_field, aeval_X_pow, zero_pow.
- [b9 step 1] Wrote block. Errors: `by decide` does not reduce `natDegree` (switched all to
  `by simp`); `rw [zero_pow hn]` did not see through beta (`simpa [zero_pow hn]`). Fixed.
- [b9 step 2] Diagnostics CLEAN. lean_verify all three _Pconstructible: axioms
  propext, Classical.choice, Quot.sound only. lake_check Pptc/BoxGraph.lean OK.
  lake build Pptc.BoxGraph OK (olean).
- Note: guard's CRLF normalization is NOT firing this session; BoxGraph.lean (and HANDOFF md)
  are LF. Box.lean was already LF (like BoxSine.lean/Level24Alg.lean), so nothing was broken;
  left endings alone per AGENTS "do not hand-roll normalize scripts".

## B9 final
- `monomialArc_exists` (private) BoxGraph.lean ~158-192: B8 at a=0 for `fun t => t^n`.
- `parabolaHalfArcAbscissa_Pconstructible : PConstructible parabolaHalfArcAbscissa` line 207.
- `cubicUnitArcAbscissa_Pconstructible : PConstructible cubicUnitArcAbscissa` line 224.
- `quarticUnitArcAbscissa_Pconstructible : PConstructible quarticUnitArcAbscissa` line 241.
- Each witness = def(2) + spec(5) + Pconstructible(2) = 9 code lines. Nothing unproved.


