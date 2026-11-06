# HANDOFF — Box B10: compactness of restricted curves

Target file: `pptc/Pptc/Box.lean`
Goal:
```lean
theorem isCompact_restrict_of_isClosed {S : Set (ℝ × ℝ)} (hS : IsClosed S)
    (xmin xmax ymin ymax : ℝ) :
    IsCompact (S ∩ {p : ℝ × ℝ | xmin ≤ p.1 ∧ p.1 ≤ xmax ∧ ymin ≤ p.2 ∧ p.2 ≤ ymax})
```
Plus `IsClosed` instances: poly_graph, ellipse, rectangle, exp_two, sine, cubic_bezier.
Docstring on power_law exclusion. Optional corollary for poly_graph restrict.

## Log
- [start] Created log. About to read Defs.lean restrict / base curve defs and Box.lean outline.
- [recon] restrict def at Defs.lean:346-351 (window exactly as task). bezierParam def at Defs.lean:86.
  Box W2 section ends line 202; W3 starts line 204 — will insert new section between.
- [lemmas] Confirmed: IsCompact.inter_left (ht : IsCompact t) (hs : IsClosed s) : IsCompact (s ∩ t);
  IsCompact.inter_right (hs) (ht) : IsCompact (s ∩ t); IsCompact.prod; isClosed_Icc; isClosed_singleton;
  IsClosed.prod; isClosed_eq; IsCompact.isClosed; Polynomial.continuous_aeval (p) :
  Continuous fun x => (Polynomial.aeval x) p; Real.continuous_const_rpow (h : a ≠ 0) :
  Continuous fun x => a ^ x. No `continuous_bezierParam` lemma exists; will prove inline.
- [write] Added section W2b to Box.lean between nonempty_traced_arc and W3: general lemma +
  6 IsClosed instances + poly_graph corollary. Added imports Mathlib.Topology.Algebra.Polynomial,
  Mathlib.Analysis.SpecialFunctions.Pow.Continuity.
- [diag] First diagnostic pass: no errors. Only 2 deprecation warnings for Set.mem_setOf_eq at
  lines 239/275; replaced with Set.mem_ofPred_eq.
- [diag] Second pass: clean, zero diagnostics.
- [verify] lean_verify isCompact_restrict_of_isClosed / isClosed_cubic_bezier / isClosed_rectangle:
  axioms = propext, Classical.choice, Quot.sound only.
- [lines] 233 isCompact_restrict_of_isClosed; 246 isClosed_poly_graph; 252 isClosed_ellipse;
  259 isClosed_rectangle; 285 isClosed_exp_two; 291 isClosed_sine; 297 isClosed_cubic_bezier;
  306 isCompact_restrict_poly_graph.
- [mem] Killed stale lean/lake workers (exact form); free 283MB -> 3396MB. Running lake_check.
- [done] lake_check Pptc/Box.lean: "OK - no errors or warnings."
- [done] lean_verify on all 8 new theorems: axioms = propext, Classical.choice, Quot.sound only.
  No sorry, nothing unproved. No other files edited. No @[pconstructible_cond] tags added.
