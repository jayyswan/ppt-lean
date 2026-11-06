# HANDOFF: HilbertSymbol/Existence.lean

Goal file: `Pptc/HasseMinkowski/HilbertSymbol/Existence.lean`
Namespace: `Pptc.HasseMinkowski`

Target (roughly):
```lean
theorem exists_rat_with_two_prescribed_hilbertSym ...
```

Plan: inspect local Defs/Padic/Real, fetch WiN7 reference, port bottom-up.

## Log
- [start] Created log. Beginning environment inspection.
- Inspected local Defs/Padic/Real/RatApproximation/RatSquares/Padics.Squares. Local `hilbertSym`
  is not namespaced; only case00 p-adic formula proved locally (`hilbertSym_padicInt_units`,
  `hilbertSym_padic_odd_case00`). Upstream `padic_odd_eq`/`two_adic_eq`/`almost_all_one`/`prod_eq_one`
  are all `sorry`. Main existence is `sorry` upstream too.
- Fetched WiN7 ExistenceTheorem/Basic/ApproximationTheorem/Legendre/Lemmas/Parity into Scratch.
- Decision: port the sorry-free combinatorial core (S/T/A/M/q/x + squareness + valuations), which
  needs only local Padics.Squares lemmas and Dirichlet; document the gap for the hard direction
  (needs case10/two-adic formula + global product identity).
