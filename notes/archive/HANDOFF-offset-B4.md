# HANDOFF-offset-B4

Progress log for PLAN-offset-B4 (legality of offset extractions + Lean infrastructure).
Append one line per step.

- Step 0: read PLAN-offset-00-overview.md and PLAN-offset-B4-legality-formalization.md.
- Step 1: read all of Defs.lean, Offset.lean, Basic.lean l.230-419 (crossing + isolation helpers), archived files/NOTES-jacobi-X4.md. Created dirs + scratch dir.
- Step 2: created pptc/Pptc/Scratch/OffsetB4.lean. PROVED: rationalize, rationalize_mul, rationalize_add_mul, crossing_PConstructible_of_isolated, rational_param_recovery, chain_recovery, speed_parabola, parabola_offset helpers, offsetParam_parabola. STATED (sorry): normalEq_rat_eq_zero, proper_rational_recovery_degree, finite_zeros_of_analyticOnNhd, analytic_arcs_finite_meet, H1 offsetConic, H3 degreeTenFamily. File `success: true` under lean-lsp (only sorry/linter warnings).
- Step 3: verified axioms of crossing_PConstructible_of_isolated and rationalize (propext, Classical.choice, Quot.sound only). Wolfram + scripts/B4-01-parabola-offset-degree.py confirm parabola-offset implicit degree 6 (6 in X, 4 in Y). Wrote NOTES-offset-B4.md (legality table, crossing lemmas, recovery, rationalization, parabola, H1-H3, DAG, effort, side discoveries, leads, missed modelling issue = offset needs C^2 to iterate).
