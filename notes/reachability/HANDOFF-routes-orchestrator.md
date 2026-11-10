# HANDOFF-routes-orchestrator

Progress log for `notes/reachability/PLAN-routes.md`. One line per step.

- 2026-11-10: plan written after R7 (d=0 separation fails) and R8 (missing-curve audit).
  Streams: R12 convention (wave 1), R9 singularity spectrum (wave 1), R10 decomposition dictionary
  (waves 1–2), R11 discrete spectra (wave 2), R13 goat legality (wave 2), IDX standing index.
- 2026-11-10: **R12 landed** (`R12-convention.md`). Recommendation **B + C**; awaiting ratification
  (§2.5 of the note). Main findings: (i) the value coordinate is the only free convention slot;
  (ii) A is genuinely stronger for `1/log`/`δlogδ`/complex-monodromy log points (real `φ` resolve
  them), but log points with real monodromy are A-robust (Lemma 1.2); (iii) B1 Route-O necessity
  reduces to a 4-function span condition on `R_C`; the catenary is the `tan` solution, the log-cosine
  is not, the base catalogue is excluded by Wronskians, and the rest of the tower is open.
- Decisions pending from the user: ratify B + C (or choose A), priority (R9 vs R10), scope of R11,
  whether `l=0` and the goat are in scope.
