# HANDOFF-offinv-R8 — missing-curve route audit

Progress log for stream R8 (issue 18, follow-up to R7). Deliverable:
`notes/offset-inversion/R8-missing-curve-audit.md`. Research only: no `.lean` edits, no `lake`.

- Re-read R5 §1/§3, R2 Q3.3–Q3.5, R3 §2.3/§3.9/§4, R4 §2, SUMMARY §4–5.
- Fixed the three questions per row: Q1 offset sufficiency, Q2 offset necessity (rigidity), Q3
  intersection status (log-monodromy count).
- Established the strength caveats: Q2 needs fixed curve + fixed `d` + continuous `x`; Q3 needs
  affine data + continuous family + log-type singularities. Discrete spectra and non-affine data are
  not covered.
- Found the `1/log` singularity of `λ = sinh u/(gd u + kπ)` for `tan x = λx`: not a log branch point,
  so R3's count is silent. Flagged a `1/log` invariant as the next concrete question.
- Classified all rows; strong exclusions are involute, rhumb (fixed `k`), tractrix, Biot, and
  elastica (non-elementarity). Beams are mixed (continuous interpolation excluded, discrete spectrum
  open). The `l = 0` well is open (`δ log δ`, not a log branch point). Goat is a single-target
  legality question; separatrix is pointwise R.
- Updated R5's status legend, SUMMARY §5, and added an R8 postscript to the plan.
