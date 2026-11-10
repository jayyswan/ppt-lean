# HANDOFF-offinv-R6 — chains of two offset inversions

Progress log for stream R6 (issue 18, open item 3). Deliverable: `notes/offset-inversion/R6-chains.md`.
Research only: no `.lean` edits, no `lake`.

- Read SUMMARY §7, PLAN §2 (R4), R2 Q1/Q2/Q4, R4 §1–2, R3 §3.9/§4, R0 §3.4, Defs base curves.
- Scoped the item: define a 2-chain inside the `Defs` constructor vocabulary; separate *shared-tracing*
  chains from *re-based* chains.
- Wolfram cell 1: derivative `F_d' = (s³−d)/s²`; shared-tracing residuals (1e-59); offset-the-arc residual
  (1e-59); offset-image identity; R4 chain root reproduced (`w₂ = 1.143599…`).
- Wolfram cell 2 (discarded numbers): Groebner coupling curve; low-precision PSLQ. Found the trap:
  25-digit values give spurious relations at bound 1e12.
- Wolfram cell 3: high-precision scan 0/48 with positive control; chain-root rational tests "none";
  exact relations over `Q(w₁,s₁)` verified to 1e-248; correct coupling-curve polynomial.
- Wolfram cell 4: full-precision algebraicity "none"; chain table; `InputForm` of (4.1); non-affine data
  dependence; legality threshold `x₁* = 1.309878…`.
- Wolfram cell 5: `dX/dx₁ = 1/s`, `dY/dx₁ = w/s`, speed 1; identity failure; root displacement
  `w₂ − w₁ = 0.227538…`.
- Wrote `R6-chains.md`: §2 collapse, §3 triangular reduction (Cor. 3.2, Cor. 3.3), §4 coupling curves,
  §5 separation consequences and the exact status of item 3.
- Updated `SUMMARY.md` §2 and §7, and added an R6 postscript to `PLAN-offset-inversion.md`.
