# HANDOFF-septic-normform

Progress log for `PLAN-septic-normform.md`. One line per step; newest at the bottom.

- [setup] Read B1/B2/A2/Offset.lean/septic paper; confirmed test target f = x⁷−14x⁵+49x³−36x+1 (S₇).
- [Phase 1] Verified norm-form reformulation symbolically (`01-normform-verify.py`): W = u²u'² − (Δ−u²)v'²;
  W is a norm; covering ⇔ (Δ−u²)v'² = u²u'² in A; invertible case v'² = u²u'²/(Δ−u²); non-invertible
  case forces u(τ)u'(τ)=0. All [symbolic].
- [bugfix] Caught a convention error (used v'' instead of v'): corrected system uses the quadratic v'
  itself in both S = u'²+v'² and the last term. Cross-checked against `offsetCrossPoly_normalForm` [Lean]
  and Wolfram.
- [Phase 0] Real solutions of the corrected square system for f: 37 found (25 distinct Δ, all Δ>0);
  Jacobian full rank (min sing. val. 8.35) ⇒ isolated. [numeric]
- [Phase 0] PSLQ under the strict rule (d+1)log₁₀H ≤ digits/2: **no coordinate of any solution has
  degree ≤ 6** at 800–1000 digits; Δ has **no relation of degree ≤ 8** at 1400 digits with coeffs up
  to 10¹⁰⁰ (d≤6). Refutes B1's "deg Δ ∈ {3,5,6}" as PSLQ artefacts. [numeric]
- [Phase 0] Second septic t⁷−7t⁵+14t³−7t+1 (= the ε=1 Chebyshev case B1 used): 122 real solutions,
  70 distinct Δ; first ones have no degree-≤6 relation at 1000 digits / maxcoeff 10⁷⁰. [numeric]
- [Phase 0 verdict] Decic route killed for uniform degree-≤6 coverage. [numeric, strict rule]
- [Phase 2] Stated the A[√S] reformulation and the codim-2 conic condition; remaining construction route
  recorded as a Lead (open).
- [deliverable] Wrote NOTES-septic-normform.md.
