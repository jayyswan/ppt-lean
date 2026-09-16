# HANDOFF: L9 — quartic signature V7 (H5)

Target file: `pptc/Pptc/Hypergeometric/Signatures.lean` (to create)

## Goal
```lean
theorem hyp_quarter_three_quarter {z : ℝ} (hz0 : 0 ≤ z) (hz : z < 1) :
    hyp (1 / 4) (3 / 4) 1 z
      = (1 + Real.sqrt z) ^ (-(1 / 2 : ℝ))
        * hyp (1 / 2) (1 / 2) 1 (2 * Real.sqrt z / (1 + Real.sqrt z))

@[pconstructible_cond] theorem hyp_quarter_three_quarter_Pconstructible {z : ℝ}
    (hz : PConstructible z) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    PConstructible (hyp (1 / 4) (3 / 4) 1 z)
```

## Plan
1. Read API files (Basic, Elliptic, Quadratic + handoff, notes).
2. Try formal PowerSeries route (like L6a) or convolution coefficient identity.
3. Land corollary with `hyp_half_half_one_Pconstructible`.

## Log
- [init] created log; about to read API files.
- [L9-run2] read Basic/Elliptic/Quadratic/plan/R2. Elliptic exposes
  `hyp_half_half_one_Pconstructible (hcP : PConstructible c) (hc : |c| < 1) :
   PConstructible (hyp (1/2) (1/2) 1 c)`. L6a's file has the *other* quartic
  `hyp (1/4)(1/4) 1 (4z(1-z)) = hyp (1/2)(1/2) 1 z` (different function).
  Next: numeric check of V7 with mpmath.
- [numeric] V7 confirmed 59 digits (mpmath hyp2f1): z=0.01,0.2,0.5,0.9,0.999 all diff <=6e-59.
- [L9-run3] read AGENTS, PLAN (H5 §4/V7 §2), Basic, Elliptic, R2, handoff. Plan: land
  conditional reduction (identity as explicit hypothesis); attempt V7.
- [numeric3] re-verified V7 to 60 dps (diff 0 / <7e-61 at z=0.1..0.9). Checked the
  "Erdélyi" form `G(z)=(1-z/4)^{-1/2}F((z/(2-z))²)` — WRONG (diff ~0.05), so V7 is a
  genuine Goursat transform, not V6+Pfaff. Inverse form `F((w/(2-w))²)=√((2-w)/2)G(w)`
  is correct (diff 0). Consequence: V7 is NOT derivable from Quadratic.lean's V6.
- [route] Inspected Quadratic.lean (V6 fully landed ONLY as a formal PowerSeries identity
  `hypSeriesQuad_eq_hypSeries_half`; the analytic transfer was L6a's blocker). No general
  `hypSeries a b c` ODE exists; only the hand-written (1/4,1/4;1) one. V7 is signature-4
  and (in `w=√z`) satisfies a **Heun** equation `w(1-w²)Φ''+(1-3w²)Φ'-(3/4)wΦ=0`, NOT a
  hypergeometric one, so L6a's coefficient-recurrence template does not transfer directly.
- [landed] `Pptc/Hypergeometric/Signatures.lean` created. `hyp_quarter_three_quarter_Pconstructible`
  is the L9 statement WITH Goursat's V7 as explicit hypothesis `hV7`; proof is unconditional
  otherwise. Also `two_mul_div_one_add_lt_one`, `abs_two_mul_div_one_add_lt_one`.
  `lean_diagnostic_messages` for the file: CLEAN (no items). No `sorry`/`axiom`.
- [blocker] V7 itself unproved. Precise obligation: for `0 ≤ w < 1`,
  `hyp (1/4)(3/4)1 (w^2) = (1+w)^(-1/2) * hyp (1/2)(1/2)1 (2w/(1+w))` (take `w = √z`).
  Two routes, both need new work beyond the current library:
  (a) coefficient: show `∑_{n=0}^N hypCoeff (1/2)(1/2)1 n · 2^n · (-1)^{N-n} · C(N-1/2,N-n)`
      equals `hypCoeff (1/4)(3/4)1 (N/2)` for even `N` and `0` for odd `N` (a Vandermonde-type
      holonomic identity; Gosper-type sums are NOT in Mathlib);
  (b) ODE: prove the three formal ODEs (hypSeries (1/4)(3/4)1, hypSeries (1/2)(1/2)1, and the
      Heun pullback under `w ↦ w^2` with prefactor `(1+w)^(-1/2)`) and match initial terms.
  Next concrete step: add a general `hypSeries_ode (a b c)` lemma to a NEW file (do not edit
  Basic.lean) and reuse Quadratic.lean's coeff-extraction pattern; then (b).
- [facts] `sqrt_Pconstructible`, `rpow_Pconstructible` exist (Pptc.Basic).
  `hyp_half_half_one_Pconstructible : PConstructible c -> |c|<1 -> PConstructible (hyp (1/2)(1/2)1 c)`.
  L6a's Quadratic.lean did NOT land real `hyp_quadratic` (only the formal power-series
  identity); its blocker was no `PowerSeries.sum`/`IsLinearTopology ℝ ℝ` for evaluation.
  DLMF 15.8 has no single transformation matching V7 (checked); V7 is a quartic composition.
  Next: decide route for identity (2); fallback = conditional (1).
