# HANDOFF — jacobi X1 (amplitude as a measured length)

Progress log. Append one line per step. Status: IN PROGRESS.

- [step 0] Read PLAN-jacobi-X0-overview.md and PLAN-jacobi-X1-measure.md in full. Brief understood.
- [step 1] Read Defs.lean arc_length / ellipse / offset constructors exactly. Confirmed: arc_length
  takes an arbitrary tracing gamma, both plane endpoints PConstructible. offset changes speed by
  |1 - d*kappa| (curvature term). Serret obstacle is in Jacobi.lean outlook.
- [step 2] Read R3 notes in full: derivative test, loopholes L0-L11, killed Landen/mixed-EF/Pi,
  open L1 (parameter-dependent curves). X1 adds the D-finite framing.
- [step 3] Wrote+ran X1-01-dfinite-basics.py. Results: complete K,E satisfy their 2nd-order ODEs
  to ~40 digits (D-finite); incomplete E(phi,m) has branch points of exponent 1.5, F of 0.5,
  repeating every pi (infinitely many -> not D-finite); dn has simple poles residue +-i at
  iK',3iK',5iK',2K+iK' (infinite lattice); ellipse arc = E(phi,c) exact; sine arc = moving-modulus
  E exact. Next: write notes skeleton, then offset + candidate tests.
- [step 4] KEY CORRECTION: D-finite IS closed under antiderivatives (operator argument), and
  definite integrals of algebraic families over algebraic bounds are D-finite (holonomic closure).
  So the test's moving-endpoint step is CORRECT for algebraic endpoints (via z=sin(theta)
  substitution): E(arcsin(u/2),c)=int_0^{u/2} algebraic, verified 0.0 residual. The real escape is
  TRANSCENDENTAL endpoints/curves, which Defs.lean permits. First draft of notes was wrong here;
  rewritten.
- [step 5] X1-02-offset.py: speed(offset)=v|1-d*kappa| (40 digits); offset arc = E_c(phi)-d*turn;
  closed parallel perimeter = P-2*pi*d (Steiner). Offset of algebraic curve is algebraic -> no
  escape from D-finite.
- [step 6] X1-03-candidates.py: moving-modulus E/F vs am, 4/6-param fit, off-grid plateau ~0.1
  (no identity). X1-04-dlmf-derivs.py: DLMF 19.4.5/19.4.6 verified to ~31 digits; coefficient
  cancellation forces dn algebraic -> circular.
- [step 7] DLMF 22.16 / Wolfram / MathWorld: only integral reps are int(dn) and the infinite
  Fourier series; no elementary-integrand finite rep. epsilon reps use Jacobi integrands.
- [step 8] NOTES-jacobi-X1.md finalized: verdict = correct-with-exceptions; escapes = transcendental
  fragment (sine/exp curves, sin/cos/2^x/log/ellipticEAm endpoints, reused measurements); explicit
  escape witness construction tree for E(u,c). Outcome negative/partial. DONE.
