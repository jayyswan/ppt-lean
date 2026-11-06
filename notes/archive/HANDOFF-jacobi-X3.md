# HANDOFF — jacobi X3 (classical geometric mechanisms)

Progress log for `PLAN-jacobi-X3-classical-mechanisms.md`. Append one line per step.
Deliverable: `NOTES-jacobi-X3.md`. Research only — no `.lean` file created, edited or deleted.

- [start] Read `PLAN-jacobi-X0-overview.md` and `PLAN-jacobi-X3-classical-mechanisms.md` in full.
  Created this log. Skimmed HANDOFF/notes of X1, X2, R2, R3 for prior art (D-finite, crossing
  autonomy, Serret first-kind family, Landen/mixed-EF killed). Next: web sources for the six
  mechanisms, then numeric scripts under 30 s each.
- [sources] Collected URLs: DLMF §19.30 (ellipse/hyperbola/lemniscate arclength), MathWorld
  Poncelet's Porism (tangent eq. r+d cos φ−cos(φ−θ)=0), Dinčǎ arXiv:0902.1421 §3.2 (exact
  Graves statement), Fagnano statement (Eppstein junkyard), Mingari-Scarpello arXiv:1209.4909
  (hyperbola rectification Maclaurin→Landen), Greenhill 1892 (archive.org).
- [step 1] X3-01-graves.py (ran 0.5 s): confirmed to 35 digits on two confocal pairs that
  |PT1|+|PT2| + (inner arc on the far side of P) is constant (spread 2.4e-35 and 0.0). The arc
  measured is a*(E(φ2)−E(φ1)) (pure 2nd kind). Solving it backwards for a target arc recovers
  the eccentric angle to 1e-24 = inverse-E (ellipticEAm), not am. Verdict: second-kind only.
- [step 2] X3-02-hyperbola.py (ran 1.2 s): verified DLMF 19.7.5+19.7.7 reduction of the hyperbola
  arc, s=(b²/c)F(θ,κ) − c E(θ,κ) + algebraic, to ~30 digits at a=2,b=1 (t=0.3..2.5). Both
  coefficients nonzero. Inverting the mixed map recovers θ but differs from am(target/β): no F
  inverse. Ellipse arcs contribute E only, so E-parts cancel but the F-part has no drawable
  partner (R1/R2). Verdict: negative.
- [step 3] NOTES-jacobi-X3.md WRITTEN (deliverable exists). Covers mechanisms 1–3 with verified
  numbers (Graves 2.4e-35/0.0; hyperbola ~30 digits; Fagnano 2.4e-33), mechanism 4 Poncelet as
  partial (degree-2 algebraic, coarse coordinate not reduced to standard F), mechanism 5
  (lemniscate/AGM fixed modulus, pendulum time = F, elastica not a base curve), mechanism 6 survey,
  and the precise negative claim (excluded class + the Serret/encoded-F assumption that would let
  one through). Summary, table, references and verification index included. No .lean file touched.

