# HANDOFF-jacobi-X2: amplitude as a crossing

Progress log for PLAN-jacobi-X2. Append one line per step.

- [start] Read PLAN-jacobi-X0-overview.md and PLAN-jacobi-X2-crossings.md in full. Log created.
- [step 1] Wrote/ran archived files/jacobi-scripts/X2-01-basics.py: Pfaffian chain residual ~4e-22 (40 dps); am=atan2(sn,cn) to 41 digits; F(atan2(sn,cn))=u; F not a finite cos-2k polynomial (residual floor, nonzero coefs); pendulum time = F-integral exactly (18 digits) while Euclidean portrait arclength differs.
- [step 2] Ran X2-02-crossings.py: abutting-arc crossing reproduces ellipticEAm to 4.1e-41 at c in {0.3,0.7,0.93}, 3 lengths each (positive calibration); Kepler, scaled-sine, pendulum+line, EAm-endpoint candidates all fail the Jacobi ODE (z')^2=1-c sin^2 z; circularity v(u)=a*am(u)-sin(am u) reconstructs am to 4.1e-41.
- [step 3] Ran X2-03-selfref.py: 2 unknowns x 2 equations count; fixed-intersection crossing is length-independent; moving-circle x sine and moving-line x circle fail the Jacobi ODE; required line parameter p(u)=sn(u)-a cn(u) reproduces am to 4e-41 (circularity).
- [step 4] Wrote NOTES-jacobi-X2.md (all 4 questions, equation class, Pfaffian/pendulum, Kepler/addition, self-referential, synthesis/excluded class/loopholes, EAm positive calibration, verification index, references).
- [step 5] Re-ran all 3 scripts: OK in 6.55 s / 1.48 s / 0.17 s (all <30 s). Verified cited Lean names/lines. No .lean file created, edited or deleted. DONE.
