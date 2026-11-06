# HANDOFF — jacobi X6 (identity hunt)

Progress log. Append a line after every step. Read PLAN-jacobi-X6-identity-hunt.md for the brief.

- [step 0] Read PLAN-jacobi-X0-overview.md and PLAN-jacobi-X6-identity-hunt.md in full. Created this log.
- [step 1] Reviewed prior notes (R3, X1, X3, X4) and scripts. Confirmed mpmath 1.3.0. Building a shared library module X6_lib.py for all searches.
- [step 2] PSLQ search complete (X6-01-pslq.py): 4 moduli x u in {1/2,1,3/2}, full CORE (48) for 'am' + all subsets size<=2 of PRIME(16) and size-3 of PRIME3(10), 5 targets, 100 digits. 15372 calls, 0 raw hits. results JSON empty.
- [step 3] Naive full-library grid fit gave spurious 1e-14 off-grid for ALL targets (rank-deficient/ill-conditioned: CORE rank 22 of 48). Extrapolation test (train u in [0.05,1.0], test [1.05,1.45]) blew up to 2.9e-6 for am, so NOT an identity. Rewriting X6-02 to judge small well-conditioned subsets by extrapolation.
- [step 4] X6-02-fits.py rewritten: small well-conditioned subsets (k<=6 of PRIME) judged by extrapolation u in [1.5,1.95]; min off-grid ~2e-6 but extrapolation 1e-4..1e-2. Greedy OMP over full CORE (12 terms) train ~1e-8 but extrapolation 1e-2..1e-5. No functional identity. 0 candidates < 1e-8.
- [step 5] Wrote C:\dev\Powerpoint\lean\NOTES-jacobi-X6.md (substantive): plain summary, exact search space (48 CORE/16 PRIME/10 PRIME3, 4 moduli, u sets, per-family defining move), PSLQ/fit/composition results all negative, ill-conditioning caveat, scripts table, precise negative statement. Search 4 section is a placeholder.
- [step 6] Wrote X6-04-special.py and ran search 4. Caught a spurious-relation trap at 100 digits (false degree-3, coeff ~1e11) and a verifier-precision bug; fixed by PSLQ at 160 digits/maxcoeff 1e8 + 350-digit re-verification. Results: K/2 degQ=4 degQ(sqrt(1-c))=2; K/3 quartic over Q (c=1/2: x^4-2x^3+4x-2; c=1/3: x^4-2x^3+6x-3; c=7/10: 7x^4-14x^3+20x-10); all other tested mK/n degree >6. Appended section 4 to NOTES-jacobi-X6.md and updated summary/scripts table.
