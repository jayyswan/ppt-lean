# HANDOFF: Y1b (square descent and variable-affine offset towers)

Status: **proposed, not started** (2026-11-10). Plan section `Y1b` in
`PLAN-algebraic.md`; background in `Y1a.md` and `SUMMARY.md` §8.

## Why this is the general-method attack

`Y1a` proves Theorem R: if there are \(J\ge n-1\) pairwise non-homothetic positive-definite
binary forms \(Q_j\) over \(L\) with every \(Q_j(\tau)\) a square in \(K_L\), then \(\beta\in P\).
The geometry of the needed variety
\(V_\tau=\{\rho:\rho^2\in\langle1,\tau,\tau^2\rangle\}\) is understood: a smooth complete
intersection of \(n-3\) diagonal quadrics, K3 at \(n=6\), general type for \(n\ge7\).

The open problem is **arithmetic**: find the forms. Fixed engines (egg, piriform, offset egg,
text warp) add a constant number of parameters and cannot change the asymptotics. Y1b attacks
the square condition directly.

## First computation (Y1b.1)

Fix a generic \(q\) of degree \(7\) (then \(8,9\)) and \(\tau=\beta\). Take a rank-one form

\[
B_0=\ell\ell^T,\qquad Q_{B_0}(\tau)=\ell(\tau)^2,
\]

which is automatically a square. For \(B_1\) positive definite and \(t>0\), set
\(B_t=B_0+tB_1\); \(B_t\) is positive definite. The condition

\[
Q_{B_t}(\tau)=r^2
\]

is a conic over \(K_L\) with the \(K_L\)-point \((t,r)=(0,\ell(\tau))\).

**Question:** does it have a point with

\[
t\in L,\qquad r\in K_L,
\]

and \(B_t\) positive definite? This is a Kummer/descent condition. Parameterize the conic
over \(K_L\), impose \(t\in L\), and compute the obstruction class in \(H^1(L,\mu_2)\).
Vary \(B_1\) and record whether any direction gives a positive-definite \(L\)-point.

Deliverable: `Y1b.md` with the exact conic, the obstruction, and a positive result or a scoped
negative.

## If positive

Vary \(B_1\) to get \(J\ge n-1\) non-homothetic positive-definite forms; feed them into
Theorem R; run the linear system on a totally real \(S_7\) or \(S_9\) polynomial. Then write
the Lean statement for the resulting unconditional theorem.

## If negative

- Allow **variable affine layers**: two shape parameters per layer in addition to the distance
  (three per layer). Count \(3J\) parameters against \(J\) square conditions and \(n\) linear
  equations; test whether the shape parameters absorb the obstruction.
- Test **overshoot** (crossing degree \(>n\)).
- Record a scoped obstruction to the distance-only tower; do not conclude anything about
  `algebraic_Pconstructible`.

## Files

- `notes/algebraic/PLAN-algebraic.md` — stream Y1b and the task table.
- `notes/algebraic/Y1a.md` — Theorem R, \(V_\tau\), simultaneous-squares geometry.
- `notes/algebraic/SUMMARY.md` §8 — summary bullet.
- `notes/algebraic/HANDOFF-alg-Y1b.md` — this file.
