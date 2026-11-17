# HANDOFF: Y1b (rank-one square deformation) — DONE

Status: **done (2026-11-10); scoped negative.** Deliverable: `notes/algebraic/Y1b.md`.
No Lean edits, no new task is required from this stream.

## What was asked

Y1b.1 asked whether the conic \(Q_{B_0+tB_1}(\tau)=r^2\) (with \(B_0=\ell\ell^T\) rank one) has a
point with \(t\in L\), \(r\in K_L\), \(B_t\) positive definite, and to identify the Kummer/descent
obstruction. Background: `Y1a.md` (Theorem R, \(V_\tau\)), `Z5.md` (no genus 0/1 curves on
\(V_\tau\)), `A1.md` (Theorem G).

## What was found

1. **The conic is split.** \(r^2 - Q_{B_1}(\tau)ts = \ell(\tau)^2s^2\) is smooth and already has the
   point \((0:\ell:1)\) with \(t=0\in L\), \(r\in K_L\). The \(H^1(L,\mu_2)\) class is **zero**;
   there is no descent obstruction to compute. Parametrization:
   \(t = C/m^2 - 2\ell/m\), \(r = C/m-\ell\).
2. **The real object is the pencil curve** \(X_C=\{r : r^2-\ell(\tau)^2\in L\cdot Q_{B_1}(\tau)\}
   \subset V_\tau\): a \((\mathbb Z/2)^n\)-cover of the \(t\)-line, genus
   \(1+(n-3)2^{n-2}\) (129, 321, 769 at \(n=7,8,9\)).
3. **Y1b.1 = the first step of SS.** Every positive-definite form is \(B_0+tB_1\) with
   \(B_0=\ell\ell^T\succeq0\), \(t>0\). So the deformation family is the whole PD cone, and varying
   \(B_1\) sweeps \(V_\tau\). No weakening.
4. **The obstruction is the target field.** The cover is the \(K\)-twist of the split
   \((\mathbb Z/2)^n\)-cover. The fibre at \(t=0\) is the \(S_n\)-resolvent scheme of \(q\): \(n+1\)
   components of degrees \(\binom{n}{k}\). The \(k=1\) component is \(K\) itself [Proof; Wolfram
   \(n=5\)]. Hence the arithmetic Galois closure has \(S_n\) as a quotient and is not solvable for
   \(n\ge5\). A1's Theorem G must be checked on the arithmetic closure, not the geometric monodromy
   (the geometric group here is the solvable \((\mathbb Z/2)^n\)).
5. Rational-point searches on \(X_C\) found nothing for \(n=3,4,5,7\) in small height (evidence
   only).

## Consequences

- Y1b.4 **not launched**; Y1b.2 **vacuous** (the shapes were already free; only \(J+2\ge n\)
  matters, kernel dimension \(J+2-n\)); Y1b.3 **answered negatively** (no \(\mu_2\)-class; the class
  is the \(S_n\)-torsor \(K/\mathbb Q\)).
- Untouched: overshoot engines, other bases (rational sextic graphs, power laws with
  \(b=1\pm1/k\)), the circle partner, and SS itself.

## Files

- `notes/algebraic/Y1b.md` — new, the deliverable.
- `notes/algebraic/PLAN-algebraic.md` — Y1b section and table updated to done; wave plan adjusted.
- `notes/algebraic/SUMMARY.md` — §8 bullet and §10 paragraph updated.
- `notes/algebraic/HANDOFF-alg-Y1b.md` — this file.
