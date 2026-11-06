# HANDOFF: EG-F1-exp (exp world, F1 shard)

Deliverable: `impress/notes/EG-F1-exp.csv` (48 rows).

## Progress log

- Family A (y = c x^k Exp[x], k=0..3, c in {1/2,1,2}, [0,1] and [-1,0]): 24 curves computed (NIntegrate at WP 70, 60 digits; Integrate with 30 s TimeConstrained). 6 closed forms found (A1-A6, k=0 only); none contains EulerGamma or exponential-integral functions. Log appears in A1, A2.
- Family B (loop t -> (a t^k e^t, b t^(k+1) e^t), t in (-Infinity,0], k=1..3, (a,b) in {(1,1),(1,2),(2,1)}): 9 curves computed. B3 (k=1, a=2, b=1) has exact value 2 (speed = e^t(t^2+2t+2), antiderivative e^t(t^2+2)). B8 showed an NIntegrate convergence warning in the first pass; re-run with split limits {-Infinity,-40,-10,-3,0} at 80 WP agrees with the reported 60 digits to about 61 digits. No EulerGamma in any closed form.
- Family C (y = c x^k Log[x], k=0..2, c in {1,2}, [1,2] and [1/2,1]): 12 curves computed. 4 closed forms (C1-C4, k=0); Log appears in C3, C4; none contains EulerGamma or exponential-integral functions.
- Family D' (y = c x e^x + x^2/2, c in {1/2,1,2}, [0,1]) (replaces the withdrawn family D per coordinator correction; old D was not computed): 3 curves computed. No closed forms.
- Coefficient step: no closed form contains EulerGamma, so no Coefficient[...] values to report.

## Candidate relations

- FindIntegerNullVector on {v, EulerGamma, 1, Pi, Log[2], E, Exp[-1]} at 50 digits, tolerance 10^-40, for all 48 values: no integer null vector found for any value. No candidates, so no 100-digit retest was needed.
- Note: the Wolfram kernel does not define FindIntegerRelation; FindIntegerNullVector was used instead.

## Notes

- "closed_form = none" means Integrate returned unevaluated or hit the 30 s time limit; the two cases are not distinguished.
- Log entries in closed_form_has are from Log[...] heads in the closed form.
