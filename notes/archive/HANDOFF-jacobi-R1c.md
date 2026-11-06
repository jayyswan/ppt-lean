# HANDOFF log — jacobi-R1c (sine / 2^x transcendental chains)

Task brief: `PLAN-jacobi-R1c-transcendental-chains.md`
Deliverable: `NOTES-jacobi-R1c.md`
Scripts dir: `archived files/jacobi-scripts/`

- [step 0] Read overview and R1c brief. Created this log.
- [step 1] Script r1c_01_sine_linear.py: verified symbolically speed^2 = q0+q1 cos x+q2 cos^2 x for A.(x,sin x); and symbolically/numerically at w=infinity Q/y dw = -(1/(s i sqrt q2))[q2 u^-2 + (q1/2) u^-1+...]du. Residue at infinity = -q1/(2 s i sqrt q2) (nonzero iff q1=2(ab+cd)!=0); genuine double pole coeff sqrt(q2)!=0 always. So arcsine linear-map form is (first kind)+(exact boundary)+(log if q1!=0); never pure first kind.
- [step 2] Script r1c_02_offsets.py: single-offset-after-A speed identity verified symbolically (concrete rational A) and numerically to 25 digits; correction = -d detA dw/Q_A is rational in w -> elementary. Two-offset F3 chain formula matches complex-step finite differences to 25 digits. Leading sqrt(Q_n)dx untouched, so double pole at infinity survives offsets.
- [step 3] Scripts r1c_03_exp_two.py, r1c_04_step4.py: 2^x base ds = sqrt(Q_A(z))dz/(z ln2) on the conic Y^2=Q_A(z) -> genus 0, sympy gives elementary antiderivative (rational+logs). One offset correction = -d detA ln2 dz/Q_A(z), elementary. Two offsets give sqrt(Q_n)/Q_k^{3/2}dz; after conic parametrisation, V=m(m-2)(m^2-4m+1), disc=432 -> genus 1 reachable.
- [step 4] Script r1c_04_step4.py: disc(Q_A)=-4 det(A)^2<0 so Q_A positive definite, never divisible by (1-w^2); leading term always has the w=infinity double pole. Algebraic-phi argument: at a pole phi~u^-m, dF(phi)~u^{m-1}du (holomorphic), never a double pole; at a Delta_c zero only branch/regular. So no algebraic reparametrisation matches. Preparing NOTES-jacobi-R1c.md.
- [step 5] Wrote NOTES-jacobi-R1c.md (verdict: useful negative; scripts r1c_01..r1c_04 cited). DONE.
