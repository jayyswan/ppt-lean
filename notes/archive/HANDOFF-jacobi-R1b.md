# HANDOFF log — jacobi-R1b (polynomial / Bezier / power-law chains)

- [start] Read PLAN-jacobi-00-overview.md and PLAN-jacobi-R1b-polynomial-chains.md in full.
- [start] Created this log. Next: inspect repo (Jacobi.lean, Defs.lean) and set up script dir.
- [env] Python 3.12 + mpmath 1.3.0 / sympy 1.12 confirmed at full path. Script dir exists.
- [step1] Enumerating rational b (|num|,den<=12) by Chebyshev/genus of y^2=1+k x^{2b-2}. Script R1b-01-powerlaws.py.
- [step1] Done: 18 distinct elliptic b (|P|=3 or 4). Two curves only: j=0 (cubic, |P|=3) and j=1728 (quartic, |P|=4). Scripts R1b-01, R1b-02. Boundary decompositions exact (residual 0); P=4 Legendre reduction residual 1e-31; moduli verified via period ratios.
- [step2] PH cubic: Tschirnhausen r=(t-t^3/3, t^2), offset d, linear map A. Deriving ds = sqrt(P(t))·R(t) dt symbolically + asy at infinity. Script R1b-03-ph.py.
- [step2] Done: Tschirnhausen PH, ds=sqrt(P)R dt verified to 30 digits; P quartic, R(inf)=1, P·R~(37/9)t^4 (not const/linear); order-4 pole at infinity (second kind). Depth-2 speed ~ t^2. No pure first kind.
- [step3/4] General (non-PH) cubic Bezier + offset + linear map: speed formula verified to 30 digits. On y^2=P, ds=R'dt/y with R'=P(P0^3-dW)/P0^3; R'~deg4 at infinity, first-kind needs deg<=1 => not first kind. Cusps give finite speed. F2 second-kind part is exact (boundary). Script R1b-04-general.py.
- [step4] Next: pole-at-infinity orders for poly_graph/power_law, loopholes (bounded sub-arcs, non-algebraic phi). Script R1b-05-pole.py. Then write NOTES-jacobi-R1b.md.
- [step4] Done: y=x^6 order-7 pole; b=5/2 order-6 pole; F2 second-kind part exact; bounded windows don't change differential. Script R1b-05-pole.py.
- [step5] Wrote C:\dev\Powerpoint\lean\NOTES-jacobi-R1b.md (substantive): verdict = NO single-curve pure-first-kind curve in poly_graph(<=6)/cubic_bezier/power_law + linear/translate/offset class. Negative result, assumptions and loopholes (non-algebraic phi, inter-curve cancellation, R3 composition) stated. Five scripts cited: R1b-01..R1b-05.

