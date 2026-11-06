# X2-03-selfref.py
# PLAN-jacobi-X2, step 3 (Question 4): self-referential crossings.
#  (1) the unknown/equation count for a crossing system with arc-length inputs;
#  (2) numeric: a moving circle crossed with the sine curve (parameter p=u) -- Jacobi ODE test;
#  (3) numeric: two fixed drawable curves + arcs of length L1(u),L2(u); show the shared
#      endpoint must be the *fixed* geometric intersection, hence length-independent.
# mpmath parameter convention m = c.
from mpmath import (mp, mpf, ellipfun, ellipe, sin, cos, sqrt, pi, atan2, findroot, nstr)

mp.dps = 40

def am(u, c):
    return atan2(ellipfun('sn', u, c), ellipfun('cn', u, c))

print("== (1) Unknown / equation count ==")
print("   A crossing A1 cap A2 = {P} of two arc sets has unknowns (x,y): 2,")
print("   equations P in C1, P in C2: 2  -> generically 0-dimensional (isolated points).")
print("   The lengths L1(u),L2(u) enter only (i) as window bounds on which sub-arc is present")
print("   and (ii) through the arc endpoints. Hence either:")
print("     (i') P is the fixed geometric intersection of C1,C2 (L-independent), or")
print("     (ii') P is a shared endpoint, so the 'self-reference' is one scalar relation")
print("           s1^{-1}(L1(u)) = s2^{-1}(L2(u)) between the two drawable arc lengths.")
print("   Either way there is no free parameter left to bend a coordinate into am(u);")
print("   any u-dependence must come from a curve parameter p(u) (next tests).")
print()

print("== (2) Moving circle (center p(u), radius 1) crossed with y=sin x ==")
print("   Equations: (x-p)^2 + sin(x)^2 = 1  (unit circle) and y=sin x;  z=x(u).")
print("   Jacobi ODE test: PASS iff (z')^2 == 1 - c sin^2 z.")
for c in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    mx = mpf(0)
    for u in [mpf('0.2'), mpf('0.5'), mpf('0.8')]:
        p = u
        # solve (x-u)^2 + sin^2 x = 1 near the right branch x ~ u+something
        z = findroot(lambda x: (x-p)**2 + sin(x)**2 - 1, p, tol=mpf('1e-30'))
        # implicit derivative: 2(z-p)(z'-1) + 2 sin z cos z z' = 0
        zz = z; lhs = 2*(zz-p); rhs = 2*sin(zz)*cos(zz)
        zp = lhs/(lhs + rhs)
        mx = max(mx, abs(zp**2 - (1 - c*sin(zz)**2)))
    print(f"   c={nstr(c,3)}: max|z'^2-(1-c sin^2 z)| = {nstr(mx,6)}  [{'PASS' if mx<1e-15 else 'fail'}]")
print()

print("== (3) Two fixed curves, arcs of lengths L1(u),L2(u): shared endpoint is L-independent ==")
# C1 = unit circle x^2+y^2=1 (drawable ellipse width=height=2), C2 = line y = x (rectangle edge,
# drawable as a restricted segment).  Their two intersections are fixed: (+-1/sqrt2,+-1/sqrt2).
# Arc of C1 from (1,0) of length L1(u) (angle L1) ends at angle L1; arc of C2 from (1,1) of
# length L2(u) ends at a point on the line.  If the far endpoints coincide, that point is one
# of the two fixed intersections, so L1,L2 are the fixed arc lengths to it, independent of u.
inv = 1/sqrt(2)
P = (inv, inv)                      # the fixed intersection in the first quadrant
L1_fixed = mp.atan2(P[1], P[0])     # = pi/4, arc length on unit circle
# line y=x parametrized by arclength s from origin: distance from (1,1) to (inv,inv)
L2_fixed = sqrt(2) - sqrt(2)*inv    # |(1,1)-(inv,inv)| = sqrt2 (1 - 1/sqrt2)
print(f"   fixed shared-endpoint configuration: P={nstr(P[0],18)},{nstr(P[1],18)}")
print(f"   arc length on circle C1 to P = {nstr(L1_fixed,18)}  (independent of u)")
print(f"   arc length on line   C2 to P = {nstr(L2_fixed,18)}  (independent of u)")
print("   For a fixed u-varying pair (L1(u),L2(u)) the endpoints coincide only at the u where")
print("   (L1(u),L2(u)) hits this fixed pair; the crossing coordinate itself never moves.")
print("   (Moving the curves instead is exactly case (2): parameter-dependent, ODE fails.)")
print()

print("== (4) Moving line y = a x + p(u) crossing the unit circle: exact circularity ==")
print("   Intersection angle theta satisfies sin theta = a cos theta + p, so p = sin theta - a cos theta.")
print("   To force theta = am(u) one must set p(u) = sn(u) - a cn(u), an expression in am.")
for c in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    a = mpf('0.4')
    mx = mpf(0)
    for u in [mpf('0.1'), mpf('0.4'), mpf('0.8'), mpf('1.2')]:
        p = ellipfun('sn', u, c) - a*ellipfun('cn', u, c)
        # theta solves sin th - a cos th = p near am(u); solve via phasor
        # sin th - a cos th = R sin(th - delta), R=sqrt(1+a^2), delta=atan(a)
        R = sqrt(1 + a*a); delta = mp.atan(a)
        th = delta + mp.asin(p/R)
        mx = max(mx, abs(th - am(u, c)))
    print(f"   c={nstr(c,3)}: |theta - am(u)| with p(u)=sn(u)-a cn(u) = {nstr(mx,18)}")
mx = mpf(0)
for c in [mpf('0.3')]:
    a = mpf('0.4')
    for u in [mpf('0.1'), mpf('0.4'), mpf('0.8')]:
        p = u
        R = sqrt(1 + a*a); delta = mp.atan(a)
        th = delta + mp.asin(p/R)
        # dtheta/dp = 1/(R cos(th-delta)); dp/du = 1
        zpt = 1/(R*cos(th-delta))
        mx = max(mx, abs(zpt**2 - (1 - c*sin(th)**2)))
    print(f"   c=0.3: with the plain constructible p(u)=u, max|theta'^2-(1-c sin^2 theta)| = {nstr(mx,6)}  [fail]")
print("   The required p(u)=sn(u)-a cn(u) is P-constructible only if am is; so this loophole")
print("   is circular, not a construction.")
print("DONE X2-03")
