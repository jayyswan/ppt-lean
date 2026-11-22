# z123_71.py -- session 71: the residue scheme Z123 = {3 Tr_{k3/k}(x^j) + z^j = 0, j = 1, 2, 3}
# in P(k3 x k), k3 = k(lam^(1/3)), x = p + q*kap + r*kap^2 (the S70.2 valuation analysis with the
# quadric Tr y^2 in place of Tr y^5). Prints the closed points over Q (factor degrees of the
# eliminant), to decide whether V_3 = {Tr y = Tr y^2 = Tr y^3 = 0} has points over the S70.2 3-field.
# usage: python3 z123_71.py [lam=10]
import sys, cypari
pari = cypari.pari
lam = int(sys.argv[1]) if len(sys.argv) > 1 else 10
# multiplication matrix of x on the basis 1, kap, kap^2 (kap^3 = lam)
pari('lam=%d' % lam)
pari('Mx = [p, lam*r, lam*q; q, p, lam*r; r, q, p]')
T = [pari('trace(Mx^%d)' % j) for j in (1, 2, 3)]
print('Tr x   =', T[0]); print('Tr x^2 =', T[1]); print('Tr x^3 =', T[2])
pari('z = -3*(%s)' % T[0])                      # from j = 1
E2 = pari('3*(%s) + z^2' % T[1])
E3 = pari('3*(%s) + z^3' % T[2])
print('quadric:', pari('factor(%s)' % E2))
print('cubic  :', pari('factor(%s)' % E3))
# points with r = 0
R0 = pari('polresultant(subst(%s,r,0), subst(%s,r,0), q)' % (E2, E3))
print('r = 0 chart, resultant in p:', pari('factor(%s)' % R0))
# chart r = 1: eliminate q, factor in p
R = pari('polresultant(subst(%s,r,1), subst(%s,r,1), q)' % (E2, E3))
print('chart r = 1, Res_q in p:', R)
print('factorisation over Q:', pari('factor(%s)' % R))
# a cleaner coordinate: q/r on the conic; resultant in q
Rq = pari('polresultant(subst(%s,r,1), subst(%s,r,1), p)' % (E2, E3))
print('chart r = 1, Res_p in q:', pari('factor(%s)' % Rq))
