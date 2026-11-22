# Session 63 (S63.5): local solubility of V_K at primes p by plane sections (any size of p).
# F3 = Tr(u^3) - (Tr u)^3, F5 = Tr(u^5) - (Tr u)^5 as integer forms in the 9 coordinates of u
# w.r.t. an integral basis (nfinit([f, listP]) maximal at the primes asked for, or at all primes
# below 10^6). For each p: random affine F_p-planes c = x*a + y*b + c0, common roots of F3, F5
# mod p via the resultant in y, then a 2x2 minor of the 2x9 Jacobian that is a unit mod p
# (Hensel => a Q_p-point). Prints per prime the number of planes used, or FAIL.
# Usage: python3 locplane63.py <psl|s9|plant|poly> <pmin> <pmax> [extra primes,comma] [dec]
import sys, cypari, random
pari = cypari.pari
pari.allocatemem(4*10**9)
POLYS = {
 'psl': 'x^9 - 3*x^8 - 12000*x^7 - 295072*x^6 + 27805575*x^5 + 1157871573*x^4 + 7683210630*x^3 - 82305140040*x^2 - 848281897593*x - 1186350537195',
 's9': 'x^9 - 288*x^7 + 42*x^6 + 30219*x^5 - 10290*x^4 - 1364812*x^3 + 826728*x^2 + 22291201*x - 21772799',
 'plant': '6000*x^9 + 18000*x^8 - 38973*x^7 - 116919*x^6 + 68613*x^5 + 205839*x^4 + 6606*x^3 - 92271*x^2 - 25881*x + 1640',
}
fstr = POLYS.get(sys.argv[1], sys.argv[1])
_f = pari(fstr); _lc = int(pari.pollead(_f)); _n = int(pari.poldegree(_f))
if _lc != 1:   # monic transform theta' = lc*theta
    fstr = str(pari('subst(%s, x, x/%d)*%d^%d' % (fstr, _lc, _lc, _n-1)))
pmin, pmax = int(sys.argv[2]), int(sys.argv[3])
extra = [int(q) for q in sys.argv[4].split(',')] if len(sys.argv) > 4 and sys.argv[4] not in ('', '-') else []
dec = len(sys.argv) > 5 and sys.argv[5] == 'dec'
lst = ','.join(str(q) for q in extra)
nfs = 'nfinit([%s, %s])' % (fstr, ('[%s]' % lst) if extra and pmax < 2 else '10^6' if not extra else 'concat(primes(primepi(10^5)),[%s])' % lst)
pari('NF = %s; n = poldegree(NF.pol); zk = NF.zk;' % nfs)
pari('cv = vector(n, i, eval(Str("c" i)));')
pari('u = sum(i = 1, n, cv[i]*zk[i]); s = polsym(NF.pol, 5*n);')
pari('TR(P) = my(Q = lift(Mod(P, subst(NF.pol, x, x)))); sum(m = 0, poldegree(Q, x), polcoef(Q, m, x)*s[m+1]);')
pari('t = TR(u); F3 = TR(u^3) - t^3; F5 = TR(u^5) - t^5; F1 = t;')
if dec:
    pari('EQ = [F1, F3, F5];')
else:
    pari('EQ = [F3, F5];')
pari('JAC = matrix(#EQ, n, r, j, deriv(EQ[r], cv[j]));')
pari('print("forms ready: F3 terms ", #Vec(F3), "  degree n = ", n);')
# GP routine: try planes mod p
pari(r'''
tryp(p, maxpl) = {
  my(k = #EQ);
  for (pl = 1, maxpl,
    my(a = vector(n, i, random(p)), b = vector(n, i, random(p)), c0 = vector(n, i, random(p)));
    my(sub = vector(n, i, a[i]*'xx + b[i]*'yy + c0[i]));
    my(G = vector(k, r, substvec(EQ[r], cv, sub) * Mod(1, p)));
    my(R, xs);
    if (k == 2, R = polresultant(G[1], G[2], 'yy), R = gcd(polresultant(G[1], G[2], 'yy), polresultant(G[1], G[3], 'yy)));
    if (R == 0, next);
    xs = polrootsmod(lift(R), p);
    for (ix = 1, #xs,
      my(x0 = xs[ix], g = gcd(subst(G[1], 'xx, x0), subst(G[2], 'xx, x0)), ys);
      if (k == 3, g = gcd(g, subst(G[3], 'xx, x0)));
      if (poldegree(g, 'yy) < 1, next);
      ys = polrootsmod(lift(g), p);
      for (iy = 1, #ys,
        my(pt = vector(n, i, a[i]*x0 + b[i]*ys[iy] + c0[i]));
        if (pt == vector(n, i, Mod(0, p)), next);
        my(J = substvec(JAC, cv, pt) * Mod(1, p));
        if (matrank(J) == k, return([pl, lift(pt)]))));
  );
  return(0);
}
''')
primes = [int(q) for q in pari('primes([%d, %d])' % (pmin, pmax))] + [q for q in extra if q > pmax]
fails = []
for p in primes:
    r = pari('tryp(%d, 12)' % p)
    if r == 0:
        fails.append(p); print(p, 'FAIL (no smooth F_p-point on 12 planes)', flush=True)
    elif p < 60 or p in extra:
        print(p, 'smooth F_p-point on plane', r[0], flush=True)
print('done: %d primes, fails %s' % (len(primes), fails))
