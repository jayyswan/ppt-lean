# msparam.py -- read an msolve .ms input and its .out parametrisation (char p), verify the sign convention,
# and compute the minimal polynomial (eliminant) of a chosen variable, its squarefree degree and factor degrees.
# Usage: python3 msparam.py <file.ms> <file.out> <var>
import sys, ast, cypari
pari = cypari.pari; pari.allocatemem(3*10**9)
ms, outf, var = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(ms).read().split('\n')
vars_in = lines[0].split(','); p = int(lines[1])
polys = ''.join(lines[2:]).split(',')
t = open(outf).read().replace('\n', '').strip().rstrip(':').rstrip(';')
L = ast.literal_eval(t)
_, (pp, nv, deg, vars_out, form, par) = L
P = par[1]
f = pari('Pol(%s,T)' % str(P[0][1][::-1])) * pari('Mod(1,%d)' % p)
den = pari('Pol(%s,T)' % str(P[1][1][::-1])) * pari('Mod(1,%d)' % p)
nums = [pari('Pol(%s,T)' % str(q[0][1][::-1])) * pari('Mod(1,%d)' % p) for q in P[2]]
cs = [q[1] if len(q) > 1 else 1 for q in P[2]]
elimvar = vars_out[-1]
def subst_all(sign):
    vals = {}
    for v, n, c in zip(vars_out[:-1], nums, cs):
        vals[v] = pari.Mod(sign * n * pari.Mod(1, p) / c, f) / pari.Mod(den, f)
    vals[elimvar] = pari.Mod(pari('T'), f)
    return vals
for sign in (1, -1):
    vals = subst_all(sign)
    ok = True
    for e in polys[:2]:
        ex = e
        g = pari(ex.replace('^', '^'))
        # substitute variables
        for v in vars_in:
            g = pari.subst(g, pari(v), vals[v])
        if g != 0: ok = False
    print('sign', sign, 'satisfies eqs:', ok)
    if ok: good = vals
mp = pari.charpoly(good[var])
mp = pari.subst(pari.lift(mp), pari('x'), pari('X'))
g = pari.gcd(mp, pari.deriv(mp, pari('X')))
print('charpoly deg', pari.poldegree(mp), 'gcd(mp, mp\') deg', pari.poldegree(g))
sq = pari('(a,b)->a/b')(mp, g)
F = pari.factor(sq)
print('distinct', var, 'values:', pari.poldegree(sq), 'factor degrees', sorted(int(pari.poldegree(F[0][i])) for i in range(len(F[0]))))
