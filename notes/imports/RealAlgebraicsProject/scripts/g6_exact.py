# Session 9: exact version. For each multiplicity pattern m (k <= 5 distinct values), the
# critical-point system reduces to 0, 1 or 2 equations in affine unknowns a (and b).
# Eliminate b by a resultant, factor over Q, and for each irreducible factor f(a) compute the
# common root b as gcd over Q[a]/f. Then g6/p2^3 is an exact element of Q[a]/f; we record its
# minimal polynomial and its values at the real roots of f. Rigorous up to PARI's factoring.
from g6_certify import system, partitions
import sympy as sp, random, re, cypari
pari = cypari.pari
pari.allocatemem(2*10**9)

def topari(e, names):
    s = str(sp.expand(e)).replace('**', '^')
    for old, new in names.items(): s = re.sub(r'\b%s\b' % old, new, s)
    return pari(s)

def analyse(m, seed=1):
    v, lin, rest = system(m)
    rnd = random.Random(seed)
    dehom = sum(sp.Integer(rnd.randint(1, 97)) * vi for vi in v) - 1
    linear = [l for l in lin + rest if sp.Poly(l, *v).total_degree() == 1] + [dehom]
    nonlin = [e for e in rest if sp.Poly(e, *v).total_degree() > 1]
    s = sp.solve(linear, list(v), dict=True)[0]
    free = [vi for vi in v if vi not in s]
    eqs = [sp.expand(sp.numer(sp.together(e.subs(s)))) for e in nonlin]
    if any(e == 0 for e in eqs): return 'positive-dimensional', []
    names = {str(f): n for f, n in zip(free, ['a', 'b'])}
    vec = [topari(s[vi], names) if vi in s else pari(names[str(vi)]) for vi in v]
    def ratio(vals):
        P = lambda j: sum(mi * vi**j for mi, vi in zip(m, vals))
        return (231*P(2)**3 - 966*P(2)*P(4) + 1008*P(6) - 256*P(3)**2), P(2)
    results = []
    if len(free) == 0:
        num, den = ratio(vec); results.append(('rational', num/den**3, [num/den**3]))
        return 'ok', results
    if len(free) == 1:
        factors = pari.factor(topari(eqs[0], names))[0]
        subs = lambda f: {}  # b absent
    else:
        A, B = topari(eqs[0], names), topari(eqs[1], names)
        res = pari.polresultant(A, B, pari('b'))
        if res == 0: return 'positive-dimensional', []
        factors = pari.factor(res)[0]
    for f in factors:
        if pari.poldegree(f, pari('a')) == 0: continue
        if len(pari.polrootsreal(f)) == 0: continue   # no real points on this factor
        z = pari('(f)->my(t=varlower("t"));Mod(t,subst(f,a,t))')(f)
        if len(free) == 2:
            g = pari('(A,B,z)->gcd(subst(A,a,z),subst(B,a,z))')(A, B, z)
            if pari.poldegree(g, pari('b')) != 1:
                d = pari.poldegree(g, pari('b'))
                assert pari.poldegree(f) == 1, 'nonlinear f with gcd degree > 1'
                gq = pari.lift(pari.lift(g)) if True else g
                gq = pari('(g)->substpol(lift(g), variable(lift(polcoef(g,0))), 0)')(g) if False else pari('(g)->my(c=Vec(g));Pol(apply(x->if(type(x)=="t_POLMOD",lift(x),x),c),b)')(g)
                rb = pari.polrootsreal(gq) if pari.poldegree(gq) > 0 else []
                results.append(('gcd degree %s, real b roots %s' % (d, len(rb)), f, None)); continue
            bval = -pari.polcoef(g, 0, pari('b')) / pari.polcoef(g, 1, pari('b'))
            vals = [pari.subst(pari.subst(x, pari('a'), z), pari('b'), bval) for x in vec]
        else:
            vals = [pari.subst(x, pari('a'), z) for x in vec]
        num, den = ratio(vals)
        if den == 0:
            results.append(('p2=0', f, None)); continue
        q = num / den**3
        if q == 0:
            # exact: count coincidences among the k values; need a merged multiplicity >= 7
            k = len(vals); merged = list(m)
            parent = list(range(k))
            for i in range(k):
                for j in range(i):
                    if vals[i] == vals[j]: parent[i] = parent[j]; break
            tot = {}
            for i in range(k): tot[parent[i]] = tot.get(parent[i], 0) + m[i]
            assert max(tot.values()) >= 7, ('zero off the planes', m, vals)
        mp = pari.minpoly(q)                # exact minimal polynomial of g6/p2^3 at these points
        rr = pari.polrootsreal(f)          # real embeddings
        ql = pari.lift(q)
        ev = pari('(q,r)->if(type(q)=="t_POL", subst(q, variable(q), r), q)')
        evals = [ev(ql, r) for r in rr]
        results.append((str(mp), f, evals))
    return 'ok', results

if __name__ == '__main__':
    for k in range(2, 6):
        for m in partitions(9, k):
            st, res = analyse(m)
            if st != 'ok': print(m, st); continue
            for mpq, f, evals in res:
                if evals is None: print(m, mpq, 'factor', f); continue
                if isinstance(f, str) or mpq == 'rational': print(m, 'value', f); continue
                if len(evals) == 0: continue
                print(m, 'deg f', pari.poldegree(f), 'minpoly(g6/p2^3) =', mpq,
                      'real values:', [float(e) for e in evals])
