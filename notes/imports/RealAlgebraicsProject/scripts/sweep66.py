# sweep66.py -- sweep local nonic algebras at p (default 3) with loc66.plane_test.
# usage: python3 sweep66.py <kind> <count> <planes> <seed> [p] [modulus]
# kinds: eis9 (random Eisenstein degree 9), e3f3 (degree-9 fields with e=3,f=3),
#        c333 (product of three Eisenstein cubics), c36 (Eisenstein cubic x Eisenstein sextic),
#        c3u6 (Eisenstein cubic x unramified sextic), e9list (fixed list of special Eisenstein polys)
# Reports per algebra the number of planes with a certified smooth Q_p-point; flags 0-hit algebras.
import sys, random, cypari
exec(open('loc66.py').read().split("\nif __name__ == '__main__'")[0])
pari = cypari.pari

def eis(d, p, M, rng):
    while True:
        c = [p*rng.randrange(0, M) for _ in range(d)]
        if (c[0] // p) % p == 0: continue   # constant term must be p*unit
        f = pari('x')**d + sum(c[i]*pari('x')**i for i in range(d))
        if pari.polisirreducible(f): return f

def unram(d, p, rng):
    while True:
        f = pari('x')**d + sum(rng.randrange(0, p)*pari('x')**i for i in range(d))
        if pari.polisirreducible(pari('Mod(1,%d)'%p)*f): return f

def e3f3(p, M, rng):
    # norm from U3 = Q_p[t]/(u(t)) of an Eisenstein cubic x^3 + p*a(t) x^2 + p*b(t) x + p*c(t), c(t) a unit
    u = unram(3, p, rng).substpol if False else None
    u = unram(3, p, rng); ut = pari.subst(u, 'x', pari('t'))
    while True:
        a = sum(rng.randrange(0, M)*pari('t')**i for i in range(3))
        b = sum(rng.randrange(0, M)*pari('t')**i for i in range(3))
        c = sum(rng.randrange(0, M)*pari('t')**i for i in range(3))
        if pari.Mod(1, p)*pari.polresultant(ut, c, 't') == 0: continue
        g = pari('x')**3 + p*a*pari('x')**2 + p*b*pari('x') + p*c
        f = pari.polresultant(ut, g, 't')
        if pari.poldegree(f) == 9 and pari.polisirreducible(f): return f

def main():
    kind = sys.argv[1]; cnt = int(sys.argv[2]); NP = int(sys.argv[3]); seed = int(sys.argv[4])
    p = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    M = int(sys.argv[6]) if len(sys.argv) > 6 else 9
    rng = random.Random(seed); random.seed(seed)
    zero = []; tot = 0
    for k in range(cnt):
        if kind == 'eis9': f = eis(9, p, M, rng)
        elif kind == 'e3f3': f = e3f3(p, M, rng)
        elif kind == 'c333': f = eis(3, p, M, rng)*eis(3, p, M, rng)*eis(3, p, M, rng)
        elif kind == 'c36': f = eis(3, p, M, rng)*eis(6, p, M, rng)
        elif kind == 'c3u6': f = eis(3, p, M, rng)*unram(6, p, rng)
        elif kind == 'c3e3u3': f = eis(3, p, M, rng)*eis(3, p, M, rng)*unram(3, p, rng)
        else: raise SystemExit('kind?')
        if pari.poldegree(pari.gcd(f, pari.deriv(f))) > 0: continue
        S = pari.polsym(f, 5*8 + 2)
        hits = 0; ok = 0
        for j in range(NP):
            X = [[random.randint(-9, 9) for _ in range(9)] for _ in range(3)]
            r = plane_test(f, 9, S, p, X, 'nonic')
            if r is None or r[0] != 'ok': continue
            ok += 1; hits += (r[1] > 0)
        tot += 1
        if hits == 0: zero.append((str(f), ok))
        print(k, hits, '/', ok, '  ', str(f) if hits <= 1 else '', flush=True)
    print(f"kind {kind} p={p} M={M}: algebras {tot}, with 0 hits: {len(zero)}")
    for z in zero: print('ZERO', z)

if __name__ == '__main__':
    main()
