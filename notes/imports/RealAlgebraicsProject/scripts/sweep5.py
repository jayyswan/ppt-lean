# sweep5.py -- general degree-10 local algebras A = Q_p[x]/(f) (decic type; a nonic algebra K_v is A = K_v x Q_p,
# f = g*(x - c)), certified p-adic plane sections inside {Tr = 0} (loc66.plane_test, mode 'decic').
# kind = comma list of factors: E<d> Eisenstein, U<d> unramified, K<e> x^e - p*u, Q a linear factor (distinct).
# usage: python3 sweep5.py <kind> <count> <planes> <seed> <p> [M]
# kinds: L5U3Q (Eis5 x unram3 x Q_p x Q_p? no: nonic L5 x U3 x Q_p, plus the 10th factor Q_p) ,
#        L5L3Q (Eis5 x (x^3 - p*u) x Q_p x Q_p), L5L5 (two Eisenstein quintics), L5U5, E10 (Eisenstein degree 10),
#        L9Q (Eisenstein 9 x Q_p, the nonic type, as a cross-check of loc66 nonic mode)
import sys, random, cypari
exec(open('sweep66.py').read().split("\ndef main")[0])
pari = cypari.pari
def lin(c): return pari('x') - c
def main():
    kind = sys.argv[1]; cnt = int(sys.argv[2]); NP = int(sys.argv[3]); seed = int(sys.argv[4]); p = int(sys.argv[5])
    M = int(sys.argv[6]) if len(sys.argv) > 6 else p
    rng = random.Random(seed); random.seed(seed); zero = []; tot = 0
    for k in range(cnt):
        f = pari(1); lc = 0
        for part in kind.split(','):
            if part == 'Q': lc += 1; f = f*lin(lc)
            elif part[0] == 'E': f = f*eis(int(part[1:]), p, M, rng)
            elif part[0] == 'U': f = f*unram(int(part[1:]), p, rng)
            elif part[0] == 'K': f = f*(pari('x')**int(part[1:]) - p*(1 + p*rng.randrange(0, M)))   # Kummer-type x^e - p*u
            else: raise SystemExit('kind?')
        assert pari.poldegree(f) == 10, kind
        if pari.poldegree(pari.gcd(f, pari.deriv(f))) > 0: continue
        n = 10; S = pari.polsym(f, 5*(n-1) + 2); hits = ok = 0
        for j in range(NP):
            X = [tz([random.randint(-9, 9) for _ in range(n)], S, n) for _ in range(3)]
            r = plane_test(f, n, S, p, X, 'decic')
            if r is None or r[0] != 'ok': continue
            ok += 1; hits += (r[1] > 0)
        tot += 1
        if hits == 0: zero.append((str(f), ok))
        print(k, hits, '/', ok, flush=True)
    print(f"kind {kind} p={p} M={M}: algebras {tot}, with 0 hits: {len(zero)}")
    for z in zero: print('ZERO', z)
if __name__ == '__main__':
    main()
