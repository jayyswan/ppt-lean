# recheck5.py <logfile> <planes> <B> <p> [kindfilter]: rerun ZERO degree-10 algebras of a sweep5 log (decic mode),
# plane entries uniform in [-B, B], inside {Tr = 0}.
import sys, random, ast, cypari
exec(open('loc66.py').read().split("\nif __name__ == '__main__'")[0])
log, NP, B, p = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
Z = [ast.literal_eval(l[5:])[0] for l in open(log) if l.startswith('ZERO')]
random.seed(int(sys.argv[5]) if len(sys.argv) > 5 else 2)
for fs in Z:
    f = pari(fs); n = 10; S = pari.polsym(f, 47); hits = ok = 0
    for j in range(NP):
        X = [tz([random.randint(-B, B) for _ in range(n)], S, n) for _ in range(3)]
        r = plane_test(f, n, S, p, X, 'decic', prec=60)
        if r is None or r[0] != 'ok': continue
        ok += 1; hits += (r[1] > 0)
        if hits >= 3: break
    print(hits, '/', ok, fs, flush=True)
