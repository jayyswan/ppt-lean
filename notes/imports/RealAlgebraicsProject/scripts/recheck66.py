# recheck66.py <logfile> <planes> <B> [maxalg]: rerun the ZERO algebras of a sweep log with more planes,
# plane entries uniform in [-B, B] (B = 364 is uniform mod 3^6).
import sys, random, ast, cypari
exec(open('loc66.py').read().split("\nif __name__ == '__main__'")[0])
log, NP, B = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
mx = int(sys.argv[4]) if len(sys.argv) > 4 else 99
Z = [ast.literal_eval(l[5:])[0] for l in open(log) if l.startswith('ZERO')][:mx]
random.seed(1)
for fs in Z:
    f = pari(fs); S = pari.polsym(f, 42); hits = ok = 0
    for j in range(NP):
        X = [[random.randint(-B, B) for _ in range(9)] for _ in range(3)]
        r = plane_test(f, 9, S, 3, X, 'nonic', prec=60)
        if r is None or r[0] != 'ok': continue
        ok += 1; hits += (r[1] > 0)
    print(hits, '/', ok, fs, flush=True)
