# Session 13: symmetric invariants on V (trace-zero, dim 8) vanishing to order >= 4
# along Pi = (a,a,a,a,b,b,b,b,-4(a+b)); value of the normal quartic at the
# order-4 eigenvectors u = (1,i,-1,-i) on one 4-set.
# Arithmetic mod a prime p = 1 mod 4 (so i exists).  Ranks are mod p at random points.
import random, sys
p = 1000000009  # p % 4 == 1
I = pow(11, (p - 1) // 4, p)
assert I * I % p == p - 1
R = 5  # keep t-series up to t^4

def parts(d, mx=9, mn=2):
    if d == 0:
        yield ()
        return
    for k in range(min(d, mx), mn - 1, -1):
        for rest in parts(d - k, k, mn):
            yield (k,) + rest

def mul(A, B):
    C = [0] * R
    for i, x in enumerate(A):
        if x:
            for j in range(R - i):
                C[i + j] = (C[i + j] + x * B[j]) % p
    return C

def psums(x, n):
    # series in t of p_k(x + t n), k = 0..9
    out = {}
    from math import comb
    for k in range(2, 10):
        s = [0] * R
        for xi, ni in zip(x, n):
            for j in range(min(k, R - 1) + 1):
                s[j] = (s[j] + comb(k, j) * pow(xi, k - j, p) * pow(ni, j, p)) % p
        out[k] = s
    return out

def evalbasis(basis, ps):
    rows = []
    for lam in basis:
        s = [1] + [0] * (R - 1)
        for k in lam:
            s = mul(s, ps[k])
        rows.append(s)
    return rows  # rows[j][order]

def pipt(a, b):
    return [a] * 4 + [b] * 4 + [(-4 * (a + b)) % p]

def rnormal():
    u = [random.randrange(p) for _ in range(3)]; u.append((-sum(u)) % p)
    w = [random.randrange(p) for _ in range(3)]; w.append((-sum(w)) % p)
    return u + w + [0]

def nullspace(M, ncols):
    M = [r[:] for r in M]
    piv = []
    r = 0
    for c in range(ncols):
        pr = next((i for i in range(r, len(M)) if M[i][c]), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [v * inv % p for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(vi - f * vr) % p for vi, vr in zip(M[i], M[r])]
        piv.append(c); r += 1
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [0] * ncols; v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-M[i][fc]) % p
        basis.append(v)
    return basis

def run(d, order=4, samples=None):
    basis = list(parts(d))
    nb = len(basis)
    rows = []
    for _ in range(samples or 3 * nb + 10):
        a, b = random.randrange(p), random.randrange(p)
        ps = psums(pipt(a, b), rnormal())
        ev = evalbasis(basis, ps)
        for o in range(order):
            rows.append([ev[j][o] for j in range(nb)])
    ns = nullspace(rows, nb)
    return basis, ns

def quartic_at_u(basis, v, a, b, which=0, w=None):
    u = [1, I, p - 1, p - I]
    n = (u + [0] * 4 if which == 0 else [0] * 4 + u) + [0]
    if w is not None:
        n = w
    ps = psums(pipt(a, b), n)
    ev = evalbasis(basis, ps)
    return [sum(v[j] * ev[j][o] for j in range(len(basis))) % p for o in range(R)], ev

if __name__ == "__main__":
    for d in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        basis, ns2 = run(d, 2)
        basis, ns = run(d, 4)
        a, b = random.randrange(p), random.randrange(p)
        good = 0
        for v in ns:
            for which in (0, 1):
                val, _ = quartic_at_u(basis, v, a, b, which)
                assert val[:4] == [0] * 4
                if val[4]:
                    good += 1
        print(f"d={d}: dim={len(basis)}, ord>=2: {len(ns2)}, ord>=4: {len(ns)}, nonzero quartic at u (count over basis x two 4-sets): {good}", flush=True)
