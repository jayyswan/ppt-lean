# Session 64: small toolkit for unramified etale algebras A = prod F_{p^f} (mod p) or prod Z_{p^f}/p^N (Hensel).
# An algebra is given by a list of monic integer polynomials g_j (irreducible mod p), coefficient lists low->high.
# Elements: list of coefficient lists (one per factor), integers mod M (M = p or p^N).
import random

def polmulmod(a, b, g, M):
    f = len(g) - 1
    r = [0] * (2 * f - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    for k in range(len(r) - 1, f - 1, -1):
        c = r[k] % M
        if c:
            for j in range(f):
                r[k - f + j] -= c * g[j]
        r[k] = 0
    return [x % M for x in r[:f]]

def powersums(g, M, kmax):
    # s_j = sum of j-th powers of the roots of monic g, j = 0..kmax (Newton), mod M
    f = len(g) - 1
    e = [1] + [((-1) ** k) * g[f - k] for k in range(1, f + 1)]   # elementary symmetric e_k
    s = [f % M]
    for k in range(1, kmax + 1):
        # standard Newton: s_k = sum_{i=1}^{k-1} (-1)^{i-1} e_i s_{k-i} + (-1)^{k-1} k e_k
        v = sum(((-1) ** (i - 1)) * (e[i] if i <= f else 0) * s[k - i] for i in range(1, k)) + ((-1) ** (k - 1)) * k * (e[k] if k <= f else 0)
        s.append(v % M)
    return s

class Alg:
    def __init__(self, gs, M):
        self.gs = gs; self.M = M
        self.dims = [len(g) - 1 for g in gs]
        self.n = sum(self.dims)
        self.ps = [powersums(g, M, len(g) - 1) for g in gs]   # traces of 1, x, ..., x^{f-1}
    def split(self, v):
        out, i = [], 0
        for f in self.dims:
            out.append(list(v[i:i + f])); i += f
        return out
    def join(self, parts):
        return [x for p in parts for x in p]
    def mul(self, a, b):
        return [polmulmod(x, y, g, self.M) for x, y, g in zip(a, b, self.gs)]
    def tr(self, a):
        return sum(c * s for x, ps in zip(a, self.ps) for c, s in zip(x, ps)) % self.M
    def F35(self, v):
        a = self.split(v)
        a2 = self.mul(a, a); a3 = self.mul(a2, a); a5 = self.mul(a3, a2)
        t = self.tr(a)
        return (self.tr(a3) - t ** 3) % self.M, (self.tr(a5) - t ** 5) % self.M
    def grad(self, v):
        # gradients of F3, F5 in the coordinates of v
        a = self.split(v); M = self.M
        a2 = self.mul(a, a); a4 = self.mul(a2, a2); t = self.tr(a)
        g3, g5 = [], []
        i = 0
        for j, f in enumerate(self.dims):
            for k in range(f):
                e = [[0] * d for d in self.dims]; e[j][k] = 1
                tb = self.tr(e)
                g3.append((3 * self.tr(self.mul(a2, e)) - 3 * t * t * tb) % M)
                g5.append((5 * self.tr(self.mul(a4, e)) - 5 * pow(t, 4, M) * tb) % M)
                i += 1
        return g3, g5

def irred_mod_p(f, p, rng):
    # random monic polynomial of degree f irreducible mod p (Ben-Or test via PARI)
    import cypari
    pari = cypari.pari
    while True:
        c = [rng.randrange(p) for _ in range(f)] + [1]
        P = pari('Pol(%s)' % str(c[::-1]))
        if f == 1 or pari('polisirreducible')(P * pari('Mod(1,%d)' % p)):
            return c
