# loc66.py -- exact p-adic plane sections of V_A for A = L x Q_p (nonic type) or A = L (decic type).
# L = Q_p[x]/(f), f monic integral (e.g. Eisenstein at p).  V_A = {Tr y = Tr y^3 = Tr y^5 = 0} in P(A).
# Nonic type: y = (x, -Tr x), x in L (deg 9):  F3 = Tr x^3 - (Tr x)^3, F5 = Tr x^5 - (Tr x)^5.
# Decic type (deg f = 10): y = x with Tr x = 0 imposed by the plane.
# A random integer plane x = X0 + s X1 + t X2 meets V_A in deg = 15 points.  If the resultant R(t)
# (degree 15) is squarefree, every simple Q_p-root of R gives a SMOOTH Q_p-point of V_A
# (intersection multiplicity 1 at each of 15 distinct points).  Certified, exact.
# usage: python3 loc66.py "<f>" <p> <nplanes> <seed> [bound] [mode]   mode: nonic|decic
import sys, random, cypari
pari = cypari.pari
pari.allocatemem(10**9)

def setup(fstr, p):
    f = pari(fstr)
    n = int(pari.poldegree(f))
    S = pari.polsym(f, 5*(n-1) + 2)   # S[k] = Tr(pi^k), k = 0..
    return f, n, S

def trace(g, n, S):
    # g: polynomial in x (pi) with coeffs in y,z, reduced mod f
    return sum(pari.polcoef(g, i, 'x') * S[i] for i in range(n))

def tz(X, S, n):
    # move an integer vector into the trace-zero hyperplane: c' = n c - (sum c_i S_i) e_0
    t = sum(X[i]*int(S[i]) for i in range(n))
    return [n*X[0] - t] + [n*X[i] for i in range(1, n)]

def plane_test(f, n, S, p, X, mode, prec=40):
    X0, X1, X2 = X
    elt = sum((X0[i] + pari('y')*X1[i] + pari('z')*X2[i]) * pari('x')**i for i in range(n))
    T1 = trace(elt % f, n, S)
    e2 = (elt*elt) % f
    e3 = (e2*elt) % f
    e5 = (e3*e2) % f
    T3 = trace(e3, n, S); T5 = trace(e5, n, S)
    if mode == 'nonic':
        F3 = T3 - T1**3; F5 = T5 - T1**5; eqs = [F3, F5]
        R = pari.polresultant(F3, F5, 'y')
        degexp = 15
    else:
        # decic / general type: A = Q_p[x]/(f), deg f = n; the plane is chosen inside {Tr x = 0} by the caller
        assert T1 == 0, 'plane not in trace-zero hyperplane'
        F3 = T3; F5 = T5
        R = pari.polresultant(F3, F5, 'y')
        degexp = 15
    if pari.poldegree(F3, 'y') != 3 or pari.poldegree(F5, 'y') != 5: return ('lc', 0)   # leading y-coefficients are nonzero constants
    R = pari.content(R)**-1 * R if R != 0 else R
    if R == 0 or pari.poldegree(R, 'z') != degexp: return ('deg', int(pari.poldegree(R,'z')) if R!=0 else -1)
    if pari.poldegree(pari.gcd(R, pari.deriv(R,'z')),'z') > 0: return ('nsf', 0)
    rts = pari.polrootspadic(R, p, prec)
    return ('ok', len(rts))

def main():
    fstr = sys.argv[1]; p = int(sys.argv[2]); N = int(sys.argv[3]); seed = int(sys.argv[4])
    B = int(sys.argv[5]) if len(sys.argv) > 5 else 9
    mode = sys.argv[6] if len(sys.argv) > 6 else 'nonic'
    random.seed(seed)
    f, n, S = setup(fstr, p)
    hits = 0; tried = 0; bad = 0
    for k in range(N):
        X = [[random.randint(-B, B) for _ in range(n)] for _ in range(3)]
        r = plane_test(f, n, S, p, X, mode)
        if r is None or r[0] != 'ok': bad += 1; continue
        tried += 1
        if r[1] > 0:
            hits += 1
    print(f"f={fstr} p={p}: planes {tried} (bad {bad}), planes with a smooth Q_{p}-point: {hits}")

if __name__ == '__main__':
    main()
