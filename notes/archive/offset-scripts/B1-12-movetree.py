"""B1-12: 30-digit move-tree check.

For a random totally real rational septic q, solve the root-based covering system,
refine to 50 digits, then:

  (1) verify W = u^2(u'^2+v'^2) - Delta v'^2 equals q * g exactly (remainder < 1e-30);
  (2) realize x = u, y = -int v' (so y' = -v'), d = sqrt(Delta);
  (3) at a real root beta of q verify the genuine axis-crossing equation
      x(beta)*sqrt(x'^2+y'^2) = d*y'(beta)  to 30 digits, with the sign of d chosen
      so that it holds exactly.
"""
import numpy as np
import mpmath as mp
from scipy.optimize import root

mp.mp.dps = 60


def polydiv(num, den):
    """long division of coefficient lists (ascending); returns (q, r)."""
    num = [mp.mpf(c) for c in num]
    den = [mp.mpf(c) for c in den]
    while len(num) >= 1 and abs(num[-1]) < mp.mpf('1e-50'):
        num.pop()
    dd = len(den) - 1
    q = [mp.mpf(0)] * max(1, len(num) - dd)
    r = num[:]
    for i in range(len(num) - 1, dd - 1, -1):
        coef = r[i] / den[dd]
        q[i - dd] = coef
        for j in range(dd + 1):
            r[i - dd + j] -= coef * den[j]
    return q, r[:dd] if dd > 0 else [mp.mpf(0)]


def main():
    # totally real septic (perturbation of Chebyshev, rational)
    qc = [mp.mpf(v) for v in [1, 0, -7, 0, 14, 0, -7, 1]]
    rmp = mp.polyroots(qc, maxsteps=300, error=False)
    ri = [mp.mpf(x.real) for x in rmp]
    ri.sort()

    def F(x):
        a, b, c, p, qq, r, D = x
        return [ (ri[i]**3 + a*ri[i]**2 + b*ri[i] + c)**2
                 * ((3*ri[i]**2 + 2*a*ri[i] + b)**2 + (p*ri[i]**2 + qq*ri[i] + r)**2)
                 - D * (p*ri[i]**2 + qq*ri[i] + r)**2 for i in range(7)]

    def Jmat(x):
        a, b, c, p, qq, r, D = x
        M = mp.matrix(7, 7)
        for i in range(7):
            x0 = ri[i]
            u = x0**3 + a*x0**2 + b*x0 + c
            up = 3*x0**2 + 2*a*x0 + b
            vp = p*x0**2 + qq*x0 + r
            S = up**2 + vp**2
            M[i, 0] = 2*u*x0**2*S + u**2*2*up*(2*x0)
            M[i, 1] = 2*u*x0*S + u**2*2*up
            M[i, 2] = 2*u*S
            M[i, 3] = u**2*2*vp*x0**2 - D*2*vp*x0**2
            M[i, 4] = u**2*2*vp*x0 - D*2*vp*x0
            M[i, 5] = u**2*2*vp - D*2*vp
            M[i, 6] = -vp**2
        return M

    # seed from scipy
    Fnp = lambda x: np.array([float(v) for v in F(x)])
    Jnp = lambda x: np.array([[float(Jmat(x)[i, j]) for j in range(7)] for i in range(7)])
    rng = np.random.default_rng(3)
    seed = None
    for _ in range(500):
        x0 = rng.normal(size=7) * np.array([1., 2., 3., 1., 2., 3., 50.])
        res = root(Fnp, x0, jac=Jnp, method='hybr')
        if res.success and np.max(np.abs(Fnp(res.x))) < 1e-10 and res.x[6] > 0:
            seed = [mp.mpf(v) for v in res.x]
            break
    assert seed is not None, "no seed"
    # Newton refine
    x = seed
    for _ in range(80):
        Fv = mp.matrix(F(x))
        x = [x[i] - mp.lu_solve(Jmat(x), Fv)[i] for i in range(7)]
        if max(abs(Fv[i]) for i in range(7)) < mp.mpf('1e-50'):
            break
    a, b, c, p, qq, r, D = x
    print("solution (50 digits):")
    for nm, v in zip(['a','b','c','p','q','r','Delta'], x):
        print("   %-6s %s" % (nm, mp.nstr(v, 40)))

    # (1) W vs q*g
    u = [c, b, a, mp.mpf(1)]
    up = [b, 2*a, 3]
    vp = [r, qq, p]
    def mul(A, B):
        C = [mp.mpf(0)]*(len(A)+len(B)-1)
        for i, ai in enumerate(A):
            for j, bj in enumerate(B):
                C[i+j] += ai*bj
        return C
    S = [up[0]**2+vp[0]**2, 2*up[0]*up[1]+2*vp[0]*vp[1],
         up[1]**2+2*up[0]*up[2]+vp[1]**2+2*vp[0]*vp[2],
         2*up[1]*up[2]+2*vp[1]*vp[2], up[2]**2+vp[2]**2]
    W = mul(mul(u, u), S)
    vp2 = mul(vp, vp)
    for i in range(len(vp2)):
        W[i] -= D*vp2[i]
    # pad
    while len(W) < 11:
        W.append(mp.mpf(0))
    g, rem = polydiv(W, list(reversed(qc)))
    print("deg W =", len(W)-1, "  quotient g =", [mp.nstr(v, 20) for v in g])
    print("remainder W - q*g (should be ~0):", [mp.nstr(v, 6) for v in rem])
    resid = max(abs(v) for v in rem) if rem else mp.mpf(0)
    print("max |remainder| =", mp.nstr(resid, 6), "  (30-digit pass:", resid < mp.mpf('1e-30'), ")")

    # (3) axis crossing at beta = q's real root
    beta = ri[0]
    ub = beta**3 + a*beta**2 + b*beta + c
    upb = 3*beta**2 + 2*a*beta + b
    vpb = p*beta**2 + qq*beta + r
    ypb = -vpb
    w = mp.sqrt(upb**2 + vpb**2)
    lhs = ub*w
    rhs = -mp.sqrt(D)*vpb  # d=-s chosen
    print("beta =", mp.nstr(beta, 40))
    print("x(beta)*sqrt(x'^2+y'^2) =", mp.nstr(lhs, 40))
    print("d*y'(beta)              =", mp.nstr(rhs, 40))
    print("crossing agreement (<1e-30):", abs(lhs-rhs) < mp.mpf('1e-30'), " diff", mp.nstr(abs(lhs-rhs), 6))
    # q(beta)
    print("q(beta) =", mp.nstr(sum(qc[i]*beta**(7-i) for i in range(8)), 6))


if __name__ == '__main__':
    main()
