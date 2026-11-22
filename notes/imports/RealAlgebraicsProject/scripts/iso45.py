# Session 45: trace-form isotropy checks in K (x) R = R^r x C^s.
# Usage:
#   python3 iso45.py lines <r> <ks> <starts> <seed>   real lines Q+kv with p_k == 0 for k in ks (e.g. 1,2,4)
#   python3 iso45.py conics <r> <ks> <starts> <seed>  real conics A+Bk+Ck^2 with p_k == 0 for k in ks (e.g. 1,2,3)
# For each solution prints: residual, degeneracy data (number of distinct ratio classes of the
# coordinate forms), the rank data of the product spaces, and the real-root count of p4 (lines/conics).
import sys, numpy as np
from numpy.polynomial import polynomial as Pn
from scipy.optimize import least_squares

def cplx(y, r):
    s = (9 - r)//2
    z = np.empty(r + s, complex)
    z[:r] = y[:r]
    z[r:] = y[r::2][:s] + 1j*y[r+1::2][:s]
    return z

def coord_polys(Ys, r):
    # Ys: list of real 9-vectors (coefficients of k^0, k^1, ...); returns (r+s) x deg+1 complex coefficient arrays
    return np.array([cplx(Y, r) for Y in Ys]).T  # shape (r+s, d+1)

def psum_poly(C, r, k):
    # power sum p_k along the curve; C: (r+s, d+1) coefficient arrays in kappa
    tot = np.zeros((C.shape[1]-1)*k + 1)
    for i, c in enumerate(C):
        pk = np.array([1.0+0j])
        for _ in range(k):
            pk = Pn.polymul(pk, c)
        w = 1.0 if i < r else 2.0
        tot = tot + w*np.real(pk) if i < r else tot + 2*np.real(pk)
    return tot

def resid(x, r, d, ks, G, g):
    Ys = x.reshape(d+1, 9)
    C = coord_polys(Ys, r)
    out = []
    for k in ks:
        out.extend(psum_poly(C, r, k))
    out.extend(G @ x - g)
    return np.array(out)

def nclasses(C, tol=1e-6):
    # number of distinct points of P^d-forms up to scalar among the coordinate forms (complex)
    vs = []
    for c in C:
        n = c/np.linalg.norm(c)
        n = n/ (n[np.argmax(abs(n))]/abs(n[np.argmax(abs(n))]))
        vs.append(n)
    cls = []
    for v in vs:
        if not any(min(np.linalg.norm(v - u*np.exp(0j)), 10) < tol or abs(abs(np.vdot(u, v)) - 1) < tol for u in cls):
            cls.append(v)
    return len(cls)

def realvec(z, r):
    s = len(z) - r
    y = np.empty(9)
    y[:r] = np.real(z[:r])
    y[r::2][:s] = np.real(z[r:]); y[r+1::2][:s] = np.imag(z[r:])
    return y

def main():
    mode, r, ks, starts, seed = sys.argv[1], int(sys.argv[2]), [int(t) for t in sys.argv[3].split(',')], int(sys.argv[4]), int(sys.argv[5])
    d = 1 if mode == 'lines' else 2
    rng = np.random.default_rng(seed)
    n = 9*(d+1)
    ngauge = 4 if d == 1 else 6   # lines: GL2 (4); conics: scale+PGL2 (4) + 2 slack rows for a random slice
    sols = []
    for st in range(starts):
        G = rng.standard_normal((ngauge, n)); g = rng.standard_normal(ngauge)
        x0 = rng.standard_normal(n)
        res = least_squares(resid, x0, args=(r, d, ks, G, g), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        f = np.linalg.norm(res.fun)
        if not np.isfinite(f) or f > 1e-10:
            continue
        Ys = res.x.reshape(d+1, 9)
        if np.linalg.svd(Ys, compute_uv=False)[-1] < 1e-6:
            continue
        C = coord_polys(Ys, r)
        ncl = nclasses(C)
        # product space data for lines: span of Q^2, Qv, v^2 in A (real 9-vectors)
        if d == 1:
            zQ, zv = C[:, 0], C[:, 1]
            M = np.array([realvec(zQ*zQ, r), realvec(zQ*zv, r), realvec(zv*zv, r)])
            sv = np.linalg.svd(M, compute_uv=False); sv = sv/sv[0]
        else:
            sv = np.linalg.svd(Ys, compute_uv=False); sv = sv/sv[0]
        p4 = psum_poly(C, r, 4)
        rts = np.roots(p4[::-1]) if np.max(abs(p4)) > 1e-12 else np.array([])
        nreal = int(np.sum(abs(np.imag(rts)) < 1e-7*np.maximum(1, abs(rts))))
        # minimum of p4/|y|^4 along the real curve on a kappa grid (projective: use kappa = tan t)
        ts = np.linspace(-np.pi/2, np.pi/2, 2001)[1:-1]
        best = np.inf
        for t in ts:
            c, s_ = np.cos(t), np.sin(t)
            y = sum(Ys[j]*c**(d-j)*s_**j for j in range(d+1))
            z = cplx(y, r)
            val = np.sum(np.real(z[:r]**4)) + 2*np.sum(np.real(z[r:]**4))
            best = min(best, val/np.dot(y, y)**2)
        sols.append((f, ncl, sv, nreal, best))
        print(f"start {st}: res {f:.1e} classes {ncl} sv {np.array2string(sv, precision=3)} p4 real roots {nreal} min p4/|y|^4 {best:.4f}", flush=True)
    print(f"{len(sols)} solutions of {starts}")

if __name__ == '__main__':
    main()
