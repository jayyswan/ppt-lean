# Session 20 core: lines on D as nine-point configurations, deflated system, invariants, adaptive tracker.
import numpy as np

def vec(u): return np.concatenate([[-u.sum()], u])
def P_(z, k): return np.sum(z**k)
def Q4(z): return 6*P_(z, 4) - P_(z, 2)**2
def Q5(z): return 18*P_(z, 5) - 5*P_(z, 2)*P_(z, 3)
_ts = {d: np.exp(2j*np.pi*np.arange(d+1)/(d+1)) for d in (4, 5)}
def coeffs(f, deg, a, b):
    v = np.array([f(a + t*b) for t in _ts[deg]]); return np.fft.fft(v)/(deg+1)
def eqs(x):
    a, b = vec(x[:8]), vec(x[8:]); return np.concatenate([coeffs(Q4, 4, a, b), coeffs(Q5, 5, a, b)])
def full(y): return np.concatenate([[1, 0], y[:6], [0, 1], y[6:]])
def ab(Y): x = full(Y[:12]); return vec(x[:8]), vec(x[8:])
def M9(a, b): return np.array([[1, a[i], b[i], a[i]**2, a[i]*b[i], b[i]**2, a[i]**3, a[i]**2*b[i], a[i]*b[i]**2, b[i]**3] for i in range(9)])
R = np.random.default_rng(3).normal(size=(2, 10))
def G(Y):
    y, v1, v2 = Y[:12], Y[12:22], Y[22:32]; x = full(y); a, b = vec(x[:8]), vec(x[8:]); M = M9(a, b)
    return np.concatenate([eqs(x), M@v1, M@v2, [R[0]@v1-1, R[1]@v1, R[0]@v2, R[1]@v2-1]])
def moments(a, b):
    P = np.stack([a, b], 1); Q = P.T@P; T = np.einsum('ni,nj,nk->ijk', P, P, P); return P, Q, T
def invs(a, b):
    P, Q, T = moments(a, b); Qi = np.linalg.inv(Q)
    J2 = np.einsum('ijk,lmn,il,jm,kn->', T, T, Qi, Qi, Qi)
    A, B_, C, D = T[0, 0, 0], 3*T[0, 0, 1], 3*T[0, 1, 1], T[1, 1, 1]
    disc = B_**2*C**2 - 4*A*C**3 - 4*B_**3*D - 27*A**2*D**2 + 18*A*B_*C*D
    return np.array([disc/np.linalg.det(Q)**3, J2])
def H(Y, c): a, b = ab(Y); return np.concatenate([G(Y), invs(a, b) - c])
def jacY(F, Y, h=1e-6):
    f0 = F(Y); J = np.zeros((len(f0), len(Y)), complex)
    for j in range(len(Y)):
        e = np.zeros(len(Y), complex); e[j] = h; J[:, j] = (F(Y+e) - F(Y-e))/(2*h)
    return J
def gram(Y):
    a, b = ab(Y); P, Q, T = moments(a, b); return P@np.linalg.inv(Q)@P.T
def sheets(Y): return np.diag(gram(Y))

def newton(Y, c, it=8, tol=1e-12):
    for k in range(it):
        f = H(Y, c); r = np.linalg.norm(f)
        if r < tol: return Y, r
        Y = Y + np.linalg.lstsq(jacY(lambda v: H(v, c), Y), -f, rcond=None)[0]
    return Y, np.linalg.norm(H(Y, c))

def tangent(Y, c, dc):
    JY = jacY(lambda v: H(v, c), Y); f = H(Y, c)
    # dH/dc = -[0..0, I2]
    rhs = np.zeros(len(f), complex); rhs[-2:] = dc
    return np.linalg.lstsq(JY, rhs, rcond=None)[0]

def track(Y, path, h0=0.05, hmin=1e-6, tol=1e-10):
    """Track Y along a piecewise-linear path of c-values (list). Adaptive Euler-Newton. Returns Y or None."""
    for p, q in zip(path[:-1], path[1:]):
        s, h = 0.0, h0
        while s < 1 - 1e-14:
            h = min(h, 1 - s); c1 = p + (q - p)*(s + h)
            dY = tangent(Y, p + (q-p)*s, (q - p)*h)
            Yp, r = newton(Y + dY, c1, it=4)
            # accept if converged and the correction was small relative to the step
            if r < tol and np.linalg.norm(Yp - Y - dY) < 0.1*max(np.linalg.norm(dY), 1e-8) + 1e-9:
                Y, s = Yp, s + h; h = min(2*h, 0.2)
            else:
                h /= 2
                if h < hmin: return None
    return Y

def deflated_start(row):
    a, b = row[:9], row[9:]
    g = np.linalg.inv(np.array([[a[1], b[1]], [a[2], b[2]]]).T); a2, b2 = g@np.stack([a, b])
    N = np.linalg.svd(M9(a2, b2))[2][-2:].T.conj(); V = N@np.linalg.solve(R@N, np.eye(2))
    Y0 = np.concatenate([a2[3:9], b2[3:9], V[:, 0], V[:, 1]])
    return newton(Y0, invs(a2, b2), it=12)[0]

# --- line finder (from session 19 lines.py) ---
def find_lines(seed, starts):
    rng = np.random.default_rng(seed); out = []
    def jac(F, y, h=1e-7):
        f0 = F(y); J = np.zeros((len(f0), len(y)), complex)
        for j in range(len(y)):
            e = np.zeros(len(y), complex); e[j] = h; J[:, j] = (F(y+e) - f0)/h
        return J
    for t in range(starts):
        L = rng.normal(size=(2, 12)) + 1j*rng.normal(size=(2, 12)); cc = rng.normal(size=2) + 1j*rng.normal(size=2)
        F = lambda y: np.concatenate([eqs(full(y)), L@y - cc])
        y = rng.normal(size=12) + 1j*rng.normal(size=12); ok = True
        for it in range(100):
            f = F(y)
            if np.linalg.norm(f) < 1e-12: break
            y = y + np.linalg.lstsq(jac(F, y), -f, rcond=None)[0]
            if np.linalg.norm(y) > 1e6: ok = False; break
        if not ok or np.linalg.norm(F(y)) > 1e-10: continue
        x = full(y); a, b = vec(x[:8]), vec(x[8:])
        if min(abs(a[i]-a[j]) + abs(b[i]-b[j]) for i in range(9) for j in range(i+1, 9)) < 1e-6: continue
        out.append(np.concatenate([a, b]))
    return np.array(out)
