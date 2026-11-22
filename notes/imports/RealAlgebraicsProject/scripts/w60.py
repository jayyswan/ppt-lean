# Session 42: the 60-point incidence W ∩ Λ for 3-spaces Λ = <P, Π>, P ∈ X = {p1 = p3 = 0},
# Π an isotropic plane of Q_P(v) = Σ P_i v_i² on N_P = {Σ v = 0, Σ P² v = 0} (mod P).
# Then X ∩ Λ is the cone over the plane cubic {p3 = 0} ⊂ Π with vertex P (T3 structure),
# and W ∩ Λ = {p3(w) = 0, Q4(sP + w) = 0, p5(sP + w) = 0}: Bezout 3·4·5 = 60.
# Module: sampling of P (generic / in L_135 / in Y4), spinor chart of isotropic planes,
# total-degree homotopy, parameter homotopy, monodromy loops.
import numpy as np
rng = np.random.default_rng(0)
n = 9
ONE = np.ones(n)

def ps(z, k): return np.sum(z**k)
def Q4(z): return 6*ps(z, 4) - ps(z, 2)**2

def tz_basis():
    M = np.eye(n) - ONE[:, None]*ONE[None, :]/n
    u, s, vt = np.linalg.svd(M); return u[:, :n-1]
TZ = tz_basis()

def real_X_point(seed):
    r = np.random.default_rng(seed)
    while True:
        a, b = TZ @ r.normal(size=n-1), TZ @ r.normal(size=n-1)
        # p3(a + t b) = 0 : cubic in t
        c = [ps(b**3, 1), 3*np.sum(a*b*b), 3*np.sum(a*a*b), ps(a**3, 1)]
        for t in np.roots(c):
            if abs(t.imag) < 1e-12:
                z = a + t.real*b; return z/np.linalg.norm(z)

def newton_real(z, fs, iters=60):
    """Real Newton (least-norm) for a list of functions on the trace-zero space."""
    for _ in range(iters):
        F = np.array([f(z) for f in fs])
        if np.max(abs(F)) < 1e-14: break
        J = np.array([num_grad(f, z) for f in fs]) @ TZ
        dz = TZ @ np.linalg.lstsq(J, -F, rcond=None)[0]
        z = z + dz; z /= np.linalg.norm(z)
    return z

def num_grad(f, z, h=1e-7):
    g = np.zeros(n)
    for i in range(n):
        e = np.zeros(n); e[i] = h; g[i] = (f(z+e) - f(z-e))/(2*h)
    return g

def NP_basis(P):
    C = np.vstack([ONE, P**2, P])           # Σv = 0, ΣP²v = 0, complement of P
    u, s, vt = np.linalg.svd(C)
    return vt[3:].T                          # 9 x 6

def QP_matrix(P, B):
    return B.T @ np.diag(P) @ B

def spinor_frame(P):
    """Return (B, T): v = B @ T @ y, with Q_P = Σ_{k<3} u_k w_k in y = (u, w)-coordinates."""
    B = NP_basis(P); M = QP_matrix(P, B)
    d, U = np.linalg.eigh(M)
    S = U @ np.diag(1/np.sqrt(d.astype(complex)))   # Q = Σ y_j²
    # y_j = (u_j + w_j)/2, y_{j+3} = (u_j - w_j)/(2i)  =>  y_j² + y_{j+3}² = u_j w_j
    T = np.zeros((6, 6), complex)
    for j in range(3):
        T[j, j] = .5; T[j, 3+j] = .5
        T[j+3, j] = 1/(2j); T[j+3, 3+j] = -1/(2j)
    return B @ S @ T, np.sign(d)

def plane(Fr, A3):
    a, b, c = A3
    A = np.array([[0, a, b], [-a, 0, c], [-b, -c, 0]])
    Y = np.vstack([np.eye(3), A])           # columns: u = e_k, w = A e_k
    return Fr @ Y                            # 9 x 3 complex

class System:
    def __init__(s, P, chart):
        s.P = P.astype(complex); s.c = chart
    def setV(s, V): s.V = V; s.M = np.hstack([s.P[:, None], V])   # z = M @ X, X ∈ C^4
    def F(s, X):
        z = s.M @ X; p2, p3, p4, p5 = (np.sum(z**k) for k in (2, 3, 4, 5))
        return np.array([p3, 6*p4 - p2*p2, p5, s.c @ X - 1])
    def J(s, X):
        z = s.M @ X; p2 = np.sum(z*z)
        g2, g3, g4, g5 = (k*z**(k-1) for k in (2, 3, 4, 5))
        return np.vstack([g3 @ s.M, (6*g4 - 2*p2*g2) @ s.M, g5 @ s.M, s.c])

def newton(sys, X, tol=1e-12, it=8):
    for _ in range(it):
        dX = np.linalg.solve(sys.J(X), -sys.F(X)); X = X + dX
        if np.linalg.norm(dX) < tol*max(1, np.linalg.norm(X)): return X, True
    return X, np.linalg.norm(sys.F(X)) < 1e-9

def total_degree(sys, gamma=None):
    """Solve sys (with V set) by a total-degree homotopy from x_i^{d_i} = x_0^{d_i}."""
    if gamma is None: gamma = np.exp(2j*np.pi*rng.random())
    deg = (3, 4, 5); c = sys.c
    def G(X): return np.array([X[i+1]**deg[i] - X[0]**deg[i] for i in range(3)] + [c @ X - 1])
    def GJ(X):
        Jm = np.zeros((4, 4), complex)
        for i in range(3):
            Jm[i, i+1] = deg[i]*X[i+1]**(deg[i]-1); Jm[i, 0] = -deg[i]*X[0]**(deg[i]-1)
        Jm[3] = c; return Jm
    starts = []
    for k0 in range(3):
        for k1 in range(4):
            for k2 in range(5):
                Y = np.array([1, np.exp(2j*np.pi*k0/3), np.exp(2j*np.pi*k1/4), np.exp(2j*np.pi*k2/5)])
                starts.append(Y/(c @ Y))
    sols = []
    for X in starts:
        H = lambda X, t: (1-t)*gamma*G(X) + t*sys.F(X)
        HJ = lambda X, t: (1-t)*gamma*GJ(X) + t*sys.J(X)
        X, ok = track(H, HJ, X, 0.0, 1.0)
        if ok:
            X, ok = newton(sys, X)
            if ok: sols.append(X)
    return sols

def track(H, HJ, X, t0, t1, h=0.01, hmin=1e-9, hmax=0.02):
    t = t0
    while t < t1 - 1e-15:
        h = min(h, t1 - t)
        # Euler predictor with dH/dt by finite difference
        dt = 1e-7
        Ht = (H(X, t+dt) - H(X, t))/dt
        Jm = HJ(X, t)
        try: dX = np.linalg.solve(Jm, -Ht)
        except np.linalg.LinAlgError: return X, False
        Xp = X + h*dX; tn = t + h; ok = False
        nd = []
        for _ in range(5):
            try: d = np.linalg.solve(HJ(Xp, tn), -H(Xp, tn))
            except np.linalg.LinAlgError: break
            Xp = Xp + d; nd.append(np.linalg.norm(d))
            if len(nd) >= 2 and nd[-1] > 0.5*nd[-2] and nd[-1] > 1e-10: break
            if nd[-1] < 1e-10*max(1, np.linalg.norm(Xp)): ok = True; break
        if ok and nd[0] < 0.05*max(1, np.linalg.norm(X)):
            X, t = Xp, tn; h = min(1.4*h, hmax)
        else:
            h /= 2
            if h < hmin: return X, False
    return X, True

def param_track(sys, Va, Vb, X, gamma_path=None):
    """Track X from V = Va to V = Vb along V(t) = (1-t)Va + t Vb."""
    def H(X, t): sys.setV((1-t)*Va + t*Vb); return sys.F(X)
    def HJ(X, t): sys.setV((1-t)*Va + t*Vb); return sys.J(X)
    X, ok = track(H, HJ, X, 0.0, 1.0)
    sys.setV(Vb)
    if ok: X, ok = newton(sys, X)
    return X, ok

def match(sols, X):
    d = [np.linalg.norm(S - X) for S in sols]
    i = int(np.argmin(d)); return i, d[i]
