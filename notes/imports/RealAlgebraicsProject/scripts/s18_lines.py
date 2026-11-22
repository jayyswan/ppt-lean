# Session 18: dimensions of line families over C (geometry is the same for every K; coordinates = the 9 conjugates).
# F(Q4): lines on Q4; F(D): lines on D = Q4 ∩ Q5; Sigma: lines whose square-span span(a^2, ab, b^2) is totally R-isotropic.
# Local dimension at a found line = 16 - rank(J) - 4 (GL2 acting on the basis a, b).
import numpy as np, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 18)
def vec(u): return np.concatenate([[-u.sum()], u])          # trace-zero vector in C^9
def P(z, k): return np.sum(z**k)
def Q4(z): return 6*P(z,4) - P(z,2)**2
def Q5(z): return 18*P(z,5) - 5*P(z,2)*P(z,3)
def Rb(u, w): return 6*np.sum(u*w) - np.sum(u)*np.sum(w)    # polar form of R(w) = 6 Tr(w^2) - Tr(w)^2
def coeffs(f, deg, a, b):                                    # coefficients of f(a + t b) via interpolation
    ts = np.exp(2j*np.pi*np.arange(deg+1)/(deg+1))
    vals = np.array([f(a + t*b) for t in ts])
    return np.fft.fft(vals)/(deg+1)
def eqs(x, kind):
    a, b = vec(x[:8]), vec(x[8:])
    if kind == 'Q4': return coeffs(Q4, 4, a, b)
    if kind == 'D':  return np.concatenate([coeffs(Q4, 4, a, b), coeffs(Q5, 5, a, b)])
    if kind == 'Sigma':
        A, X, Y = a*a, a*b, b*b
        return np.array([Rb(A,A), Rb(A,X), Rb(A,Y), Rb(X,X), Rb(X,Y), Rb(Y,Y)])
def jac(f, x, h=1e-7):
    f0 = f(x); J = np.zeros((len(f0), len(x)), complex)
    for j in range(len(x)):
        e = np.zeros(len(x), complex); e[j] = h; J[:, j] = (f(x+e) - f0)/h
    return J
def solve(kind, nslice):
    # gauge: a = (1,0,*), b = (0,1,*) in u-coordinates; plus nslice random affine-linear slices
    L = rng.normal(size=(nslice, 12)) + 1j*rng.normal(size=(nslice, 12)); c = rng.normal(size=nslice) + 1j*rng.normal(size=nslice)
    def full(y): return np.concatenate([[1, 0], y[:6], [0, 1], y[6:]])
    def F(y): return np.concatenate([eqs(full(y), kind), L@y - c])
    y = rng.normal(size=12) + 1j*rng.normal(size=12)
    for it in range(200):
        f = F(y); 
        if np.linalg.norm(f) < 1e-11: break
        J = jac(F, y); dy = np.linalg.lstsq(J, -f, rcond=None)[0]; y = y + dy
        if np.linalg.norm(y) > 1e6: return None
    return full(y) if np.linalg.norm(F(y)) < 1e-10 else None
for kind, nslice in [('Q4', 7), ('Sigma', 6), ('D', 1)]:
    dims = []
    for trial in range(40):
        x = solve(kind, nslice)
        if x is None: continue
        J = jac(lambda z: eqs(z, kind), x)
        s = np.linalg.svd(J, compute_uv=False); rank = int(np.sum(s > 1e-6*s[0]))
        dims.append(16 - rank - 4)
        if len(dims) >= 5: break
    print(kind, 'local dimensions at found lines:', dims)
