# Session 17: real lines on Q4 for r = 1, classified by the type of p2 restricted to the line.
# Real model of K (x) R for r = 1: R x C^4, conjugates (z0, z1, conj z1, ..., z4, conj z4).
# Checks Proposition S17.1: with a p2-adapted basis (orthonormal or null), the element m
# (n = a^2 + b^2, or m = ab) satisfies 9 Tr(m^2) = Tr(m)^2.
import numpy as np
from scipy.optimize import least_squares
rng = np.random.default_rng(17)
def conj(v):   # v in R^9 -> nine complex conjugates
    z = [v[0]+0j]
    for k in range(4):
        w = v[1+2*k] + 1j*v[2+2*k]; z += [w, np.conj(w)]
    return np.array(z)
def Tr(z): return np.sum(z).real
def tz(v):     # project to trace zero
    z = conj(v); return v - np.array([Tr(z)/9] + [0]*8) * 0 if False else v
# parametrise trace-zero vectors: v0 = -2*sum Re(z_k)
def vec(u):    # u in R^8 -> v in R^9 with trace zero
    return np.concatenate([[-2*(u[0]+u[2]+u[4]+u[6])], u])
def Q4(z): return 6*Tr(z**4) - Tr(z**2)**2
def resid(x):
    a, b = conj(vec(x[:8])), conj(vec(x[8:]))
    pts = [(1,0),(0,1),(1,1),(1,-1),(1,2)]
    r = [Q4(p*a+q*b) for p,q in pts]
    G = np.array([[x[:8]@x[:8], x[:8]@x[8:]],[x[:8]@x[8:], x[8:]@x[8:]]])
    return np.array(r + [G[0,0]-1, G[1,1]-1, G[0,1]])
types = {'definite':0, 'indefinite':0, 'degenerate':0}; checks = []
found = 0
for trial in range(300):
    sol = least_squares(resid, rng.normal(size=16), xtol=1e-15, ftol=1e-15, gtol=1e-15)
    if np.max(np.abs(sol.fun)) > 1e-10: continue
    found += 1
    a, b = conj(vec(sol.x[:8])), conj(vec(sol.x[8:]))
    g = np.array([[Tr(a*a), Tr(a*b)],[Tr(a*b), Tr(b*b)]])
    det = np.linalg.det(g); scale = np.max(np.abs(g))
    if abs(det) < 1e-8*scale**2: types['degenerate'] += 1; continue
    w, V = np.linalg.eigh(g)
    if det > 0:
        types['definite'] += 1
        A = (V[0,0]*a + V[1,0]*b)/np.sqrt(abs(w[0])); B = (V[0,1]*a + V[1,1]*b)/np.sqrt(abs(w[1]))
        m = A*A + B*B
    else:
        types['indefinite'] += 1
        A = (V[0,0]*a + V[1,0]*b)/np.sqrt(abs(w[0])); B = (V[0,1]*a + V[1,1]*b)/np.sqrt(abs(w[1]))
        a2, b2 = A + B, A - B          # null vectors
        m = a2*b2
    checks.append(abs(9*Tr(m*m) - Tr(m)**2)/max(1, Tr(m)**2))
print('real lines found', found, types)
print('max |9 Tr(m^2) - Tr(m)^2| / Tr(m)^2 :', max(checks) if checks else None)
