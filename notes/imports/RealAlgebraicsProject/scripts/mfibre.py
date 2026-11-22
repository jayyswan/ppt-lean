# Session 17: fibre of the map  line -> m = ab  (indefinite null basis a, b), over C.
# Split coordinates K (x) C = C^9.  Given m with 9 sum m^2 = (sum m)^2, solve for a in P^8:
#  sum a = 0, sum m/a = 0, sum a^2 = 0, sum (m/a)^2 = 0, sum a^4 = 0, sum (m/a)^4 = 0,
#  sum m a^2 = 0, sum m^3/a^2 = 0      (b = m/a).
# Step 1: build a line on Q4 numerically (complex), take its m; Step 2: Newton from random starts.
import numpy as np, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
def F(a, m, h):
    b = m / a
    return np.array([a.sum(), b.sum(), (a*a).sum(), (b*b).sum(), (a**4).sum(), (b**4).sum(),
                     (m*a*a).sum(), (m**3/a**2).sum(), h @ a - 1])
def J(a, m, h):
    b = m / a; db = -m / a**2
    rows = [np.ones(9), db, 2*a, 2*b*db, 4*a**3, 4*b**3*db, 2*m*a, -2*m**3/a**3, h]
    return np.array(rows)
def newton(a, m, h, it=60):
    for _ in range(it):
        f = F(a, m, h)
        if not np.all(np.isfinite(f)): return None
        try: d = np.linalg.lstsq(J(a, m, h), -f, rcond=None)[0]
        except np.linalg.LinAlgError: return None
        a = a + d
        if np.linalg.norm(d) < 1e-13 * (1 + np.linalg.norm(a)): break
    f = F(a, m, h)
    return a if np.all(np.isfinite(f)) and np.linalg.norm(f) < 1e-9 else None
# --- step 1: random complex line on Q4 via the same system with m unknown: solve (a, b) directly
def Fl(x, h1, h2):
    a, b = x[:9], x[9:]
    Q = lambda z: 6*(z**4).sum() - ((z*z).sum())**2
    e = [a.sum(), b.sum(), (a*a).sum(), (b*b).sum(), (a**4).sum(), (b**4).sum(),
         (a**3*b).sum(), (a*b**3).sum(), 9*((a*b)**2).sum() - ((a*b).sum())**2,
         h1 @ a - 1, h2 @ b - 1]
    return np.array(e)
def Jl(x, h1, h2):
    a, b = x[:9], x[9:]; z = np.zeros(9); ab = (a*b).sum()
    r = [np.r_[np.ones(9), z], np.r_[z, np.ones(9)], np.r_[2*a, z], np.r_[z, 2*b],
         np.r_[4*a**3, z], np.r_[z, 4*b**3], np.r_[3*a*a*b, a**3], np.r_[b**3, 3*a*b*b],
         np.r_[18*a*b*b - 2*ab*b, 18*a*a*b - 2*ab*a], np.r_[h1, z], np.r_[z, h2]]
    return np.array(r)
h1, h2 = rng.normal(size=9) + 1j*rng.normal(size=9), rng.normal(size=9) + 1j*rng.normal(size=9)
for t in range(2000):
    x = rng.normal(size=18) + 1j*rng.normal(size=18)
    for _ in range(80):
        d = np.linalg.lstsq(Jl(x, h1, h2), -Fl(x, h1, h2), rcond=None)[0]; x = x + d
        if np.linalg.norm(d) < 1e-14: break
    if np.linalg.norm(Fl(x, h1, h2)) < 1e-10 and abs((x[:9]*x[9:]).sum()) > 1e-3: break
a0, b0 = x[:9], x[9:]
# underdetermined system (11 eqs, 18 unknowns): the solution is a random point of the 7-dim family
m = a0 * b0
print('line found; residual', np.linalg.norm(Fl(x, h1, h2)), ' 9 tr m^2 - (tr m)^2 =', abs(9*(m*m).sum() - m.sum()**2))
h = rng.normal(size=9) + 1j*rng.normal(size=9)
sols = []
def add(a):
    a = a / (h @ a)
    for s in sols:
        if np.linalg.norm(s - a) < 1e-6 * np.linalg.norm(a): return False
    sols.append(a); return True
add(a0 / (h @ a0)); add(b0 / (h @ b0))
print('Jacobian rank of fibre system at a0:', np.linalg.matrix_rank(J(a0/(h@a0), m, h), tol=1e-8))
hist = []
for t in range(N):
    a = newton(rng.normal(size=9) + 1j*rng.normal(size=9), m, h)
    if a is not None and abs((m/a).sum()) < 1e-8 and abs((a*(m/a)).sum()) > 1e-8: add(a)
    if (t+1) % (N//8) == 0: hist.append(len(sols)); print(t+1, 'starts ->', len(sols), 'distinct a', flush=True)
