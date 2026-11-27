"""Numerical checks for notes/generalization/POWER-TOWERS.md (labels T1-T3 match the note).
Run: pip install mpmath; python3 power_tower_checks.py. Each line prints |lhs - rhs|."""
from mpmath import mp, mpf, quad, sqrt, diff, atan2, cos, sin, pi, matrix
mp.dps = 30
def show(name, a, b): print(f"{name}: diff = {mp.nstr(abs(a-b), 5)}   ({mp.nstr(a, 20)})")

p = mpf(5)/2; s = p - 1
d1, d2 = mpf(1)/7, mpf(-1)/5
N1 = matrix([[1, mpf(2)/3], [mpf(-1)/2, mpf(5)/4]])      # first affine map (sheared)
N2 = matrix([[mpf(3)/2, mpf(1)/4], [mpf(1)/3, mpf(4)/5]])  # second affine map
t0, t1 = mpf(1)/2, mpf(3)/2

def lin(N, v): return (N[0,0]*v[0] + N[0,1]*v[1], N[1,0]*v[0] + N[1,1]*v[1])
def offset(g, d):
    def h(t):
        x, y = g(t); dx = diff(lambda u: g(u)[0], t); dy = diff(lambda u: g(u)[1], t)
        n = sqrt(dx**2 + dy**2)
        return (x - d*dy/n, y + d*dx/n)            # left unit normal J T
    return h
g0 = lambda t: (t, t**p)
g1 = offset(g0, d1)                                  # offset, N_1 = I
g2 = lambda t: lin(N1, g1(t))                        # affine
g3 = offset(g2, d2)                                  # offset, N_2 = N1
g4 = lambda t: lin(N2, g3(t))                        # affine, N = N2 N1
def speed(g, t): return sqrt(diff(lambda u: g(u)[0], t)**2 + diff(lambda u: g(u)[1], t)**2)
direct = quad(lambda t: speed(g4, t), [t0, t1])

# T1  normal form: ds = |N(1,v)| dt - sum_j d_j det(N_j) |N(1,v)| / |N_j(1,v)|^3 dv,  v = g'(t)
I2 = matrix([[1, 0], [0, 1]]); N = N2*N1
def nrm(M, v): w = lin(M, (1, v)); return sqrt(w[0]**2 + w[1]**2)
def det(M): return M[0,0]*M[1,1] - M[0,1]*M[1,0]
vp = lambda t: p*t**s; vpp = lambda t: p*s*t**(s-1)
form = quad(lambda t: nrm(N, vp(t)) - sum(dj*det(Nj)*nrm(N, vp(t))/nrm(Nj, vp(t))**3
                                            for dj, Nj in [(d1, I2), (d2, N1)]) * vpp(t), [t0, t1])
show("T1 tower length = normal form", direct, form)

# T2  affine Steiner: tower length = length(N gamma) - sum_j d_j * (arc of ellipse M_j(S^1)), M_j = N N_j^-1
base = quad(lambda t: nrm(N, vp(t)), [t0, t1])
def ellipse_arc(M, th0, th1):
    return quad(lambda th: sqrt(sum(c**2 for c in lin(M, (-sin(th), cos(th))))), [th0, th1])
def psi(Nj, t): w = lin(Nj, (1, vp(t))); return atan2(w[1], w[0])
corr = 0
for dj, Nj in [(d1, I2), (d2, N1)]:
    Mj = N * Nj**-1
    corr += dj * mp.sign(det(Nj)) * ellipse_arc(Mj, psi(Nj, t0) - pi/2, psi(Nj, t1) - pi/2)
show("T2 tower = affine image - sum d_j * ellipse arcs", direct, base - corr)

# T3  sheared power law: genus by 2/(p-1).  p = 5/3 (1/s = 3/2): v^(1/2) sqrt(q) dv -> quartic under v = w^2
r = mp.mpc(mpf(3)/10, mpf(7)/10); q = lambda v: abs(v - r)**2
lhs = quad(lambda v: sqrt(v)*sqrt(q(v)), [mpf(1)/5, mpf(2)])
rhs = quad(lambda w: 2*w**2*sqrt(q(w**2)), [sqrt(mpf(1)/5), sqrt(mpf(2))])
show("T3 p=5/3 sheared length element is sqrt(quartic) in w = sqrt(v)", lhs, rhs)
