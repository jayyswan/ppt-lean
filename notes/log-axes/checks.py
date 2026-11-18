"""Numeric checks for notes/log-axes/SURVEY.md. Backend: mpmath, 40 digits.
Run: python3 -I notes/log-axes/checks.py   (needs mpmath)."""
from mpmath import mp, mpf, exp, log, sqrt, quad, findroot, diff, cosh, sinh, atan, pi, mpc, quadts

mp.dps = 40

def cell(name, val):
    print(f"{name}: {mp.nstr(val, 12)}")

# C1  Transfer lemma: N1 ∩ line  ==  poly ∩ E5 after X = log u.
p = lambda t: t**3 - 2*t + 1          # rational trendline polynomial
a, b = mpf(1)/2, mpf(3)
X = findroot(lambda X: p(exp(X)) - (a*X + b), 1)
u = findroot(lambda u: p(u) - (a*log(u) + b), 3)
cell("C1 |X - log u|", abs(X - log(u)))

# C2  Three (here four) commensurate rates + drift in ONE log-x graph, sheared.
#     h(X) = p(e^X) + alpha X  with p(t) = t + t^2 + t^3 ; R10 Claim 3.2 class.
h = lambda X: exp(X) + exp(2*X) + exp(3*X) + X
x = mpf(5)
r = findroot(lambda X: h(X) - x, 0.5)
cell("C2 root of e^u+e^2u+e^3u+u = 5", r)
cell("C2 residual", h(r) - x)
#     Neile d=0, cosh^3(u)/3 as N1 - (reflected N1): (t^3+3t)/24 and (3t+t^3)/24 at -u.
g1 = lambda U: (exp(3*U) + 3*exp(U))/24
g2 = lambda U: -(3*exp(-U) + exp(-3*U))/24
U = mpf('0.7')
cell("C2 cosh^3/3 split residual", cosh(U)**3/3 - (g1(U) - g2(U)))

# C3  Arc length of the N1 screen curve (X, p(e^X)) equals the abelian integral in u = e^X.
X0, X1 = mpf(-1), mpf('0.5')
dp = lambda t: 3*t**2 - 2
L_screen = quad(lambda X: sqrt(1 + (exp(X)*dp(exp(X)))**2), [X0, X1])
L_u = quad(lambda u: sqrt(1 + (u*dp(u))**2)/u, [exp(X0), exp(X1)])
cell("C3 |L_screen - L_u|", abs(L_screen - L_u))

# C4  log(x^2-1) on a log-y axis: speed is rational, arc length elementary.
s0, s1 = mpf(2), mpf(5)
L = quad(lambda s: sqrt(1 + (2*s/(s**2-1))**2), [s0, s1])
F = lambda s: s + log((s-1)/(s+1))
cell("C4 |L - [x + log((x-1)/(x+1))]|", abs(L - (F(s1) - F(s0))))

# C5  Monodromy types. softplus-at-rate-2 log(1+e^{2X}) has a log point at i*pi/2:
#     loop integral of its derivative = 2*pi*i (imaginary).  gd u: loop integral of sech = 2*pi (real).
def loop(f, z0, rad=mpf('0.3')):
    return quad(lambda t: f(z0 + rad*exp(1j*t)) * 1j*rad*exp(1j*t), [0, 2*pi])
z0 = mpc(0, pi/2)
m_soft = loop(lambda z: 2*exp(2*z)/(1+exp(2*z)), z0)
m_gd = loop(lambda z: 1/cosh(z), z0)
print("C5 monodromy softplus(2X) at i*pi/2:", mp.nstr(m_soft, 12))
print("C5 monodromy gd at i*pi/2:          ", mp.nstr(m_gd, 12))

# C6  log cosh from log-log poly: log((e^{2X}+1)/2) - X = log cosh X.
cell("C6 residual", log((exp(2*U)+1)/2) - U - log(cosh(U)))

# C7  N4 (Gompertz) arc length: screen form vs u = e^X form.
A, k = mpf(1), mpf(-1)
L4s = quad(lambda X: sqrt(1 + (A*k*exp(X)*exp(k*exp(X)))**2), [X0, X1])
L4u = quad(lambda u: sqrt(1 + (A*k*u*exp(k*u))**2)/u, [exp(X0), exp(X1)])
cell("C7 |L4s - L4u|", abs(L4s - L4u))

# C8  Psi-family (Gaussian type): log(x+2) = x^2  <=>  e^{x^2} = x + 2.
g = findroot(lambda s: log(s+2) - s**2, 1)
cell("C8 root of e^{x^2} = x+2", g)
cell("C8 residual", exp(g**2) - g - 2)
