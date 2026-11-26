"""Numerical checks for notes/generalization/GENERALIZATIONS.md (labels C1-C10 match the note).
Run: pip install mpmath; python3 generalizations_checks.py. Each line prints |lhs - rhs|."""
from mpmath import mp, mpf, quad, sqrt, hyp2f1, hyp3f2, betainc, appellf1, conj, gamma, beta
mp.dps = 40
def show(name, a, b): print(f"{name}: diff = {mp.nstr(abs(a-b), 5)}   ({mp.nstr(a, 20)})")

# C1  Gamma paper's arc length is a 2F1 at z = -1
s = mpf(5)/2
l = quad(lambda x: sqrt(1+x**s), [0,1])
show("C1 l(sigma)=2F1(-1/2,1/s;1+1/s;-1)", l, hyp2f1(-0.5, 1/s, 1+1/s, -1))
A = quad(lambda x: 1/sqrt(1+x**s), [0,1])
show("C6 A(sigma)=2F1(1/2,1/s;1+1/s;-1)", A, hyp2f1(0.5, 1/s, 1+1/s, -1))

# C2  general endpoint and coefficient: incomplete Beta with p+q = -1/2, any w X^s (beyond |z|<1)
for (s, w, X) in [(mpf(5)/2, mpf(3), mpf(7)/5), (mpf(2)/3, mpf(1)/2, mpf(4)), (mpf(7), mpf(2), mpf(1))]:
    L = quad(lambda x: sqrt(1+w*x**s), [0, X])
    U = w*X**s; T = U/(1+U); p = 1/s
    viaBeta = (1/s)*w**(-p)*betainc(p, -p-mpf(1)/2, 0, T)
    viaPfaff = X*sqrt(1+U)*hyp2f1(-0.5, 1, 1+p, T)
    show(f"C2 beta  s={s},w={w},X={X} (U={mp.nstr(U,4)})", L, viaBeta)
    show(f"C2 pfaff s={s},w={w},X={X}", L, viaPfaff)

# C3  affine image of a rational power law: Appell F1 at a conjugate pair
n = mpf(5)/2; sexp = n-1
a, b, c, d = mpf(1), mpf(2)/3, mpf(-1)/2, mpf(3)/4
X = mpf(1)/2
sp = lambda t: sqrt((a + b*n*t**sexp)**2 + (c + d*n*t**sexp)**2)
L = quad(sp, [0, X])
z1 = complex(a, c); z2 = complex(b*n, d*n)   # speed = |z1 + z2 u|
r = -mp.mpc(z1)/mp.mpc(z2)
F = appellf1(1/sexp, -0.5, -0.5, 1+1/sexp, X**sexp/r, X**sexp/conj(r))
show("C3 affine power-law arc = X|z1| F1(1/s;-1/2,-1/2;1+1/s;X^s/r,X^s/rbar)", L, X*abs(mp.mpc(z1))*F.real)
print("   imag part of F1:", mp.nstr(F.imag, 5))

# C5  Clausen on the power-law class: 2F1(1/2,p;p+1;z)^2 = 3F2(1,2p,p+1/2;2p+1,p+1;z)
for p in [mpf(2)/5, mpf(3)/7]:
    z = mpf(3)/10
    show(f"C5 Clausen p={p}", hyp2f1(0.5,p,p+1,z)**2, hyp3f2(1,2*p,p+0.5,2*p+1,p+1,z))

# C8  Goursat on the power-law class: 2F1(1,2p;p+1;z) = 2F1(1/2,p;p+1;4z(1-z))
p = mpf(2)/5; z = mpf(1)/5
show("C8 Goursat", hyp2f1(1,2*p,p+1,z), hyp2f1(0.5,p,p+1,4*z*(1-z)))

# C9  quadratic map: B_T(p,p) = 2^(1-2p) B_{4T(1-T)}(p,1/2)  for T <= 1/2
p = mpf(1)/3; T = mpf(1)/5
show("C9 B_T(p,p) vs B_{4T(1-T)}(p,1/2)", betainc(p,p,0,T), 2**(1-2*p)/2*betainc(p,0.5,0,4*T*(1-T)))

# C10  bcc lattice Green function is (2K/pi)^2 at every t in (0,1); t = 1 is Watson's I1
from mpmath import cos, pi, ellipk
mp.dps = 20
for t in [mpf(3)/5, mpf(9)/10]:
    G = quad(lambda x: quad(lambda y: 1/sqrt(1 - t**2*cos(x)**2*cos(y)**2), [0, pi/2, pi]),
             [0, pi/2, pi])/pi**2
    show(f"C10 bcc G({t})", G, (2/pi)**2*ellipk((1 - sqrt(1 - t**2))/2)**2)
