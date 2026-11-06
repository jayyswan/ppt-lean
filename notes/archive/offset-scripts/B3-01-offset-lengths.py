# B3-01-offset-lengths.py
# Q1/Q2: arc length of offset arcs and the inverse functions arc_of_length inverts.
# Verifies (O2) L_d = L - d*(turning angle) symbolically and numerically, and
# reduces the cusp condition kappa = 1/d for sine and 2^x.
import sympy as sp
import mpmath as mp

mp.mp.dps = 40

def section(t):
    print("\n" + "=" * 70)
    print(t)
    print("=" * 70)

# ---------------------------------------------------------------- generic identity
section("generic: speed(offset) = speed * |1 - d*kappa|  (symbolic)")
t = sp.symbols('t', real=True)
d = sp.symbols('d', real=True)
x = sp.Function('x')(t)
y = sp.Function('y')(t)
vx, vy = sp.diff(x, t), sp.diff(y, t)
sp2 = vx**2 + vy**2
K = vx * sp.diff(vy, t) - vy * sp.diff(vx, t)   # det(v, v')
# offset
NX, NY = -vy / sp.sqrt(sp2), vx / sp.sqrt(sp2)
ox, oy = x + d * NX, y + d * NY
ospeed2 = sp.simplify(sp.diff(ox, t)**2 + sp.diff(oy, t)**2)
pred = sp2 * (1 - d * K / sp2**sp.Rational(3, 2))**2
print("speed(offset)^2 - speed^2*(1-d kappa)^2 simplifies to:",
      sp.simplify(ospeed2 - pred))

# ---------------------------------------------------------------- ellipse
section("ellipse (a cos t, b sin t): L_d = L - d*Delta_theta, L = a*E-type")
a, b = sp.symbols('a b', positive=True)
xe, ye = a * sp.cos(t), b * sp.sin(t)
ve = (sp.diff(xe, t), sp.diff(ye, t))
se2 = sp.simplify(ve[0]**2 + ve[1]**2)
Ke = sp.simplify(ve[0] * sp.diff(ve[1], t) - ve[1] * sp.diff(ve[0], t))
print("sigma^2 =", se2)
print("K = det(v,v') =", Ke)
# turning angle integrand kappa*sigma = K/sigma^2
print("kappa*sigma =", sp.simplify(Ke / se2))
# correction integrand: sigma*(1-d kappa) - sigma = -d K/sigma^2 (elementary)
corr = sp.simplify(-Ke / se2)
print("correction integrand (for L_d = L + d*int corr):", corr,
      "  int =", sp.simplify(sp.integrate(corr, t)))

# ---------------------------------------------------------------- sine
section("sine (x, sin x): L_d = L - d*arctan(cos x)")
xs, ys = t, sp.sin(t)
vs = (sp.diff(xs, t), sp.diff(ys, t))
ss2 = sp.simplify(vs[0]**2 + vs[1]**2)
Ks = sp.simplify(vs[0] * sp.diff(vs[1], t) - vs[1] * sp.diff(vs[0], t))
print("sigma^2 =", ss2, " K =", Ks)
ksig = sp.simplify(Ks / ss2)
print("kappa*sigma =", ksig, "  int =", sp.simplify(sp.integrate(ksig, t)))
corr_s = sp.simplify(-Ks / ss2)
print("correction integrand:", corr_s, "  int =", sp.simplify(sp.integrate(corr_s, t)))

# ---------------------------------------------------------------- 2^x
section("2^x: correction is elementary (log-type)")
z = sp.symbols('z', positive=True)
ln2 = sp.log(2)
xz, yz = t, 2**t
vz = (sp.diff(xz, t), sp.diff(yz, t))
sz2 = sp.simplify(vz[0]**2 + vz[1]**2)
Kz = sp.simplify(vz[0] * sp.diff(vz[1], t) - vz[1] * sp.diff(vz[0], t))
print("sigma^2 =", sz2, " K =", Kz)
print("correction integrand:", sp.simplify(-Kz / sz2))
print("int:", sp.simplify(sp.integrate(-Kz / sz2, t)))

# ---------------------------------------------------------------- cusp conditions
section("cusp condition kappa = 1/d")
u = sp.symbols('u', positive=True)
# sine: cos^2 x = u, sigma^2 = 1+u, -K = sin x, kappa = -sin/(1+u)^{3/2}
# 1/d = kappa -> -d sin x = (1+u)^{3/2}; square with sin^2=1-u
print("sine cusp squared : d^2(1-u) - (1+u)^3 =",
      sp.expand(d**2 * (1 - u) - (1 + u)**3), "=0")
# 2^x: w = (ln2)^2 z^2, sigma^2=1+w, K=(ln2)^2 z, 1/d = (1+w)^{3/2}/((ln2)^2 z)
print("2^x cusp squared  : d^2 (ln2)^2 w - (1+w)^3 =",
      sp.expand(d**2 * ln2**2 * w - (1 + w)**3), "=0") if False else None
w = sp.symbols('w', positive=True)
print("2^x cusp squared  : d^2 (ln2)^2 w - (1+w)^3 =",
      sp.expand(d**2 * ln2**2 * w - (1 + w)**3), "=0")

# ---------------------------------------------------------------- numeric check
section("numeric check of L_d = L - d*Delta_theta (ellipse, sine)")
aa, bb = mp.mpf(2), mp.mpf(1)
# ellipse arc length from 0 to T: int_0^T sqrt(a^2 sin^2 + b^2 cos^2)
Lf = lambda T: mp.quad(lambda th: mp.sqrt(aa**2*mp.sin(th)**2 + bb**2*mp.cos(th)**2), [0, T])
# turning angle integrand for ellipse: K/sigma^2 = a b / (a^2 sin^2 + b^2 cos^2)
dth = lambda T: mp.quad(lambda th: aa*bb/(aa**2*mp.sin(th)**2 + bb**2*mp.cos(th)**2), [0, T])
def offset_speed(T, dd):
    return mp.quad(lambda th: aa*bb/(aa**2*mp.sin(th)**2 + bb**2*mp.cos(th)**2), [0, T])
for T in [mp.mpf('0.7'), mp.mpf('2.1')]:
    for dd in [mp.mpf('0.3'), mp.mpf('-0.8')]:
        Ld = Lf(T) - dd*dth(T)
        # direct: int_0^T sigma*(1 - d*kappa) where sigma*kappa = ab/sigma^2
        direct = mp.quad(lambda th: (mp.sqrt(aa**2*mp.sin(th)**2 + bb**2*mp.cos(th)**2)
                        - dd*aa*bb/(aa**2*mp.sin(th)**2 + bb**2*mp.cos(th)**2)), [0, T])
        print(f"ellipse T={T} d={dd}: formula={mp.nstr(Ld,25)} direct={mp.nstr(direct,25)} "
              f"diff={mp.nstr(Ld-direct,5)}")
# sine: L = int sqrt(1+cos^2), Delta theta = arctan(cos x)-arctan(1)
Lfs = lambda T: mp.quad(lambda th: mp.sqrt(1+mp.cos(th)**2), [0, T])
for T in [mp.mpf('1.3'), mp.mpf('2.6')]:
    for dd in [mp.mpf('0.5'), mp.mpf('-1.1')]:
        Ld = Lfs(T) - dd*(mp.atan(mp.cos(T)) - mp.atan(mp.mpf(1)))
        direct = mp.quad(lambda th: mp.sqrt(1+mp.cos(th)**2)
                         + dd*mp.sin(th)/(1+mp.cos(th)**2), [0, T])
        print(f"sine T={T} d={dd}: formula={mp.nstr(Ld,25)} direct={mp.nstr(direct,25)} "
              f"diff={mp.nstr(Ld-direct,5)}")
