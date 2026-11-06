# R1a step 3: reductions of the basic ellipse integrals and the pole structure of the
# generic correction term sqrt(q_n)/q_k^{3/2}.
#
# Integrand of the chain (interval where all signs are +):
#   ds_n/dt = sqrt(q_n) - sum_k c_k sqrt(q_n)/q_k^{3/2} ,  c_k = d_k sign(S_k) detA_(k) K .
# (i)  sqrt(q)      : second kind (E) when q non-constant.
# (ii) 1/q          : elementary (third kind), from the similarity case.
# (iii) sqrt(q_n)/q_k^{3/2} : has a genuine finite pole at every complex zero of q_k.
import mpmath as mp
import sympy as sp

mp.mp.dps = 30
t, a, b = sp.symbols("t a b", positive=True)
q = a + b * sp.cos(2 * t)

# ---- (i) reduction of int dt/q^{3/2} = (int sqrt(q)dt - b sin2t/sqrt(q)) / (a^2-b^2) ----
S = sp.Function("S")
I3 = (S(t) - b * sp.sin(2 * t) / sp.sqrt(q)) / (a**2 - b**2)
dI3 = sp.diff(I3, t).subs(sp.Derivative(S(t), t), sp.sqrt(q))
print("int dt/q^{3/2} reduction (symbolic) :", sp.simplify(dI3 - q ** sp.Rational(-3, 2)) == 0)

# ---- (ii) elementary int dt/q ----
k0 = sp.sqrt((a - b) / (a + b))
I1 = sp.atan(k0 * sp.tan(t)) / sp.sqrt(a**2 - b**2)
print("int dt/q elementary (symbolic)     :", sp.simplify(sp.diff(I1, t) - 1 / q) == 0)

# ---- ellipse arc length = second-kind E (numeric) ----
bb = mp.mpf("1.7")
m = (bb**2 - 1) / bb**2  # kappa^2
T = mp.mpf("2.3")
q0 = lambda s: mp.sin(s) ** 2 + bb**2 * mp.cos(s) ** 2
num = mp.quad(lambda s: mp.sqrt(q0(s)), [0, T])
E = bb * mp.ellipe(T, m)
print(f"int_0^T sqrt(q0) = {mp.nstr(num,20)}   b*ellipe(T,m) = {mp.nstr(E,20)}"
      f"   diff = {mp.nstr(abs(num-E), 5)}")

# ---- (iii) pole of the generic mixed term at a complex zero of q_k ----
# pick non-proportional q0,q1 from a non-similarity 2x2 map
A1 = ((mp.mpf("1.5"), mp.mpf("0.333")), (mp.mpf("-0.4"), mp.mpf("1.25")))


def coeffs(A, bb):
    p, qq, r, s = A[0][0], A[0][1], A[1][0], A[1][1]
    al = (p**2 + r**2 + bb**2 * (qq**2 + s**2)) / 2
    be = (bb**2 * (qq**2 + s**2) - (p**2 + r**2)) / 2
    ga = -bb * (p * qq + r * s)
    return al, be, ga


def qval(A, bb, z):  # z complex
    al, be, ga = coeffs(A, bb)
    return al + be * mp.cos(2 * z) + ga * mp.sin(2 * z)


al0, be0, ga0 = coeffs(((mp.mpf(1), mp.mpf(0)), (mp.mpf(0), mp.mpf(1))), bb)
# complex zero of q0: al0+be0 cos2t + ga0 sin2t = 0 (base has ga0=0)
cos2t0 = -al0 / be0
t0 = mp.acos(cos2t0) / 2  # principal complex value
print(f"\nbase q0 zeros at 2t = +/- {mp.nstr(mp.acos(cos2t0),12)}; |cos2t0|>1: {abs(cos2t0)>1}")

for tag, A in [("q1 (mapped)", A1)]:
    f = lambda z: mp.sqrt(qval(A, bb, z)) / qval(((mp.mpf(1), mp.mpf(0)), (mp.mpf(0), mp.mpf(1))), bb, z) ** mp.mpf("1.5")
    print(f"mixed term sqrt({tag})/q0^(3/2) near zero t0 of q0:")
    for eps in [mp.mpf("1e-2"), mp.mpf("1e-3"), mp.mpf("1e-4")]:
        val = f(t0 + eps)
        print(f"   eps={mp.nstr(eps,3)}: |f|={mp.nstr(abs(val),12)}  "
              f"|f|*eps^1.5={mp.nstr(abs(val)*eps**mp.mpf('1.5'),12)}")
    print("   -> |f| ~ eps^(-3/2): order-3/2 pole, NOT holomorphic.")

# candidate first-kind forms are bounded near t0
for tag, A in [("q0", ((mp.mpf(1), mp.mpf(0)), (mp.mpf(0), mp.mpf(1)))),
               ("q1", A1)]:
    g = lambda z: 1 / mp.sqrt(qval(A, bb, z))
    print(f"  1/sqrt({tag}) at eps=1e-4: {mp.nstr(abs(g(t0+mp.mpf('1e-4'))),12)} (bounded)")

# ---- similarity-chain closed form (algebra) ----
print("\nSimilarity chain: A_k = c_k R_k => q_k = c_k^2 q_0,")
print("  S_n = 1 - K (sum_k d_k sign(S_k) c_k^2 /(c_k^3 q_0^{3/2}))")
print("  ds_n = c_1..c_n [ sqrt(q_0) - K (sum_k d_k sign/c_k) / q_0 ] dt  (E + elementary).")
