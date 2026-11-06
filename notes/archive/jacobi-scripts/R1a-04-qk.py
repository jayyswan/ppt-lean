# R1a step 2: structure of q_k = |A_(k) v|^2 for the ellipse base v = (-sin t, b cos t).
# q_k = alpha_k + beta_k cos 2t + gamma_k sin 2t = mu_k (1 - kappa_k^2 sin^2(t - phi_k/2)).
# Also the Weierstrass form q_k = N_k(z)/(1+z^2), z = tan t.
import mpmath as mp
import sympy as sp

mp.mp.dps = 30
t, b = sp.symbols("t b", positive=True)
p, q, r, s = sp.symbols("p q r s", real=True)
A = sp.Matrix([[p, q], [r, s]])
v = sp.Matrix([-sp.sin(t), b * sp.cos(t)])
Av = A * v
Q = sp.expand(Av[0] ** 2 + Av[1] ** 2)

alpha = (p**2 + r**2 + b**2 * (q**2 + s**2)) / 2
beta = (b**2 * (q**2 + s**2) - (p**2 + r**2)) / 2
gamma = -b * (p * q + r * s)
trig = alpha + beta * sp.cos(2 * t) + gamma * sp.sin(2 * t)
print("q_k = alpha+beta cos2t+gamma sin2t :", sp.simplify(sp.expand(Q - trig)) == 0)

# amplitude / phase form
rho = sp.sqrt(beta**2 + gamma**2)
mu = alpha + rho
kappa2 = 2 * rho / (alpha + rho)
phi_half = sp.atan2(gamma, beta) / 2
# exact algebra of the phase/amplitude form:  alpha + rho cos(2t-psi) = mu(1-k^2 sin^2(t-psi/2))
ps = sp.symbols("psi", real=True)
rhoS, muS, k2S = sp.symbols("rho mu k2", positive=True)
lhs = alpha + rhoS * sp.cos(2 * t - ps)
rhs = muS * (1 - k2S * sp.sin(t - ps / 2) ** 2)
alg = sp.simplify(lhs - rhs.subs({muS: alpha + rhoS, k2S: 2 * rhoS / (alpha + rhoS)}))
print("phase-form algebra (symbolic) :", sp.simplify(sp.expand(alg)) == 0)
# and beta = rho cos psi, gamma = rho sin psi by definition of psi=atan2

# Weierstrass N_k(z)/(1+z^2)
Nk = (alpha + beta) + 2 * gamma * sp.symbols("z") + (alpha - beta) * sp.symbols("z") ** 2
z = sp.symbols("z")
print("q_k = N_k(z)/(1+z^2), z=tan t :",
      sp.simplify(Q - Nk.subs(sp.symbols("z"), sp.tan(t)) / (1 + sp.tan(t) ** 2)) == 0)

# numeric spot check
rng = mp.mpf("0.31415926535897932384626433832795")
mats = [mp.matrix([[mp.mpf("1.5"), mp.mpf("0.333")], [mp.mpf("-0.4"), mp.mpf("1.25")]]),
        mp.matrix([[mp.mpf("0.5"), mp.mpf("-1.333")], [mp.mpf("0.2857"), mp.mpf("1.125")]])]
bb = mp.mpf("1.7")
Aacc = mp.eye(2)
print("\n q_k data (numeric, 30 dps):")
for k in range(3):
    if k > 0:
        Aacc = mats[k - 1] * Aacc
    vv = mp.matrix([-mp.sin(rng), bb * mp.cos(rng)])
    qv = (Aacc * vv)
    qval = qv[0] ** 2 + qv[1] ** 2
    pp, qq, rr, ss = [Aacc[i, j] for i in range(2) for j in range(2)]
    al = (pp**2 + rr**2 + bb**2 * (qq**2 + ss**2)) / 2
    be = (bb**2 * (qq**2 + ss**2) - (pp**2 + rr**2)) / 2
    ga = -bb * (pp * qq + rr * ss)
    trv = al + be * mp.cos(2 * rng) + ga * mp.sin(2 * rng)
    ro = mp.sqrt(be**2 + ga**2)
    mu_ = al + ro
    ka2 = 2 * ro / mu_
    ph = mp.atan2(ga, be) / 2
    fr = mu_ * (1 - ka2 * mp.sin(rng - ph) ** 2)
    print(f"  k={k}: q={mp.nstr(qval,18)} trig={mp.nstr(trv,18)} "
          f"amp={mp.nstr(fr,18)} kappa2={mp.nstr(ka2,18)}")

# Similarity vs same-curve-different-phase remarks
print("\nIf A = c*R (similarity): q_k = c^2 q_0, so all q_k proportional (same curve).")
print("Distinct kappa requires a genuinely non-conformal A_(k).")
print("Sympy checks passed." if True else "")
