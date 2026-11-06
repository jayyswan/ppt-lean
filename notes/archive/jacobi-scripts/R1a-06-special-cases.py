# R1a step 4: the two special cases the brief flags.
#   (1) two stages with the SAME elliptic curve (kappa equal) but different phases psi;
#   (2) Q_n constant (final map conformal + circular base).
import mpmath as mp

mp.mp.dps = 30


def q_of(alpha, rho, psi, t):
    # alpha + rho cos(2t - psi) = mu(1 - kappa^2 sin^2(t - psi/2))
    return alpha + rho * mp.cos(2 * t - psi)


def kappa2(alpha, rho):
    return 2 * rho / (alpha + rho)


# (1) same curve (same alpha,rho => same kappa), different phase.
alpha, rho = mp.mpf("2.0"), mp.mpf("0.7")
psi0, psi1 = mp.mpf("0"), mp.mpf("0.9")
print("(1) same elliptic curve, different phases:")
print(f"    kappa^2 (both) = {mp.nstr(kappa2(alpha,rho),15)}")
# zeros of r=q(psi1): cos(2t-psi1) = -alpha/rho
u0 = mp.acos(-alpha / rho)
t0 = (u0 + psi1) / 2
f = lambda t: mp.sqrt(q_of(alpha, rho, psi0, t)) / q_of(alpha, rho, psi1, t) ** mp.mpf("1.5")
print("    mixed term sqrt(q0)/q1^(3/2) at a zero of q1:")
for eps in [mp.mpf("1e-2"), mp.mpf("1e-3"), mp.mpf("1e-4")]:
    v = f(t0 + eps)
    print(f"      eps={mp.nstr(eps,3)}: |f|*eps^1.5 = {mp.nstr(abs(v)*eps**mp.mpf('1.5'),12)}"
          "   (constant => order-3/2 pole)")
print("    => Landen/addition cannot make it first kind: the pole is still there.\n")

# (2) Q_n constant: circular base (b=1), A_2 = similarity . A_1^{-1}.
b = mp.mpf(1)
A1 = ((mp.mpf("1.5"), mp.mpf("0.333")), (mp.mpf("-0.4"), mp.mpf("1.25")))
detA1 = A1[0][0] * A1[1][1] - A1[0][1] * A1[1][0]
A1inv = ((A1[1][1] / detA1, -A1[0][1] / detA1), (-A1[1][0] / detA1, A1[0][0] / detA1))
c = mp.mpf("2.3")
A2 = ((c * A1inv[0][0], c * A1inv[0][1]), (c * A1inv[1][0], c * A1inv[1][1]))


def apply(A, v):
    return (A[0][0] * v[0] + A[0][1] * v[1], A[1][0] * v[0] + A[1][1] * v[1])


def matmul(A, B):
    return ((sum(A[i][k] * B[k][j] for k in range(2))) for i in range(2) for j in range(2)) if False else (
        (A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]),
        (A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]))


Aacc = mp.eye(2)
print("(2) Q_n constant case (circle base, A_2 = c A_1^{-1}):")
for k in [0, 1, 2]:
    if k == 1:
        Aacc = mp.matrix(A1)
    if k == 2:
        Aacc = mp.matrix(A2) * mp.matrix(A1)
    qs = []
    for t in [mp.mpf("0.3"), mp.mpf("1.1"), mp.mpf("2.7")]:
        Aaccm = Aacc
        v = (-mp.sin(t), b * mp.cos(t))
        w = (Aaccm[0, 0] * v[0] + Aaccm[0, 1] * v[1], Aaccm[1, 0] * v[0] + Aaccm[1, 1] * v[1])
        qs.append(w[0] ** 2 + w[1] ** 2)
    print(f"    q_{k} over t = {[mp.nstr(q,12) for q in qs]}")
# reduction of int dt/q1^{3/2} = (int sqrt(q1) - b1 sin2t/sqrt(q1))/(a1^2-b1^2)
p, qq, r, s = A1[0][0], A1[0][1], A1[1][0], A1[1][1]
al1 = (p**2 + r**2 + b**2 * (qq**2 + s**2)) / 2
be1 = (b**2 * (qq**2 + s**2) - (p**2 + r**2)) / 2
ga1 = -b * (p * qq + r * s)
print(f"    q1 coeffs: alpha={mp.nstr(al1,12)} beta={mp.nstr(be1,12)} gamma={mp.nstr(ga1,12)}")
print("    int dt/q1^(3/2) = (E-type - algebraic)/(alpha^2-beta^2)  -> second kind + exact.")
print("    With q2 constant the leading term is elementary; total = elementary + 2nd kind => not F.")
