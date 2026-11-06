"""R1c step 3: the 2^x base.

(a) speed of A.(x, 2^x) = sqrt(q0 + q1 z + q2 z^2), z = 2^x, and
        ds = sqrt(q0+q1 z+q2 z^2) dz/(z ln2).
    The curve Y^2 = q0+q1 z+q2 z^2 is a CONIC (genus 0), so this integral is
    elementary.  Verified symbolically for concrete q.
(b) one offset after A: correction = -d detA ln2 dz/Q_A(z), also elementary.
(c) two offsets: correction term ~ sqrt(Q_n)/Q_k^{3/2} dz with Q_n != Q_k.
    After rationally parametrising the conic Y^2 = Q_n(z), the integrand becomes
    W(m)/V(m)^{3/2} dm with V a quartic; genus 1 iff V is squarefree.  Verified.
"""
import mpmath as mp
import sympy as sp

z, m = sp.symbols('z m', real=True)
ln2 = sp.log(2)

print("=== (a) exp_two base arc length is elementary (genus 0) ===")
q0, q1, q2 = sp.Rational(3, 2), sp.Rational(-1, 4), sp.Rational(5, 3)
I = sp.integrate(sp.sqrt(q0 + q1 * z + q2 * z ** 2) / z, z)
print("integral =", sp.simplify(I))
# independent numeric check at a point
Iv = sp.integrate(sp.sqrt(q0 + q1 * z + q2 * z ** 2) / z, (z, sp.Rational(1, 2), sp.Integer(2)))
print("definite int [0.5,2] =", sp.nsimplify(Iv))
print("numeric =", mp.nstr(mp.quad(lambda t: mp.sqrt(1.5 - 0.25 * t + (5.0 / 3) * t * t) / t,
                                   [0.5, 2]), 25))

print()
print("=== (b) one offset after A: correction -d detA ln2 dz/Q_A(z) is elementary ===")
Qc = 1 + 3 * z + 2 * z ** 2
print("integral dz/Q_A =", sp.integrate(1 / Qc, z))

print()
print("=== (c) two offsets: genus-1 curve from two distinct quadratics ===")
# Q_n = 1 + z + z^2 (q2=1, rational point at infinity (1:1:0))
# conic parametrisation Y = z + m  =>  R(m) = (1 - m^2)/(2m - 1)
N = 1 - m ** 2
D = 2 * m - 1
R = N / D
qn = [1, 1, 1]
qk = [2, 3, 1]
# V = qk2*N^2 + qk1*N*D + qk0*D^2  (quartic)
V = sp.expand(qk[2] * N ** 2 + qk[1] * N * D + qk[0] * D ** 2)
print("V(m) =", V)
print("V factored =", sp.factor(V))
print("disc(V) =", sp.discriminant(V, m))
roots = sp.solve(V, m)
print("roots V =", roots)
print("number of distinct roots =", len(set([sp.nsimplify(r) for r in roots])))

# j-invariant of y^2 = V(m) after reduction is more work; instead show the
# associated smooth projective curve is the intersection of two quadrics:
#   Y^2 = Qn(z), W^2 = Qk(z)  in P^3 (variables z,Y,W,T).
zv, Y, W, T = sp.symbols('zv Y W T')


def quadric(q):
    M = sp.zeros(4, 4)
    M[1, 1] = 1                      # Y^2
    M[0, 0] = -q[2]                  # -q2 z^2
    M[0, 3] = -q[0] / 1
    M[3, 0] = -q[0] / 1
    M[3, 3] = -q[0]                  # careful: using q0 and q1 together below
    return M


# Build correctly: Y^2 T^2 ? Use affine slice T=1, then Y^2 = q2 z^2+q1 z+q0.
# Homogenise with T: Y^2 = q2 z^2 + q1 z T + q0 T^2.
def qmat(q):
    M = sp.zeros(4, 4)
    M[1, 1] = 1
    M[0, 0] = -q[2]
    M[0, 3] -= q[1] / 2
    M[3, 0] -= q[1] / 2
    M[3, 3] = -q[0]
    return M


M1 = qmat(qn)
M2 = qmat(qk)
lam = sp.symbols('lam')
print("det(M1 + lam M2) =", sp.factor((M1 + lam * M2).det()))
# Smooth intersection of two quadrics in P^3 has genus 1; check the discriminant
# of the discriminant locus is nonzero (four distinct base points).
print("base locus / pencil smooth iff det is not a perfect power times constant:")
print("  det polynomial in lam, degree:", sp.degree((M1 + lam * M2).det(), lam))
