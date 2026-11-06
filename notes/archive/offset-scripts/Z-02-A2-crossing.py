# Z-02: independent re-verification of A2 (offset x second curve, degrees 10m).
# Re-derives the rationalized crossing polynomial Q(t) = A^2 - B^2 q from scratch:
#   w^m F(Gamma(t)) reduced mod (w^2 - q)  ->  A + B w,  Q = A^2 - B^2 q.
# Checks Q matches the printed degree-20 (ellipse) / degree-30 (nodal cubic) polynomials,
# irreducibility, real roots, genuine crossing for one sign of d, and Galois cycle types.
import sympy as sp

t, w = sp.symbols('t w', real=True)


def offset_point(x, y, d):
    # use 1/w = w/q so the point is a polynomial in w (with w^2 = q)
    u, v = sp.diff(x, t), sp.diff(y, t)
    q = sp.expand(u ** 2 + v ** 2)
    Gx = sp.expand(x - d * v * w / q)
    Gy = sp.expand(y + d * u * w / q)
    return Gx, Gy, q


def rationalize(F, x, y, d, XX, YY):
    # F is an expression in the two symbols XX, YY.
    Gx, Gy, q = offset_point(x, y, d)
    num, den = sp.fraction(sp.cancel(F.subs({XX: Gx, YY: Gy})))
    # den is a power of q (w never appears in the denominator); num is polynomial in w
    scaled = sp.expand(num)
    # reduce w^k -> q^(k//2) * w^(k%2)
    wpoly = sp.Poly(sp.expand(scaled), w)
    A, B = sp.Integer(0), sp.Integer(0)
    for (k,), c in wpoly.terms():
        if k % 2 == 0:
            A += c * q ** (k // 2)
        else:
            B += c * q ** ((k - 1) // 2)
    # num above was multiplied by the denominator (a power of q); divide out the
    # common factor of A and B to get the minimal rationalization (the true norm form).
    A, B = sp.expand(A), sp.expand(B)
    Ap, Bp = sp.Poly(A, t), sp.Poly(B, t)
    g = sp.gcd(Ap, Bp)
    if g.degree() > 0:
        A = sp.expand(Ap.quo(g).as_expr())
        B = sp.expand(Bp.quo(g).as_expr())
    Q = sp.expand(A ** 2 - B ** 2 * q)
    return Q, A, B, q, (XX, YY)


# ---------- F2: offset of cubic pair x = t^3+t+1, y = 2t^3-t^2+3, d=2, ellipse 4X^2+9Y^2=36
X, Y = sp.symbols('X Y')
x2 = t ** 3 + t + 1
y2 = 2 * t ** 3 - t ** 2 + 3
F2 = 4 * X ** 2 + 9 * Y ** 2 - 36
Q2, A2, B2, q2, syms2 = rationalize(F2, x2, y2, sp.Integer(2), X, Y)
print("=== F2 ellipse: deg Q2 =", sp.Poly(Q2, t).degree(), " (expected 20)")
print("    deg A =", sp.Poly(A2, t).degree(), " deg B =", sp.Poly(B2, t).degree(),
      " deg q =", sp.Poly(q2, t).degree())
print("    irreducible:", sp.Poly(Q2, t).is_irreducible)
prim2 = sp.Poly(Q2, t).primitive()[1]
print("    primitive integer Q2 =", prim2.as_expr())
qn2 = sp.nroots(prim2, n=50, maxsteps=300)
reals2 = sorted(complex(r).real for r in qn2 if abs(complex(r).imag) < sp.Float('1e-35'))
print("    #real roots:", len(reals2), [sp.N(r, 40) for r in reals2])
# genuine crossing: evaluate F2 at the true geometric offset point with w = sqrt(q)
u2, v2 = sp.diff(x2, t), sp.diff(y2, t)
q2e = sp.expand(u2 ** 2 + v2 ** 2)
for r in reals2:
    rq = complex(sp.N(q2e.subs(t, r), 60))
    wr = complex(sp.sqrt(rq))
    for sgn in (1, -1):
        d = 2 * sgn
        gx = complex(sp.N(x2.subs(t, r), 60)) - d * complex(sp.N(v2.subs(t, r), 60)) / wr
        gy = complex(sp.N(y2.subs(t, r), 60)) + d * complex(sp.N(u2.subs(t, r), 60)) / wr
        fv = 4 * gx ** 2 + 9 * gy ** 2 - 36
        print(f"      t={sp.N(r,40)} d={d:+d}: F(offset)={abs(fv):.2e}")

print()
# ---------- F3: same base, d=2, nodal cubic Y^2 = X^3 - X^2  =>  F = X^3 - X^2 - Y^2
F3 = X ** 3 - X ** 2 - Y ** 2
Q3, A3, B3, q3, syms3 = rationalize(F3, x2, y2, sp.Integer(2), X, Y)
print("=== F3 nodal cubic: deg Q3 =", sp.Poly(Q3, t).degree(), " (expected 30)")
print("    deg A =", sp.Poly(A3, t).degree(), " deg B =", sp.Poly(B3, t).degree(),
      " deg q =", sp.Poly(q3, t).degree())
print("    irreducible:", sp.Poly(Q3, t).is_irreducible)
prim3 = sp.Poly(Q3, t).primitive()[1]
print("    primitive integer Q3 =", prim3.as_expr())
qn3 = sp.nroots(prim3, n=50, maxsteps=300)
reals3 = sorted(complex(r).real for r in qn3 if abs(complex(r).imag) < sp.Float('1e-35'))
print("    #real roots:", len(reals3), [sp.N(r, 40) for r in reals3])
for r in reals3:
    rq = complex(sp.N(q2e.subs(t, r), 60))
    wr = complex(sp.sqrt(rq))
    for sgn in (1, -1):
        d = 2 * sgn
        gx = complex(sp.N(x2.subs(t, r), 60)) - d * complex(sp.N(v2.subs(t, r), 60)) / wr
        gy = complex(sp.N(y2.subs(t, r), 60)) + d * complex(sp.N(u2.subs(t, r), 60)) / wr
        fv = gx ** 3 - gx ** 2 - gy ** 2
        print(f"      t={sp.N(r,40)} d={d:+d}: F(offset)={abs(fv):.2e}")


def galois_cycle_types(poly, primes=(1000003, 2000003, 3000017, 4000037, 5000011)):
    for q in primes:
        fac = sp.factor_list(poly, modulus=q)[1]
        mults = sorted([(f[0].degree(), f[1]) for f in fac])
        print(f"    mod {q}: {mults}")


print()
print("=== Galois cycle types Q2 (deg 20) ===")
galois_cycle_types(prim2)
print("=== Galois cycle types Q3 (deg 30) ===")
galois_cycle_types(prim3)
