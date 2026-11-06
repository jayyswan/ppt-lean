"""A3-01: eliminate (t2,w1,w2) from the offset x offset system over GF(p).

System (two cubic pairs x_i(t), y_i(t), offsets d1, d2):
  E1: (x1-x2) w1 w2 - d1 y1' w2 + d2 y2' w1 = 0
  E2: (y1-y2) w1 w2 + d1 x1' w2 - d2 x2' w1 = 0
  w1^2 = x1'^2 + y1'^2,   w2^2 = x2'^2 + y2'^2

We compute a Groebner basis in lex order with t1 the smallest variable, and read off
the univariate elimination polynomial in t1. Its degree is the genuine degree of the
offset x offset projection (mod p), and we factor it.
"""
import sympy as sp

p = 1000003
t1, t2, w1, w2 = sp.symbols('t1 t2 w1 w2')

# generic random rational cubics; reduce mod p
c = dict(
    x1a3=2, x1a2=-3, x1a1=5, x1a0=7,
    y1a3=1, y1a2=4, y1a1=-2, y1a0=1,
    x2a3=3, x2a2=1, x2a1=-4, x2a0=2,
    y2a3=-1, y2a2=2, y2a1=6, y2a0=-5,
)
def mod(x): return sp.Poly(x, t1, t2, w1, w2, modulus=p).as_expr()

x1 = c['x1a3']*t1**3 + c['x1a2']*t1**2 + c['x1a1']*t1 + c['x1a0']
y1 = c['y1a3']*t1**3 + c['y1a2']*t1**2 + c['y1a1']*t1 + c['y1a0']
x2 = c['x2a3']*t2**3 + c['x2a2']*t2**2 + c['x2a1']*t2 + c['x2a0']
y2 = c['y2a3']*t2**3 + c['y2a2']*t2**2 + c['y2a1']*t2 + c['y2a0']
u1 = sp.diff(x1, t1); v1 = sp.diff(y1, t1)
u2 = sp.diff(x2, t2); v2 = sp.diff(y2, t2)
q1 = u1**2 + v1**2; q2 = u2**2 + v2**2
a = x1 - x2; b = y1 - y2
d1, d2 = 1, 1

E1 = a*w1*w2 - d1*v1*w2 + d2*v2*w1
E2 = b*w1*w2 + d1*u1*w2 - d2*u2*w1
F1 = w1**2 - q1
F2 = w2**2 - q2

print("starting groebner", flush=True)
G = sp.groebner([E1, E2, F1, F2], t2, w1, w2, t1, order='lex', modulus=p)
print("groebner done; basis size", len(G.polys), flush=True)

elim = [g for g in G.polys if g.as_expr().free_symbols <= {t1}]
print("number of univariate-in-t1 basis elements:", len(elim))
for g in elim:
    e = sp.Poly(g.as_expr(), t1, modulus=p)
    print("  degree in t1:", e.degree())
    fac = sp.factor_list(e.as_expr(), modulus=p)
    print("  factorization (monic-ish):")
    for f, m in fac[1]:
        print("      deg", sp.Poly(f, t1, modulus=p).degree(), "mult", m)
