# Phase 0: exact count of complex solutions of the decic square system over F_p.
import sympy as sp, sys, time
sys.stdout.reconfigure(line_buffering=True)

p = int(sys.argv[1]) if len(sys.argv)>1 else 32003
method = sys.argv[2] if len(sys.argv)>2 else 'f5b'
order = sys.argv[3] if len(sys.argv)>3 else 'grevlex'

a,b,c,pp,qq,rr,D = sp.symbols('a b c p q r D')
t = sp.symbols('t')
f = t**7 - 14*t**5 + 49*t**3 - 36*t + 1
u = t**3 + a*t**2 + b*t + c
v = pp*t**2 + qq*t + rr
up = sp.diff(u,t); vp = sp.diff(v,t)
S = up**2 + vp**2
W = sp.expand(u**2*S - D*vp**2)
rem = sp.rem(sp.Poly(W, t), sp.Poly(f, t)).as_expr()
eqs = [sp.expand(sp.Poly(cf, [a,b,c,pp,qq,rr,D], modulus=p).as_expr())
       for cf in sp.Poly(rem, t).all_coeffs()]
print("num eqs", len(eqs), "degrees", [sp.Poly(e,[a,b,c,pp,qq,rr,D],modulus=p).total_degree() for e in eqs], flush=True)
t0=time.time()
G = sp.groebner(eqs, a,b,c,pp,qq,rr,D, order=order, modulus=p, method=method)
print("groebner done in %.1fs, size %d" % (time.time()-t0, len(G.exprs)), flush=True)
# leading monomials -> degree (number of solutions) if zero-dimensional
lm = [G.exprs[i].as_poly(*[a,b,c,pp,qq,rr,D]).LM() for i in range(len(G.exprs))]
print("leading monomials:", lm, flush=True)
