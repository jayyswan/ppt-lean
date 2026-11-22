# offs71.py -- session 71, item (1): offsets of a P-affine image of a Q-quintic graph.
# (a) degree of the offset of y = E0(x) (Euclidean metric; general metric M behaves the same)
# (b) number of crossings of that offset with a random cubic Bezier (resultant in t)
# (c) genus of the foot cover C_M: s^2 = q_M(E0'(x)) for a random metric (generic) and for the
#     metric matched to a non-real critical value of E0' (genus drop to 1)
# usage: python3 offs71.py
import cypari
pari = cypari.pari
pari.allocatemem(2*10**9)

E0 = pari('x^5 + 2*x^4 - x^3 + 3*x^2 - x')      # a Q-quintic whose E0'' has a non-real pair
E1 = pari('deriv(%s,x)' % E0)
print('E0 =', E0, '  E0\'\' roots:', pari('polroots(deriv(deriv(%s,x),x))' % E0))

# (a) degree of offset: generic line aX + bY + c = 0, distance d, metric M^{-1} = [[m11,m12],[m12,m22]]
# foot x, normal v = Minv*(-E0', 1), point = (x,E0) + (d/s) v, s^2 = (-E0',1) Minv (-E0',1)^T
pari('m11=3; m12=1; m22=2; d=7/5; a=2; b=-3; c=5')
pari('E0=%s; E1=deriv(E0,x)' % E0)
pari('q = m11*E1^2 - 2*m12*E1 + m22')               # s^2 (positive definite in E1)
pari('vx = -m11*E1 + m12; vy = -m12*E1 + m22')       # Minv * (-E1, 1)
# a*(x + d vx/s) + b*(E0 + d vy/s) + c = 0  <=>  (a x + b E0 + c) s = -d (a vx + b vy)
deg_line = pari('poldegree((a*x+b*E0+c)^2*q - d^2*(a*vx+b*vy)^2)')
print('(a) offset degree (points on a generic line):', deg_line)

# (b) crossing with a cubic Bezier (X(t),Y(t)): unknowns t (Bezier) and x (foot)
#   normal condition: (X - x, Y - E0) parallel to v  <=>  (X-x)*vy - (Y-E0)*vx = 0
#   distance condition: (X-x, Y-E0) = (d/s) v  =>  ((X-x)^2 ... ) use the M-norm: |w|_M^2 = d^2 with M = Minv^{-1}
pari('X = 2*t^3 - t^2 + 3*t - 1; Y = -t^3 + 4*t^2 + t + 2')
pari('Mi=[m11,m12;m12,m22]; M=Mi^-1')
pari('w1 = X - x; w2 = Y - E0')
pari('f1 = w1*vy - w2*vx')
pari('f2 = M[1,1]*w1^2 + 2*M[1,2]*w1*w2 + M[2,2]*w2^2 - d^2')
R = pari('polresultant(f1, f2, x)')
R = pari('(%s)/content(%s)' % (R, R))
print('(b) Res_x(normal, distance) has degree in t:', pari('poldegree(%s,t)' % R),
      '; squarefree:', pari('poldegree(%s,t) == poldegree(%s/gcd(%s, deriv(%s,t)),t)' % (R, R, R, R)))
print('    real roots (real crossings for this sample):', len(pari('polrootsreal(%s)' % R)))

# (c) genus of the foot cover s^2 = q_M(E0'(x))
def genus_of(poly):
    # hyperelliptic s^2 = poly: genus from the number of odd-multiplicity roots (over C)
    fa = pari('factor(%s)' % poly)
    nrows = int(pari('matsize(%s)[1]' % fa))
    odd = 0
    for i in range(nrows):
        e = int(fa[1][i]); dg = int(pari('poldegree(%s)' % fa[0][i]))
        if e % 2 == 1:
            odd += dg
    return (odd + 1) // 2 - 1 if odd > 0 else -1, odd

g, odd = genus_of(pari('q'))
print('(c) generic metric: q(E0\'(x)) degree', pari('poldegree(q)'), ', odd roots', odd, ', genus', g)

# metric matched to a non-real critical value alpha = E0'(c), E0''(c) = 0, c non-real
# exact: work over the field of the cubic E0''; q(u) = (u - alpha)(u - conj alpha) = u^2 - 2 Re(alpha) u + |alpha|^2
# here we test with high-precision numerics: q has real coefficients in the cubic's real closure
cs = pari('polroots(deriv(deriv(%s,x),x))' % E0)
cnr = [c for c in cs if abs(float(pari('imag(%s)' % c))) > 1e-20][0]
alpha = pari('subst(%s, x, %s)' % (E1, cnr))
re_a = pari('real(%s)' % alpha); n_a = pari('norm(%s)' % alpha)
qa = pari('(%s)^2 - 2*(%s)*(%s) + (%s)' % (E1, re_a, E1, n_a))
rts = pari('polroots(%s)' % qa)
print('(c\') matched metric: roots of q(E0\'(x)) (8, numerical):')
for r in rts:
    print('     ', r)
# count coincident pairs
rl = [complex(float(pari('real(%s)' % r)), float(pari('imag(%s)' % r))) for r in rts]
pairs = sum(1 for i in range(8) for j in range(i+1, 8) if abs(rl[i]-rl[j]) < 1e-6)
print('    coincident root pairs:', pairs, '-> odd-multiplicity roots', 8 - 2*pairs,
      '-> genus', (8 - 2*pairs)//2 - 1)
