# Session 39: for Engine O members, real-root count r of G and of Q4|line, line z_i(s) = h(x_i)^2 (1 + s x_i)/F'(x_i) (in K).
# Checks p1,p3,p5 = 0 on the line (relative), and counts real roots of Q4(z(s)) = 6 p4 - p2^2 (a quartic in s).
# usage: python3 engO_q4.py <a> "<b list>" "<U list>"   (rationals)
import sys, cypari, mpmath as mp; P=cypari.pari; mp.mp.dps=60
for l in open('EngineO.gp'):
    l=l.strip()
    if l and not l.startswith('\\\\'): P(l)
a=sys.argv[1]; bl=sys.argv[2].split(','); Ul=sys.argv[3].split(',')
for b in bl:
  for U in Ul:
    g=P(f'substvec(G,[a,b,U],[({a}),({b}),({U})])')
    r=int(P('polsturm')(g)); R=P('polroots')(P('precision')(g,80))
    xs=[mp.mpc(str(P('real')(z)).replace(' E','e'),str(P('imag')(z)).replace(' E','e')) for z in R]
    A_=mp.mpf(a.split('/')[0])/ (mp.mpf(a.split('/')[1]) if '/' in a else 1)
    B_=mp.mpf(b.split('/')[0])/ (mp.mpf(b.split('/')[1]) if '/' in b else 1)
    h=lambda x: x**3+A_*x+B_
    def Fp(i): 
        p=mp.mpf(1)
        for j in range(9):
            if j!=i: p*=xs[i]-xs[j]
        return p
    w=[h(xs[i])**2/Fp(i) for i in range(9)]
    def ps(m,s): return sum((w[i]*(1+s*xs[i]))**m for i in range(9))
    sc=max(abs(wi*(1+xi)) for wi,xi in zip(w,xs))
    chk=max(abs(ps(m,mp.mpf('0.37')))/sc**m for m in (1,3,5))
    # Q4 as quartic in s: interpolate at 5 points
    S=[mp.mpf(k) for k in (-2,-1,0,1,2)]
    vals=[6*ps(4,s)-ps(2,s)**2 for s in S]
    co=mp.matrix([[s**k for k in range(5)] for s in S])**-1*mp.matrix(vals)
    co=[co[k] for k in range(5)]
    qr=mp.polyroots([c.real for c in co[::-1]],maxsteps=200,extraprec=200)
    nr=sum(1 for q in qr if abs(mp.im(q))<1e-25)
    imco=max(abs(mp.im(c)) for c in co)/max(abs(c) for c in co)
    print(f'b={b} U={U}: r={r}  max rel |p1,p3,p5|={mp.nstr(chk,3)}  Q4 coeffs imag/size={mp.nstr(imco,3)}  real roots of Q4|line: {nr}')
