import sympy as sp, random, cypari
pari = cypari.pari
z = sp.symbols('z0:9'); p = lambda k: sum(zi**k for zi in z)
Q4 = 6*p(4) - p(2)**2; Q5 = 18*p(5) - 5*p(2)*p(3)
u = [1,1,1,0,0,0,-1,-1,-1]; w = [0,0,0,1,1,1,-1,-1,-1]
L,M,N = sp.symbols('L M N')
for seed in range(6):
    random.seed(seed)
    q = [random.randint(-9,9) for _ in range(8)]; q.append(-sum(q))
    sub = dict(zip(z,[L*u[i]+M*w[i]+N*q[i] for i in range(9)]))
    C = sp.expand(sp.expand(Q4.subs(sub))/N**2); F = sp.expand(sp.expand(Q5.subs(sub))/N**2)
    r = sp.Poly(sp.resultant(C.subs(N,1), F.subs(N,1), M), L)
    s = str(r.as_expr()).replace('**','^')
    f = pari(s)
    fac = pari.factor(f)
    degs = [int(pari.poldegree(fac[0][i])) for i in range(len(fac[0]))]
    g = None
    if degs==[6]:
        g = pari.polgalois(pari.polredabs(f) if True else f)
    nreal = int(pari.polsturm(f))
    print(seed, "factor degrees", degs, "real roots", nreal, "galois", g)
