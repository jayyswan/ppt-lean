# Session 39: an explicit r = 5 Engine O member over Q; irreducibility, real roots, disc sign/square, Frobenius cycle types.
# usage: python3 engO_r5.py a b U
import sys, cypari; P=cypari.pari
for l in open('EngineO.gp'):
    l=l.strip()
    if l and not l.startswith('\\\\'): P(l)
a,b,U=sys.argv[1:4]
g=P(f'g=substvec(G,[a,b,U],[({a}),({b}),({U})]); g=g/content(g)')
print('G =',g)
print('irreducible',P('polisirreducible(g)'),' real roots',P('polsturm(g)'),' disc>0',P('poldisc(g)>0'),' disc square',P('issquare(poldisc(g))'))
print('c^2 =',P(f'substvec(-Au/Bu,[a,b,U],[({a}),({b}),({U})])'))
types={}
for p in P('primes(700)'):
    p=int(p)
    if P(f'poldisc(g)%{p}')==0 or P(f'pollead(g)%{p}')==0: continue
    f=P(f'factormod(g,{p})')
    t=tuple(sorted([int(P('poldegree')(f[0][i]))for i in range(len(f[0])) for _ in range(int(f[1][i]))],reverse=True))
    types[t]=types.get(t,0)+1
print(len(types),'cycle types:',sorted(types))
