# Session 39: exhaustive chamber census of real-root counts r for Engine O.
# For fixed real (a,b) the U-line is cut by the real roots of A(U), B(U); r is constant between them (disc identity).
# One Sturm test per interval. usage: python3 engO_slices.py <a> <bmin> <bmax> <nb>   (a = -1, 1, or 0 with b in {1})
import sys, cypari; P=cypari.pari
from fractions import Fraction as Fr
for l in open('EngineO.gp'):
    l=l.strip()
    if l and not l.startswith('\\\\'): P(l)
a=sys.argv[1]; bmin,bmax=float(sys.argv[2]),float(sys.argv[3]); nb=int(sys.argv[4])
seen={}
for i in range(nb):
    b=Fr(bmin+(bmax-bmin)*i/max(nb-1,1)).limit_denominator(10**6)
    pts=[]
    for pol in ('Au','Bu'):
        f=P(f'substvec({pol},[a,b],[({a}),({b})])')
        for z in P('polroots')(f):
            if abs(float(P('imag')(z)))<1e-9: pts.append(float(P('real')(z)))
    pts=sorted(pts)
    if not pts: continue
    tests=[pts[0]-1-abs(pts[0])]+[(pts[k]+pts[k+1])/2 for k in range(len(pts)-1)]+[pts[-1]+1+abs(pts[-1])]
    sig=[]
    for U in tests:
        Uq=Fr(U).limit_denominator(10**8)
        g=P(f'substvec(G,[a,b,U],[({a}),({b}),({Uq})])')
        if P('poldisc')(g)==0: sig.append('?'); continue
        sig.append(int(P('polsturm')(g)))
    key=tuple(sig)
    if key not in seen: seen[key]=(str(b),[round(p,4) for p in pts])
for k,v in seen.items(): print('r along U-line:',k,'  first at b =',v[0],' real roots of A,B:',v[1])
allr=set(x for k in seen for x in k if x!='?'); print('a =',a,' r values found:',sorted(allr))
