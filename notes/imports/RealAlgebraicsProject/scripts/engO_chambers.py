# Session 39: real-root count r of G(x;U,a,b) on the charts a=-1, a=+1 (b,U real) and a=0,b=1.
# r is constant on connected components of the complement of {Dh*A*B=0} (disc identity S39.1).
# usage: python3 engO_chambers.py <a> <bmin> <bmax> <nb> <Umin> <Umax> <nU>
import sys, cypari; P=cypari.pari
for l in open('EngineO.gp'):
    l=l.strip()
    if l and not l.startswith('\\\\'): P(l)
a=sys.argv[1]; bmin,bmax,nb,Umin,Umax,nU=[float(v) for v in sys.argv[2:8]]; nb=int(nb); nU=int(nU)
from fractions import Fraction as Fr
cnt={}; ex={}
rows=[]
for i in range(nb):
    b=Fr(bmin+(bmax-bmin)*i/max(nb-1,1)).limit_denominator(1000)
    row=''
    for j in range(nU):
        U=Fr(Umin+(Umax-Umin)*j/max(nU-1,1)).limit_denominator(1000)
        g=P(f'substvec(G,[a,b,U],[({a}),({b}),({U})])')
        if P('poldegree')(g)<9 or P('poldisc')(g)==0: row+='.'; continue
        r=int(P('polsturm')(g)); cnt[r]=cnt.get(r,0)+1; ex.setdefault(r,(b,U)); row+=str(r)
    rows.append(row)
print('a =',a,' counts', dict(sorted(cnt.items())), ' examples (b,U):', {k:(str(v[0]),str(v[1])) for k,v in ex.items()})
for i,r in enumerate(rows):
    if i%max(1,nb//30)==0: print('%7.3f '%(bmin+(bmax-bmin)*i/max(nb-1,1)), r[::max(1,nU//100)])
