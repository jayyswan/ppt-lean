# Session 38: scan Engine O for totally real members. h = (x+1)(x^2+beta^2) depressed; u = e1(F)-c^2 in depressed coords.
# usage: python3 engO_scan.py <beta num> <beta den> <umin> <umax> <ustep num> <ustep den>
import cypari,sys; P=cypari.pari
P.allocatemem(10**9)
P(open('engO_poly.gp').read().replace('\n',''))
P('Bu=U^5+1296*a*U^3+50112*b*U^2+27648*a^2*U+2985984*a*b')
P('Au=U^6+1278*a*U^4+50274*b*U^3+3321*a^2*U^2+2357586*a*b*U-1822500*a^3+6751269*b^2')
P('G=Bu*x^9+sum(k=1,9,(-1)^k*eval(Str("E",k))*x^(9-k))')
bn,bd,u0,u1,sn,sd=sys.argv[1:7]
P(f'be=({bn})/({bd}); hh=subst((x+1)*(x^2+be^2),x,x-1/3); aa=polcoef(hh,1); bb=polcoef(hh,0)')
P(f'Gab=subst(subst(G,a,aa),b,bb); hab=subst(subst(x^3+a*x+b,a,aa),b,bb)')
print('a,b =',P('[aa,bb]'),' j =',P('1.*1728*4*aa^3/(4*aa^3+27*bb^2)'))
P(f'res=List(); forstep(n={u0}*{sd},{u1}*{sd},{sn}, u=n/{sd}; g=subst(Gab,U,u); if(poldegree(g)==9 && polsturm(g)>=7, listput(res,[u,polsturm(g),1.*subst(subst(-Au,a,aa),b,bb)/subst(subst(Bu,a,aa),b,bb)])))')
print(P('res'))
