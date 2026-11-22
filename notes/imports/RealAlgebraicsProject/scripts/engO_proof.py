# Session 38: symbolic check of Engine O: G'^2 + Au*Bu*h^5 == 0 mod G over Q(a,b,U)  (x main variable)
import cypari,time; P=cypari.pari
P.allocatemem(4*10**9)
for l in open('EngineO.gp'):
    l=l.strip()
    if l and not l.startswith('\\\\'): P(l)
t=time.time()
P('H=x^3+a*x+b; N=deriv(G,x)^2+Au*Bu*H^5')
P('r=N; L=pollead(G,x); while(poldegree(r,x)>=9, d=poldegree(r,x); r=L*r-polcoef(r,d,x)*x^(d-9)*G)')
print('pseudo-remainder zero:',P('r==0'),' time',round(time.time()-t,1))
