# Session 37: an explicit rational S_ord polynomial F_{h,u} over Q: h = (x+1)(x^2-D2), u = e1(F) - c2 rational,
# c2 = -A(u)/B(u). Tracks the 6 sheets from fib.pkl to (D2, c2), picks the sheet with e1 - c2 = u,
# polishes at 80 digits, recognises F in Q[x] (PARI bestappr) and verifies F | F'^2 - c2 h^5 exactly.
# usage: python3 example.py <fib.pkl> <D2> <u> <c2 numerator> <c2 denominator>
import numpy as np, sys, pickle
fib,D2s,u,cn,cd=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5])
c2=cn/cd
sys.argv=['resolv.py',fib,D2s,'250','400']
exec(open('resolv.py').read().split("E=[]")[0].replace("def polish(x):","def polish(x):\n    global C2").replace("mp.mp.dps=70","mp.mp.dps=90").replace("for it in range(12):","for it in range(8):"))
C2=c2; cur=[path(y,(dend,np.log(250.0)),(dend,np.log(c2+0j))) for y in fin]
us=[np.sum(y)-c2 if y is not None else None for y in cur]; print('u values', np.round(us,6))
k=int(np.argmin([abs(v-u) if v is not None else 1e9 for v in us])); C2=mp.mpf(cn)/cd
X,r=polish(cur[k]); print('resid', mp.nstr(r,3))
# coefficients of F
co=[mp.mpc(1)]
for xr in X: co=[(co[i] if i<len(co) else 0)-xr*(co[i-1] if i>0 else 0) for i in range(len(co)+1)]
import cypari; pari=cypari.pari
cs=[]
for c in co:
    s=mp.nstr(c.real,85); q=pari('bestappr(%s, 10^30)'%s); cs.append(q); 
    print(q, ' imag %.1e'%float(abs(c.imag)), ' err %.1e'%float(abs(mp.mpf(s)-mp.mpf(pari('%s*1.0'%q).__str__().replace(' E','e')))))
F=pari('Pol([%s],x)'%','.join(str(q) for q in cs))
h=pari('(x+1)*(x^2-(%s))'%D2s)
print('F =',F)
print('exact check (deriv(F)^2 - c2 h^5) mod F =', pari('(deriv(%s)^2 - (%d/%d)*(%s)^5) %% (%s)'%(F,cn,cd,h,F)))
print('real roots', pari('polsturm(%s)'%F), ' irreducible', pari('polisirreducible(%s)'%F))
print('disc squarefree part sign', pari('sign(poldisc(%s))'%F))
pickle.dump(str(F),open('F_example.pkl','wb'))
