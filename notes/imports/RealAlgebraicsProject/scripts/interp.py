# Session 37: e1-resolvent R(T, c2) = prod_k (T - e1(F_k)) of the 6 sheets of U_C over the c2-line,
# for h = (x+1)(x^2 - D2) with D2 rational, at integer c2 values; prints coefficients (should be integers).
# usage: python3 interp.py <fib.pkl> <D2> <c2 list comma> [dps]   ; writes R_<D2>.txt
import numpy as np, sys, pickle
fib=sys.argv[1]; D2s=sys.argv[2]; clist=[int(c) for c in sys.argv[3].split(',')]; dps=int(sys.argv[4]) if len(sys.argv)>4 else 60
sys.argv=['resolv.py',fib,D2s,str(clist[0]),'400']
src=open('resolv.py').read()
exec(src.split("E=[]")[0].replace("def polish(x):","def polish(x):\n    global C2").replace("for it in range(12):","for it in range(6):").replace("mp.mp.dps=70","mp.mp.dps=%d"%dps))
out=open('R_%s.txt'%D2s,'a')
cur=fin
for c in clist:
    C2=float(c)
    if c!=clist[0]:
        cur=[path(y,(dend,np.log(prev)),(dend,np.log(C2))) for y in cur]
    prev=C2
    E=[]
    for y in cur:
        X,r=polish(y); E.append(mp.fsum(X))
    T=[mp.mpf(1)]
    for e in E: T=[(T[k] if k<len(T) else 0)-e*(T[k-1] if k>0 else 0) for k in range(len(T)+1)]
    co=[mp.nint(t.real) for t in T]; err=max(abs(t-n) for t,n in zip(T,co))
    line='%d %s err %.1e'%(c,' '.join(str(int(n)) for n in co),float(err)); print(line,flush=True); out.write(line+'\n')
