# S28: E-lines in L_135  <->  Engine S shape a cos9t + b sin9t + c cos5t + d sin5t = 0
import numpy as np, sympy as sp
rng=np.random.default_rng(0)
def eline_from_S(a,b,c,d):
    # f(t)=Re[(a-ib)e^{9it}+(c-id)e^{5it}];  lambda=e^{2it} roots of
    # (a-ib)L^9+(c-id)L^7+(c+id)L^2+(a+ib)
    co=np.zeros(10,complex); co[0]=a-1j*b; co[2]=c-1j*d; co[7]=c+1j*d; co[9]=a+1j*b
    lam=np.roots(co); return lam
ok=0; res=[]
for trial in range(200):
    a,b=rng.normal(size=2); c,d=rng.normal(size=2)*0.6
    lam=eline_from_S(a,b,c,d)
    if np.max(abs(abs(lam)-1))>1e-8: continue          # need all 9 on unit circle (totally real)
    th=np.angle(lam)/2                                   # roots of f mod pi
    f=a*np.cos(9*th)+b*np.sin(9*th)+c*np.cos(5*th)+d*np.sin(5*th)
    Z=np.cos(2*th); A=np.sin(2*th)                       # line {r cos(2th-phi)} = r(cos phi Z + sin phi A)
    ps=[max(abs(np.sum((np.cos(p)*Z+np.sin(p)*A)**m)) for p in rng.uniform(0,6.3,5)) for m in (1,3,5,7)]
    M=np.column_stack([np.ones(9),Z*Z,Z*A,A*A]); s=np.linalg.svd(M,compute_uv=False)
    res.append((max(abs(f)),*ps,s[3]/s[0])); ok+=1
res=np.array(res)
print("configs with all 9 roots real:",ok)
print("max |f(theta)|            ",res[:,0].max())
print("max |p1|,|p3|,|p5| on line",res[:,1:4].max(0))
print("min |p7| (should be ~nonzero)",res[:,4].min())
print("conic-rank test: max s4/s1 (rank 3 => E-line)",res[:,5].max())
# Galois sanity over Q: cycle types of H(v) mod primes, v=tan(theta)
v=sp.symbols('v'); a,b,c,d=3,1,1,2
I=sp.I
H=sp.expand(((a-I*b)*(1+I*v)**9+(a+I*b)*(1-I*v)**9+(c-I*d)*(1+I*v)**5*(1+v**2)**2+(c+I*d)*(1-I*v)**5*(1+v**2)**2)/2)
H=sp.Poly(H,v); print("H(v) =",H.as_expr()); print("irreducible over Q:",H.is_irreducible)
print("real roots:",len(sp.Poly(H).real_roots()))
from collections import Counter
cyc=Counter()
for p in sp.primerange(3,400):
    if H.LC()%p==0 or sp.discriminant(H.as_expr(),v)%p==0: continue
    fac=sp.factor_list(H.as_expr(),modulus=p)[1]
    cyc[tuple(sorted(sp.degree(f,v)*e for f,e in fac))]+=1
print(sorted(cyc.items(),key=lambda x:-x[1])[:12])
