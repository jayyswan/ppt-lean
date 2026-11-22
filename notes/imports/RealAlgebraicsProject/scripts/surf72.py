# surf72.py: cubic surface S_L = L ∩ {Tr u^3 = 0} for the maximal isotropic Q-subspace L of (K_0, Tr u^2) found by witt72.py
import cypari, sys, pickle, itertools
pari=cypari.pari; pari.allocatemem(2*10**9)
d=pickle.load(open(sys.argv[1],'rb')); f=d['f']
zk=[pari('Mod(%s,%s)'%(z,f)) for z in d['zk']]
B0=d['B0']; vs=d['vs']
E=[sum(B0[j][i]*zk[i] for i in range(10)) for j in range(9)]
V=[sum(v[j]*E[j] for j in range(9)) for v in vs]   # elements of K
# saturate: coordinates of V in zk basis, take Z-span ∩ (Q-span ∩ Z^10)
def coords(a): return [pari.nfalgtobasis(pari.nfinit(f),pari.lift(a))[i] for i in range(10)]
nf=pari.nfinit(f)
m=len(V)
Mv=pari.matrix(10,m,[pari.nfalgtobasis(nf,pari.lift(V[j]))[i] for i in range(10) for j in range(m)])
# saturation: kernel of kernel
K1=pari.matkerint(pari.mattranspose(Mv)); 
Sat=pari.matkerint(pari.mattranspose(K1))   # 10x4 saturated basis
# LLL w.r.t. T2
T2=pari('nfinit(%s)'%f)[4][3] if False else None
Gt2=pari.matrix(10,10,[pari.real(pari.trace(zk[i]*pari.conj(zk[j]))) if False else 0 for i in range(10) for j in range(10)])
# use numerical T2 from nf.roots
ro=nf[5]
import mpmath
def emb(a): return [pari.subst(pari.lift(a),'x',ro[k]) for k in range(len(ro))]
cols=[sum(Sat[i,j]*zk[i] for i in range(10)) for j in range(m)]
def t2(a,b):
    ea,eb=emb(a),emb(b); r1=int(nf[1][0]); s=0
    for k in range(len(ro)):
        w=1 if k<r1 else 2
        s+=w*pari.real(ea[k]*pari.conj(eb[k]))
    return s
G=pari.matrix(m,m,[t2(cols[i],cols[j]) for i in range(m) for j in range(m)])
U=pari.qflllgram(G)
L=[sum(U[i,j]*cols[i] for i in range(m)) for j in range(m)]
tr=pari.trace
print('check Q on L:',[tr(L[i]*L[j]) for i in range(m) for j in range(m)])
print('traces',[tr(a) for a in L])
# cubic coefficients
C={}
for a,b,c in itertools.combinations_with_replacement(range(m),3):
    C[(a,b,c)]=int(tr(L[a]*L[b]*L[c]))
print('cubic tensor entries:',C)
pickle.dump({'f':f,'L':[str(pari.lift(a)) for a in L],'C':C},open('surf.pkl','wb'))
