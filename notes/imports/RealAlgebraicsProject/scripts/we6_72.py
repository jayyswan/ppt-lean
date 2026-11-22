# we6_72.py: (a) trace distribution of W(E6) on the E6 lattice (a = 1 + tr, #S(F_q) = q^2 + a q + 1);
# (b) split model of V_3 over F_p: random maximal isotropic Lambda in ({sum x = 0}, sum x^2), cubic surface S = Lambda ∩ {sum x^3 = 0},
#     point count -> a; compare distributions (Frobenius equidistribution in the monodromy group).
import numpy as np, sys, random
from collections import Counter
# (a) W(E6) by BFS on 6x6 matrices of simple reflections, Cartan matrix of E6 (Bourbaki: 1-3-4-5-6 chain, 2 attached to 4)
C=np.array([[2,0,-1,0,0,0],[0,2,0,-1,0,0],[-1,0,2,-1,0,0],[0,-1,-1,2,-1,0],[0,0,0,-1,2,-1],[0,0,0,0,-1,2]])
gens=[]
for i in range(6):
    S=np.eye(6,dtype=np.int64)
    S[i,:]-=C[i,:]   # s_i(alpha_j) = alpha_j - C_ij alpha_i  (acting on root coordinates; row i)
    gens.append(S.T.copy())
seen={np.eye(6,dtype=np.int64).tobytes()}; frontier=[np.eye(6,dtype=np.int64)]; tr=Counter()
tr[6]+=1
while frontier:
    nf=[]
    for M in frontier:
        for g in gens:
            N=g@M; k=N.tobytes()
            if k not in seen:
                seen.add(k); nf.append(N); tr[int(np.trace(N))]+=1
    frontier=nf
print('|W(E6)| =',len(seen)); tot=len(seen)
dist={1+t:c/tot for t,c in sorted(tr.items())}
print('a = 1+tr distribution:',{a:round(v,4) for a,v in dist.items()})
# (b)
p=int(sys.argv[1]) if len(sys.argv)>1 else 31; N=int(sys.argv[2]) if len(sys.argv)>2 else 400
random.seed(int(sys.argv[3]) if len(sys.argv)>3 else 1)
n=10
# basis of V = {sum x = 0}: e_i - e_10
Bv=np.zeros((9,n),dtype=np.int64)
for i in range(9): Bv[i,i]=1; Bv[i,9]=p-1
def Qf(x): return int(np.dot(x,x)%p)
def Bf(x,y): return int(np.dot(x,y)%p)
def rand_vec(): return (np.array([random.randrange(p) for _ in range(9)])@Bv)%p
def nullspace_mod(M):
    # basis of {x : M x = 0} over F_p
    M=M.copy()%p; rows,cols=M.shape; r=0; pivs=[]
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i,c]%p: piv=i;break
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]; inv=pow(int(M[r,c]),p-2,p); M[r]=(M[r]*inv)%p
        for i in range(rows):
            if i!=r and M[i,c]: M[i]=(M[i]-M[i,c]*M[r])%p
        pivs.append(c); r+=1
    free=[c for c in range(cols) if c not in pivs]; B=[]
    for fc in free:
        x=np.zeros(cols,dtype=np.int64); x[fc]=1
        for i,pc in enumerate(pivs): x[pc]=(-M[i,fc])%p
        B.append(x)
    return np.array(B)
def max_isotropic():
    L=[]
    while len(L)<4:
        cons=[np.ones(n,dtype=np.int64)]+[w for w in L]   # sum x = 0 and B(x,w)=0
        Nb=nullspace_mod(np.array(cons))
        for _ in range(20000):
            c=np.array([random.randrange(p) for _ in range(len(Nb))])
            v=(c@Nb)%p
            if not v.any() or Qf(v)!=0: continue
            if rank_mod(np.array(L+[v]))==len(L)+1: L.append(v); break
        else: return None
    return np.array(L)
def rank_mod(M):
    M=M.copy()%p; r=0; rows,cols=M.shape
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i,c]%p: piv=i;break
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]; inv=pow(int(M[r,c]),p-2,p); M[r]=(M[r]*inv)%p
        for i in range(rows):
            if i!=r and M[i,c]: M[i]=(M[i]-M[i,c]*M[r])%p
        r+=1
    return r
# all points of P^3(F_p) as array
pts=[]
for a0 in range(p):
  for a1 in range(p):
    for a2 in range(p): pts.append((1,a0,a1,a2))
for a1 in range(p):
  for a2 in range(p): pts.append((0,1,a1,a2))
for a2 in range(p): pts.append((0,0,1,a2))
pts.append((0,0,0,1)); P=np.array(pts,dtype=np.int64)
cnt=Counter(); bad=0
for it in range(N):
    L=max_isotropic()
    if L is None: continue
    X=(P@L)%p
    T=(X**3 %p).sum(axis=1)%p
    ns=int((T==0).sum())
    a=(ns-p*p-1)
    if a%p: bad+=1; continue
    cnt[a//p]+=1
tot2=sum(cnt.values())
print('p=%d samples=%d non-smooth-looking=%d'%(p,tot2,bad))
print(' a : observed  vs W(E6)')
for a in sorted(set(cnt)|set(dist)):
    print('%3d : %.4f   %.4f'%(a,cnt[a]/tot2 if tot2 else 0,dist.get(a,0)))
