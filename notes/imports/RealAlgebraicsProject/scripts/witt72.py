# witt72.py: trace form on K_0 for a decic field; maximal isotropic subspace over Q via qfsolve (Witt decomposition)
import cypari, sys
pari=cypari.pari; pari.allocatemem(2*10**9)
f=sys.argv[1] if len(sys.argv)>1 else 'x^10+x^3-2*x+1'
nf=pari.nfinit(f); n=10
zk=nf[6] if False else pari('nfinit(%s).zk'%f)
print('field disc', pari.factor(pari('nfinit(%s).disc'%f)))
# multiplication via elements as polmods
W=[pari('Mod(%s,%s)'%(zk[i],f)) for i in range(n)]
tr=lambda a: pari.trace(a)
G2=[[tr(W[i]*W[j]) for j in range(n)] for i in range(n)]
t1=[tr(W[i]) for i in range(n)]
# kernel of trace (integral basis of K_0)
M=pari.matrix(1,n,t1)
ker=pari.matkerint(M)   # columns
B0=[[ker[i,j] for i in range(n)] for j in range(9)]  # B0[j] coefficient vector
E=[sum(B0[j][i]*W[i] for i in range(n)) for j in range(9)]
Q=pari.matrix(9,9,[tr(E[i]*E[j]) for i in range(9) for j in range(9)])
print('sig of Q on K0', pari.qfsign(Q))
print('det', pari.factor(pari.matdet(Q)))
def witt(Q):
    vs=[]; cur=Q; basis=pari.matid(Q.matsize()[0])
    while True:
        m=cur.matsize()[0]
        if m<2: break
        s=pari.qfsolve(cur)
        if str(pari.type(s))=='t_MAT': s=pari('['+','.join(str(s[i,0]) for i in range(m))+']~')
        if str(pari.type(s)) not in ('t_COL','t_MAT'): print('stop: qfsolve ->',s,'dim',m); break
        v=basis*s; vs.append(v)
        # hyperbolic partner: w with B(s,w)!=0
        Bs=cur*s
        # complement: vectors orthogonal to s and to w; choose w = e_j with Bs[j]!=0
        j=[i for i in range(m) if Bs[i]!=0][0]
        w=pari.mattranspose(pari.matrix(1,m,[1 if i==j else 0 for i in range(m)]))
        H=pari.matconcat([s,w])
        C=pari.matkerint(pari.mattranspose(H)*cur)  # orthogonal complement of span(s,w)
        basis=basis*C; cur=pari.mattranspose(C)*cur*C
    return vs,cur
vs,rest=witt(Q)
print('isotropic vectors found:',len(vs),' residual form sig',pari.qfsign(rest) if rest.matsize()[0]>0 else None)

import pickle
pickle.dump({'f':f,'B0':[[int(x) for x in b] for b in B0],'vs':[[int(x) for x in v] for v in vs],'zk':[str(z) for z in zk]},open('witt_%s.pkl'%f.replace('^','').replace('*',''),'wb'))
