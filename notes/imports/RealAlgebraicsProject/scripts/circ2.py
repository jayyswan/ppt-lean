# Track the labelled configuration around the circle |s - s0| = rho on the line c = c0 + s d.
# Output: winding number of D(s) = prod_{i<j} (g_i-g_j)^2 and the monodromy permutation of the nine sheets.
import numpy as np, pickle, sys, os
BASE=os.environ.get('BASE','base.pkl')
from bl import *
def pairs_phase(g):
    return np.array([g[i]-g[j] for i in range(9) for j in range(i+1,9)])
def perm_of(gs, ge):
    # labelled sheets: points tracked continuously; compare final labelled Gram with the start one
    sig=[]
    for i in range(9):
        j=int(np.argmin(abs(gs-ge[i]))); sig.append(j)
    return sig
def circle(Y, c0, d, s0, rho, n=64):
    th=np.linspace(0,2*np.pi,n+1); ss=s0+rho*np.exp(1j*th)
    # go from s0 radially? caller ensures Y is at s0+rho
    G0=gram(Y); g0=np.diag(G0); prev=pairs_phase(g0); tot=0.0; k=0
    pts=[ss[0]]
    while k<n:
        a,b=ss[k],ss[k+1]; sub=[a,b]
        # adaptive subdivision so every pair's phase moves < 0.5
        Yn=track(Y,[c0+a*d,c0+b*d])
        if Yn is None: return None
        cur=pairs_phase(np.diag(gram(Yn))); dph=np.angle(cur/prev)
        if np.abs(dph).max()>0.5 and abs(b-a)>1e-6:
            # insert midpoint
            m=s0+rho*np.exp(1j*(th[k]+th[k+1])/2); th=np.insert(th,k+1,(th[k]+th[k+1])/2); ss=np.insert(ss,k+1,m); n+=1; continue
        tot+=2*dph.sum(); prev=cur; Y=Yn; k+=1
    G1=gram(Y)
    # permutation: label i ends at position of start label sig[i]
    sig=[]
    for i in range(9):
        j=int(np.argmin(np.abs(np.diag(G0)-G1[i,i]))); sig.append(j)
    ok = len(set(sig))==9 and np.abs(G1-G0[np.ix_(sig,sig)]).max()<1e-6
    return Y, tot/(2*np.pi), sig if ok else None
def cycle_type(sig):
    seen=set(); ct=[]
    for i in range(9):
        if i in seen: continue
        j=i; L=0
        while j not in seen: seen.add(j); j=sig[j]; L+=1
        ct.append(L)
    return sorted(ct,reverse=True)
if __name__=='__main__':
    Y0,c0,d=pickle.load(open(BASE,'rb'))
    Y=Y0; s=0
    for rho in [float(r) for r in sys.argv[1:]]:
        Y=track(Y,[c0+s*d,c0+rho*d]); s=rho
        out=circle(Y,c0,d,0,rho)
        if out is None: print(rho,'fail'); continue
        Y,w,sig=out; print('rho',rho,'winding %.3f'%w,'perm',sig,'type',cycle_type(sig) if sig else None,flush=True)
