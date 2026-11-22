"""Session 31: the unique cubic C through the 9 points of C_b^gen, decomposed as
C = H + Delta*l (H harmonic). Look for consistently vanishing invariants."""
import numpy as np, itertools
exec(open('pen_sing.py').read().split("Delta=lambda")[0])
from numpy.polynomial import polynomial as Pl
Delta=lambda x: x[1]**2-4*x[0]*x[2]
def ev(coef,x): return sum(c*np.prod(x**np.array(e)) for c,e in zip(coef,mon))
# basis of Delta*linear as cubic coefficient vectors
def cubic_coeffs(f):
    xs=np.random.default_rng(5).normal(size=(20,3))
    A=np.array([[np.prod(x**np.array(e)) for e in mon] for x in xs])
    return np.linalg.lstsq(A,np.array([f(x) for x in xs]),rcond=None)[0]
DL=np.array([cubic_coeffs(lambda x,k=k: Delta(x)*x[k]) for k in range(3)])
# harmonic basis: kernel of lap (3 x 10)
Lmat=np.array([lap(np.eye(10)[j]) for j in range(10)]).T
Hb=np.linalg.svd(Lmat)[2][3:]
Ainv=np.array([[0,0,-.5],[0,1,0],[-.5,0,0]])  # dual form of Delta (up to scale)
rows=[]
for Q,lb in zip(Qs,lab):
    if lb!='gen': continue
    C=cubic_of(Q,False)
    co=np.linalg.lstsq(np.vstack([Hb,DL]).T,C,rcond=None)[0]
    H=co[:7]@Hb; l=co[7:]
    Hs=sings(H,25)
    pole=Ainv@l
    sx=np.zeros(7)
    for c,e in zip(C,mon):
        t=Pl.polymul(Pl.polypow([0,-2],e[1]),Pl.polypow([0,0,1],e[2])); sx[:len(t)]+=c*t
    r=np.roots(sx[::-1]); sep=min(abs(a-b) for a,b in itertools.combinations(r,2))/max(1,abs(r).max())
    rows.append((len(Hs), l@Ainv@l/(l@l), ev(C,pole)/np.linalg.norm(C)/np.linalg.norm(pole)**3, ev(H,pole)/np.linalg.norm(H)/np.linalg.norm(pole)**3, sep))
R=np.array(rows,dtype=float)
print('n sing pts of harmonic part:',np.bincount(R[:,0].astype(int)))
for j,nm in enumerate(['l tangent to Delta (l*A^-1*l)','C(pole of l)','H(pole of l)','min root sep of C|Delta'],1):
    v=np.abs(R[:,j]); print(nm,' min %.2e  median %.2e'%(v.min(),np.median(v)))
