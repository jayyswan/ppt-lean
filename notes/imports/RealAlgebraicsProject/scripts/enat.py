# test natural candidate points of E (T-orthogonal projections to L of products of Q1, Q2)
import numpy as np
exec(open('conic12.py').read().split("\nif __name__ == '__main__'")[0])
rng=np.random.default_rng(5)
Q1=v3_point(rng); Q2=v3_point(rng); D=setup(Q1,Q2)
Lb=D['Lb']; G=Lb.T@Lb   # trace form on L (complex bilinear)
def projL(x):  # T-orthogonal projection onto L: c with Lb^T (x - Lb c) = 0
    return np.linalg.solve(G, Lb.T@x)
one=np.ones(9)
cands={'Q1Q2':Q1*Q2,'Q1^2Q2':Q1**2*Q2,'Q1Q2^2':Q1*Q2**2,'Q1^3':Q1**3,'Q2^3':Q2**3,'Q1^2Q2^2':Q1**2*Q2**2,
 'Q1^3-Q2^3':Q1**3-Q2**3,'Q1^2+Q2^2':Q1**2+Q2**2,'(Q1-Q2)^3':(Q1-Q2)**3,'Q1^4':Q1**4,'Q1Q2(Q1-Q2)':Q1*Q2*(Q1-Q2)}
for k,x in cands.items():
    c=projL(x); c=c/np.linalg.norm(c)
    F,_=fsys(D,c)
    print(f'{k:14s} |G1|,|G2| = {abs(F[0]):.2e} {abs(F[1]):.2e}   |H| = {abs(F[2]):.2e}')
