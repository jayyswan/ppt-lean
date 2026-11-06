# A4-03-chain-degree.py: implicit degree of off_{d_n} o L_{n-1} o ... o off_{d_1}(gamma)
# for gamma a cubic pair.  Practical input for the A4 growth table.
# Method: sample the chain curve at many rational t and fit the lowest-degree implicit
# polynomial by SVD (nullspace of the monomial matrix).  [numeric, 50-digit samples]
import numpy as np
import mpmath as mp
mp.mp.dps = 50

def matmul(A, B):
    return ((A[0][0]*B[0][0]+A[0][1]*B[1][0], A[0][0]*B[0][1]+A[0][1]*B[1][1]),
            (A[1][0]*B[0][0]+A[1][1]*B[1][0], A[1][0]*B[0][1]+A[1][1]*B[1][1]))
def matvec(A, u):
    return (A[0][0]*u[0]+A[0][1]*u[1], A[1][0]*u[0]+A[1][1]*u[1])
def inv2(A):
    det = A[0][0]*A[1][1]-A[0][1]*A[1][0]
    return ((A[1][1]/det, -A[0][1]/det), (-A[1][0]/det, A[0][0]/det))
def J(u): return (-u[1], u[0])

def v(t):  return (3*t**2 + 4*t - 1, 3*t**2 - 1)          # gamma'
def gam(t): return (t**3 + 2*t**2 - t, t**3 - t + 1)       # gamma

I2 = ((mp.mpf(1),mp.mpf(0)),(mp.mpf(0),mp.mpf(1)))
Maps = [((mp.mpf('2'),mp.mpf('1')),(mp.mpf('1'),mp.mpf('3'))),
        ((mp.mpf('3'),mp.mpf('-1')),(mp.mpf('2'),mp.mpf('1'))),
        ((mp.mpf('2'),mp.mpf('-1')),(mp.mpf('1'),mp.mpf('2')))]
Ds   = [mp.mpf('0.5'), mp.mpf('0.7'), mp.mpf('0.4')]

def chain(n, t):
    P = [I2]
    for k in range(n):
        P.append(matmul(Maps[k], P[k]))
    r = matvec(P[n], gam(t))
    for k in range(1, n+1):
        Pk = P[k-1]                       # A_{k-1}
        w = matvec(Pk, v(t))
        Q = w[0]**2 + w[1]**2
        term = matvec(matmul(P[n], inv2(Pk)), J(w))
        r = (r[0] + Ds[k-1]*term[0]/mp.sqrt(Q), r[1] + Ds[k-1]*term[1]/mp.sqrt(Q))
    return r

def fit_degree(n, Nmax=36):
    tvals = [mp.mpf(k)/7 for k in range(-60, 61) if k != 0]
    Xs=[]; Ys=[]
    for tv in tvals:
        Xv,Yv = chain(n,tv)
        Xs.append(Xv); Ys.append(Yv)
    Xs = np.array([float(z) for z in Xs]); Ys = np.array([float(z) for z in Ys])
    xm,xs = Xs.mean(), Xs.std(); ym,ys = Ys.mean(), Ys.std()
    Xs = (Xs-xm)/xs; Ys = (Ys-ym)/ys
    prev = None
    for N in range(1, Nmax+1):
        mons = [(i,j) for i in range(N+1) for j in range(N+1-i)]
        A = np.array([[X**i * Y**j for (i,j) in mons] for X,Y in zip(Xs,Ys)])
        S = np.linalg.svd(A, compute_uv=False)
        rel = S[-1]/S[0]
        if rel < 1e-9:
            return N, rel
    return None, None

for n in (1,2,3):
    N, rel = fit_degree(n, Nmax=36)
    print("chain length n=%d : implicit degree = %s   (min rel. singular value %.2e)" % (n, N, rel))
