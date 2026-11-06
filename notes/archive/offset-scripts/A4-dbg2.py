import sympy as sp
t,d,X,Y=sp.symbols('t d X Y',real=True)
# (a) clean cubic graph y=t^3, offset by d: known implicit degree should be 10
x=t; y=t**3; w=sp.sqrt(1+9*t**4)
Xr=x-3*d*t**2/w; Yr=y+d/w
nX,dX=sp.fraction(sp.together(Xr)); nY,dY=sp.fraction(sp.together(Yr))
# clear sqrt: use (X-x)^2+(Y-y)^2=d^2 and (X-x)x'+(Y-y)y'=0 instead
E1=sp.expand((X-x)**2+(Y-y)**2-d**2)   # degree 6 in t
E2=sp.expand((X-x)*sp.diff(x,t)+(Y-y)*sp.diff(y,t))  # degree 3+2=5
R=sp.factor(sp.resultant(E1,E2,t))
P=sp.Poly(R,X,Y)
print("cubic graph offset implicit degree:", P.total_degree())
print("factor count:", len(sp.factor_list(R)[1]))

# (b) test chain construction clearance before applying L.
import mpmath as mp
mp.mp.dps=40
import numpy as np
def matmul(A,B): return ((A[0][0]*B[0][0]+A[0][1]*B[1][0],A[0][0]*B[0][1]+A[0][1]*B[1][1]),(A[1][0]*B[0][0]+A[1][1]*B[1][0],A[1][0]*B[0][1]+A[1][1]*B[1][1]))
def matvec(A,u): return (A[0][0]*u[0]+A[0][1]*u[1],A[1][0]*u[0]+A[1][1]*u[1])
def J(u): return (-u[1],u[0])
def v(t): return (3*t**2+4*t-1,3*t**2-1)
def gam(t): return (t**3+2*t**2-t,t**3-t+1)
M1=((mp.mpf(2),mp.mpf(1)),(mp.mpf(1),mp.mpf(3)))
for tv in [mp.mpf('0.3'),mp.mpf('1.1')]:
    wv=v(tv); Q=wv[0]**2+wv[1]**2; nrm=J(wv)
    u=(gam(tv)[0]+mp.mpf('0.5')*nrm[0]/mp.sqrt(Q), gam(tv)[1]+mp.mpf('0.5')*nrm[1]/mp.sqrt(Q))
    r=matvec(M1,u)
    # inverse map
    Minv=((mp.mpf(3)/5,-mp.mpf(1)/5),(-mp.mpf(1)/5,mp.mpf(2)/5))
    ub=matvec(Minv,r); g=gam(tv)
    print("clearance:",float(mp.sqrt((ub[0]-g[0])**2+(ub[1]-g[1])**2)),
          " orth:",float((ub[0]-g[0])*wv[0]+(ub[1]-g[1])*wv[1]))
