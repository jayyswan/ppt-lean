import mpmath as mp, numpy as np, os
mp.mp.dps = 60

def f(t):  return t**7 - 14*t**5 + 49*t**3 - 36*t + 1
def fp(t): return 7*t**6 - 70*t**4 + 147*t**2 - 36

seedr = np.roots([1,0,-14,0,49,0,-36,1]).real
rts=[]
for x0 in seedr:
    x=mp.mpf(repr(float(x0)))
    for _ in range(60):
        x = x - f(x)/fp(x)
    rts.append(x)
rts=sorted(rts)

def residual(z):
    a,b,c,p,q,rr,D = z
    return [ (lambda t: ((t**3+a*t**2+b*t+c)**2)*(((3*t**2+2*a*t+b)**2)+((2*p*t+q)**2)) - D*(p*t**2+q*t+rr)**2)(t) for t in rts ]

def jac_analytic(z):
    a,b,c,p,q,rr,D = z
    J=mp.zeros(7,7)
    for i,t in enumerate(rts):
        u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vp=2*p*t+q; vv=p*t**2+q*t+rr
        S=up*up+vp*vp
        J[i,0]=2*u*(t**2)*S+u*u*(4*up*t)
        J[i,1]=2*u*t*S+u*u*(2*up)
        J[i,2]=2*u*S
        J[i,3]=u*u*(4*vp*t)-D*(2*vv*t*t)
        J[i,4]=u*u*(2*vp)-D*2*vv*t
        J[i,5]=-D*(2*vv)
        J[i,6]=-vv*vv
    return J

def jac_fd(z,h=mp.mpf('1e-25')):
    J=mp.zeros(7,7)
    F0=mp.matrix(residual(z))
    for k in range(7):
        zp=list(z); zp[k]=z[k]+h
        F1=mp.matrix(residual(zp))
        for i in range(7):
            J[i,k]=(F1[i]-F0[i])/h
    return J

# solution 0 and solution 1 seeds
sols = np.load(r"archived files/septic-scripts/all-solutions.npy")
for si in [0,1,3]:
    z=[mp.mpf(repr(float(x))) for x in sols[si]]
    for _ in range(40):
        F=mp.matrix(residual(z))
        if max(abs(v) for v in F) < mp.mpf('1e-50'): break
        z=[z[k]-mp.lu_solve(jac_analytic(z),F)[k] for k in range(7)]
    F=mp.matrix(residual(z))
    print("sol",si,"resid",mp.nstr(max(abs(v) for v in F),5))
    Ja=jac_analytic(z); Jf=jac_fd(z)
    diff=max(abs(Ja[i,j]-Jf[i,j]) for i in range(7) for j in range(7))
    scale=max(abs(Ja[i,j]) for i in range(7) for j in range(7))
    print("   max|Ja-Jf|=",mp.nstr(diff,4),"scale=",mp.nstr(scale,4))
    print("   sing vals:", [mp.nstr(s,6) for s in mp.svd(Ja)[1]])
