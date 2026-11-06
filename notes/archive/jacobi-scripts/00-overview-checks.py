from mpmath import mp, mpf, sqrt, quad, diff, cos, sin, atan2, ellipf, asin
mp.dps = 30

# 1. Lemniscate (x^2+y^2)^2 = x^2 - y^2 is RATIONAL: x=t(1+t^2)/(1+t^4), y=t(1-t^2)/(1+t^4)
X = lambda t: t*(1+t**2)/(1+t**4); Y = lambda t: t*(1-t**2)/(1+t**4)
t = mpf('0.37')
print('lemniscate on curve:', (X(t)**2+Y(t)**2)**2 - (X(t)**2-Y(t)**2))
print('lemniscate speed^2*(1+t^4)/2 :', (diff(X,t)**2+diff(Y,t)**2)*(1+t**4)/2)

# 2. y = x^3: s(x) = x sqrt(1+9x^4)/3 + (2/3) int_0^x dx/sqrt(1+9x^4)
x = mpf('0.8')
s = quad(lambda u: sqrt(1+9*u**4), [0, x])
rhs = x*sqrt(1+9*x**4)/3 + mpf(2)/3*quad(lambda u: 1/sqrt(1+9*u**4), [0, x])
print('cubic identity residual:', s - rhs)

# 3. affine-after-offset speed formula:
#    base v(t); offset by d; then linear map A.
#    claimed speed = sqrt(Q_A(v)) * (1 - d*(v x v')/|v|^3)
b, d = mpf('0.6'), mpf('0.25')
A = [[mpf('1.7'), mpf('0.3')], [mpf('-0.2'), mpf('0.9')]]
g = lambda t: (sin(t), b*cos(t))
def off(t):
    vx, vy = diff(lambda s: g(s)[0], t), diff(lambda s: g(s)[1], t)
    n = sqrt(vx**2+vy**2)
    # unit normal = rotate tangent by +90deg: (-vy, vx)/n
    return (g(t)[0] - d*vy/n, g(t)[1] + d*vx/n)
def Aoff(t):
    p = off(t); return (A[0][0]*p[0]+A[0][1]*p[1], A[1][0]*p[0]+A[1][1]*p[1])
t = mpf('0.9')
sp = sqrt(diff(lambda s: Aoff(s)[0], t)**2 + diff(lambda s: Aoff(s)[1], t)**2)
vx, vy = cos(t), -b*sin(t)
ax, ay = -sin(t), -b*cos(t)
cross = vx*ay - vy*ax
Av = (A[0][0]*vx+A[0][1]*vy, A[1][0]*vx+A[1][1]*vy)
claim = sqrt(Av[0]**2+Av[1]**2) * abs(1 - d*cross/(vx**2+vy**2)**mpf(1.5))
print('scaled-offset speed residual:', sp - claim)
