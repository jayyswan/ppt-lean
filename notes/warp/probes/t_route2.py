from mpmath import mp, mpf, quad, sqrt, asinh
mp.dps = 30
for a in [mpf('0.45977'), mpf('0.2'), mpf('0.56338'), mpf('0.05')]:
    s = 3*a/2
    Q = lambda Z: 1 + s**2*(Z**2 - mpf(7)/4)**2
    q4 = s**2; q2 = -2*s**2*mpf(7)/4; q0 = 1 + s**2*mpf(49)/16
    c2 = q2/3; c0 = 2*q0/3
    Z0, Z1 = mpf(-3)/2, mpf(-1)/2          # X in [0,1]
    J = quad(lambda Z: sqrt(Q(Z)), [Z0, Z1])
    alg = (Z1*sqrt(Q(Z1)) - Z0*sqrt(Q(Z0)))/3
    F = quad(lambda Z: 1/sqrt(Q(Z)), [Z0, Z1])
    Z2 = quad(lambda Z: Z**2/sqrt(Q(Z)), [Z0, Z1])
    print(a, 'J-decomp residual', J - alg - c0*F - c2*Z2, ' Ehat coeff c2 =', c2)
    # parabola bottom: g' = (3a/2)(1-2X), J_B = int sqrt(1+k^2 (1-2X)^2), k=3a/2
    k = 3*a/2
    JB = quad(lambda X: sqrt(1+k**2*(1-2*X)**2), [0, 1])
    # closed form: (1/(2k))[ t sqrt(1+t^2)/2*... ] check
    t = k
    closed = (t*sqrt(1+t**2) + asinh(t))/(2*k)
    print('  parabola J_B', JB, closed, ' log coeff =', 1/(2*k))
