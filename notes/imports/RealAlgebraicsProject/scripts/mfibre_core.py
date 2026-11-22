# Session 17 helper for mono.py: fibre system of line -> m = ab, and a random complex line on Q4.
def F(a, m, h):
    b = m / a
    return np.array([a.sum(), b.sum(), (a*a).sum(), (b*b).sum(), (a**4).sum(), (b**4).sum(),
                     (m*a*a).sum(), (m**3/a**2).sum(), h @ a - 1])
def J(a, m, h):
    b = m / a; db = -m / a**2
    return np.array([np.ones(9), db, 2*a, 2*b*db, 4*a**3, 4*b**3*db, 2*m*a, -2*m**3/a**3, h])
def Fl(x, h1, h2):
    a, b = x[:9], x[9:]
    return np.array([a.sum(), b.sum(), (a*a).sum(), (b*b).sum(), (a**4).sum(), (b**4).sum(),
         (a**3*b).sum(), (a*b**3).sum(), 9*((a*b)**2).sum() - ((a*b).sum())**2, h1 @ a - 1, h2 @ b - 1])
def Jl(x, h1, h2):
    a, b = x[:9], x[9:]; z = np.zeros(9); ab = (a*b).sum()
    return np.array([np.r_[np.ones(9), z], np.r_[z, np.ones(9)], np.r_[2*a, z], np.r_[z, 2*b],
         np.r_[4*a**3, z], np.r_[z, 4*b**3], np.r_[3*a*a*b, a**3], np.r_[b**3, 3*a*b*b],
         np.r_[18*a*b*b - 2*ab*b, 18*a*a*b - 2*ab*a], np.r_[h1, z], np.r_[z, h2]])
def random_line(rng):
    h1, h2 = rng.normal(size=9) + 1j*rng.normal(size=9), rng.normal(size=9) + 1j*rng.normal(size=9)
    while True:
        x = rng.normal(size=18) + 1j*rng.normal(size=18)
        for _ in range(80):
            d = np.linalg.lstsq(Jl(x, h1, h2), -Fl(x, h1, h2), rcond=None)[0]; x = x + d
            if np.linalg.norm(d) < 1e-14: break
        if np.linalg.norm(Fl(x, h1, h2)) < 1e-10 and abs((x[:9]*x[9:]).sum()) > 1e-3:
            return x, x[:9]*x[9:]
