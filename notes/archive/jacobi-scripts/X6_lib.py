# X6_lib.py -- shared library for the X6 identity hunt.
#
# Convention: mpmath.ellipfun(kind, u, m) and mpmath.ellipf/ellipe(phi, m) take the
# PARAMETER m = c = k^2.  So `c` below is the parameter, not the modulus.
#
# All functions here are meant to be "cheap to construct": each library family is
# justified in NOTES-jacobi-X6.md against a move of pptc/Pptc/Defs.lean.
#
# Rerunnable standalone (imported by the X6-0*.py scripts).

import mpmath as mp

DPS = 100
mp.mp.dps = DPS


# ---------------------------------------------------------------- moduli helpers

def landen(c):
    """Descending Landen parameter c1 = k1^2 with k1 = (1-k')/(1+k'), k'=sqrt(1-c)."""
    kp = mp.sqrt(1 - c)
    k1 = (1 - kp) / (1 + kp)
    return k1 * k1


def sqrt1m(c):
    return mp.sqrt(1 - c)


# ---------------------------------------------------------------- elliptic pieces

def F(phi, c):
    """Incomplete first kind, parameter c."""
    return mp.ellipf(phi, c)


def E(phi, c):
    """Incomplete second kind, parameter c."""
    return mp.ellipe(phi, c)


def K(c):
    return mp.ellipk(c)


def Ecomp(c):
    return mp.ellipe(c)


def EAm(u, c):
    """Inverse of E(.,c): unique phi real with E(phi,c) = u (E is strictly increasing).

    Bracket: E(phi) <= phi and E(phi) >= phi*sqrt(1-c) for phi>=0, so u <= phi <= u/sqrt(1-c).
    """
    if c == 0:
        return u
    f = lambda phi: mp.ellipe(phi, c) - u
    lo = u
    hi = u / mp.sqrt(1 - c) + mp.mpf(1)
    # widen slightly to be safe against rounding at the boundary
    return mp.findroot(f, (lo, hi), tol=mp.mpf(10) ** (-(DPS - 5)))


def am(u, c):
    """Jacobi amplitude for 0 <= u <= K(c): principal branch via asin(sn)."""
    s = mp.ellipfun('sn', u, c)
    return mp.asin(s)


# ---------------------------------------------------------------- the library L(u)

def library(u, c):
    """Ordered dict name -> value of the depth<=2 library at (u, c).

    Entries that are undefined on the real principal branch are returned as None
    (the caller decides whether to drop or mask them).
    """
    c = mp.mpf(c)
    u = mp.mpf(u)
    L = {}
    k = mp.sqrt(c)
    c1 = 1 - c
    cl = landen(c)

    # --- elementary functions of u (number ops; sin/cos/2^/log/arccos black boxes)
    L['u'] = u
    L['u2'] = u * u
    L['sqrt_u'] = mp.sqrt(u) if u >= 0 else None
    L['sin_u'] = mp.sin(u)
    L['cos_u'] = mp.cos(u)
    L['tan_u'] = mp.tan(u)
    L['twou'] = mp.power(2, u)
    L['log_u'] = mp.log(u) if u > 0 else None
    L['arccos_u'] = mp.acos(u) if -1 <= u <= 1 else None
    L['pi'] = mp.pi

    # --- forward incomplete Legendre integrals at the ANGLE u
    L['F_u_c'] = F(u, c)
    L['E_u_c'] = E(u, c)
    L['F_u_c1'] = F(u, c1)
    L['E_u_c1'] = E(u, c1)
    L['F_u_cl'] = F(u, cl)
    L['E_u_cl'] = E(u, cl)

    # --- E-inverses (ellipticEAm, a known P-constructible inverse)
    L['EAm_u_c'] = EAm(u, c)
    L['EAm_u_c1'] = EAm(u, c1)
    L['EAm_u_cl'] = EAm(u, cl)

    # --- constants from c
    L['K_c'] = K(c)
    L['E_c'] = Ecomp(c)
    L['K_c1'] = K(c1)
    L['E_c1'] = Ecomp(c1)
    L['K_cl'] = K(cl)
    L['E_cl'] = Ecomp(cl)

    # --- depth 2: elementary of (forward integral)
    try:
        L['sinF'] = mp.sin(F(u, c))
        L['cosF'] = mp.cos(F(u, c))
        L['sinE'] = mp.sin(E(u, c))
        L['cosE'] = mp.cos(E(u, c))
        L['sqrtF'] = mp.sqrt(F(u, c)) if F(u, c) >= 0 else None
        L['sqrtE'] = mp.sqrt(E(u, c)) if E(u, c) >= 0 else None
        L['twoF'] = mp.power(2, F(u, c))
    except Exception:
        pass

    # --- depth 2: elliptic of elliptic
    try:
        L['EE'] = E(E(u, c), c)
        L['FF'] = F(F(u, c), c)
        L['EF'] = E(F(u, c), c)
        L['FE'] = F(E(u, c), c)
    except Exception:
        pass
    try:
        L['EAmE'] = EAm(E(u, c), c)      # calibration: should equal u
        L['EAmF'] = EAm(F(u, c), c)
    except Exception:
        pass

    # --- depth 2: elliptic of elementary
    try:
        L['Fsin'] = F(mp.sin(u), c)
        L['Esin'] = E(mp.sin(u), c)
        L['Fcos'] = F(mp.cos(u), c)
        L['Ecos'] = E(mp.cos(u), c)
    except Exception:
        pass

    # --- depth 2: moving-modulus complete integrals (parameter depends on u)
    try:
        L['K_cpow'] = K(mp.power(c, u))     # c^u in (0,1) for 0<c<1,u>0
        L['E_cpow'] = Ecomp(mp.power(c, u))
    except Exception:
        pass
    if c * u < 1:
        L['K_cu'] = K(c * u)
        L['E_cu'] = Ecomp(c * u)
    else:
        L['K_cu'] = None
        L['E_cu'] = None

    # --- depth 2: arc length of y = u*sin x over [0, pi/2]  = sqrt(1+u^2) E(m),
    #     m = u^2/(1+u^2).  [symbolic]
    m = u * u / (1 + u * u)
    L['arcL'] = mp.sqrt(1 + u * u) * Ecomp(m)

    L['sqrt_sin_u'] = mp.sqrt(mp.sin(u)) if mp.sin(u) >= 0 else None
    return L


def targets(u, c):
    """The four targets plus the periodic part of am at (u, c)."""
    c = mp.mpf(c)
    u = mp.mpf(u)
    sn = mp.ellipfun('sn', u, c)
    cn = mp.ellipfun('cn', u, c)
    dn = mp.ellipfun('dn', u, c)
    a = mp.asin(sn)
    return {
        'am': a,
        'sn': sn,
        'cn': cn,
        'dn': dn,
        'am_periodic': a - u * mp.pi / (2 * K(c)),
    }


# ---------------------------------------------------------------- search spaces

# Core library names used in the fixed-u PSLQ and the linear grid fit.
CORE = [
    'u', 'u2', 'sqrt_u', 'sin_u', 'cos_u', 'tan_u', 'twou', 'log_u', 'arccos_u',
    'F_u_c', 'E_u_c', 'F_u_c1', 'E_u_c1', 'F_u_cl', 'E_u_cl',
    'EAm_u_c', 'EAm_u_c1', 'EAm_u_cl',
    'K_c', 'E_c', 'K_c1', 'E_c1', 'K_cl', 'E_cl',
    'sinF', 'cosF', 'sinE', 'cosE', 'sqrtF', 'sqrtE', 'twoF',
    'EE', 'FF', 'EF', 'FE', 'EAmE', 'EAmF',
    'Fsin', 'Esin', 'Fcos', 'Ecos',
    'K_cpow', 'E_cpow', 'K_cu', 'E_cu',
    'arcL', 'sqrt_sin_u', 'pi',
]

# A shorter "prime suspects" list for combinatorial subset PSLQ and pair fits.
PRIME = [
    'u', 'sqrt_u', 'sin_u', 'cos_u', 'twou', 'log_u',
    'F_u_c', 'E_u_c', 'F_u_c1', 'E_u_c1',
    'EAm_u_c', 'EAm_u_c1', 'arcL', 'K_c', 'E_c', 'K_c1',
]

# Reduced 10-entry list used for the (expensive) size-3 subset PSLQ.
PRIME3 = [
    'u', 'sin_u', 'cos_u', 'F_u_c', 'E_u_c',
    'F_u_c1', 'E_u_c1', 'EAm_u_c', 'arcL', 'K_c',
]

MODULI = {
    '1/2': mp.mpf(1) / 2,
    '1/3': mp.mpf(1) / 3,
    '(r2-1)^2': (mp.sqrt(2) - 1) ** 2,
    '0.7': mp.mpf(7) / 10,
}

# primary u values from the brief; extra ones for the 5-fold re-test
U_PRIMARY = [mp.mpf(1) / 2, mp.mpf(1), mp.mpf(3) / 2]
U_RETEST = [mp.mpf(3) / 10, mp.mpf(7) / 10, mp.mpf(9) / 10,
            mp.mpf(6) / 5, mp.mpf(7) / 5]
U_ALL = U_PRIMARY + U_RETEST


if __name__ == '__main__':
    c = mp.mpf(1) / 2
    L = library(mp.mpf('0.7'), c)
    print("library size:", len(L))
    for name in CORE:
        v = L.get(name)
        print(f"  {name:12s} {mp.nstr(v, 25) if v is not None else 'None'}")
    print("targets:", {k: mp.nstr(v, 25) for k, v in targets(mp.mpf('0.7'), c).items()})
