#!/usr/bin/env python3
"""Session 52: conics in V_3 through one point Q inside a 5-dimensional linear slice.

n = 9. K (x) C = C^9 coordinatewise; Tr = sum. For the real model of signature r the
coordinates are (x_1..x_r real, z_1, conj z_1, ..., z_s, conj z_s).
V_3 = {p1 = p2 = p3 = 0}. Lambda = span(Q, e_1..e_5) inside {Tr = 0} (a P^5 through Q).
Conics q(k) = Q + k u + k^2 w with u = e_1 + sum_{i=2..5} a_i e_i, w = sum_{i=0..5} b_i e_i
(gauge fixed). Equations: coefficients k^1..k^4 of p2(q) and k^1..k^6 of p3(q): 10 equations,
10 unknowns. Random-start complex Newton; distinct solutions counted.

usage: conic5.py <r> <seed> <starts> [complex]
  r: signature (1,3,5,7,9); 'complex' as 4th arg uses a generic complex Q and Lambda.
Prints the number of distinct nondegenerate conics, the number of real ones and, per real
conic, the trace signature of its plane <Q,u,w> and the real-root count of p4 along it.
"""
import sys, numpy as np

def model(r):
    s = (9 - r) // 2
    return r, s

def realvec(rng, r, s, scale=1.0):
    x = rng.normal(size=r) * scale
    zs = (rng.normal(size=s) + 1j * rng.normal(size=s)) * scale
    out = list(x.astype(complex))
    for z in zs:
        out += [z, np.conj(z)]
    return np.array(out)

def tr(v):
    return v.sum()

def newton_V3(y, real, iters=100):
    for _ in range(iters):
        F = np.array([tr(y), tr(y**2), tr(y**3)])
        if np.max(abs(F)) < 1e-14:
            return y, True
        J = np.array([np.ones_like(y), 2*y, 3*y**2])
        dy = np.linalg.lstsq(J, -F, rcond=None)[0]
        y = y + dy
    return y, np.max(abs(np.array([tr(y), tr(y**2), tr(y**3)]))) < 1e-12

def F_J(z, Q, E):
    # E: list e1..e5 ; unknowns a2..a5 (4), b0..b5 (6)
    a = z[:4]; b = z[4:]
    u = E[0] + sum(a[i]*E[i+1] for i in range(4))
    B = [Q] + list(E)
    w = sum(b[i]*B[i] for i in range(6))
    F = np.array([
        2*tr(Q*u), tr(u*u)+2*tr(Q*w), 2*tr(u*w), tr(w*w),
        3*tr(Q*Q*u), 3*tr(Q*u*u)+3*tr(Q*Q*w), tr(u**3)+6*tr(Q*u*w),
        3*tr(u*u*w)+3*tr(Q*w*w), 3*tr(u*w*w), tr(w**3)])
    J = np.zeros((10, 10), complex)
    for i in range(4):
        e = E[i+1]
        J[:, i] = [2*tr(Q*e), 2*tr(u*e), 2*tr(w*e), 0,
                   3*tr(Q*Q*e), 6*tr(Q*u*e), 3*tr(u*u*e)+6*tr(Q*w*e),
                   6*tr(u*w*e), 3*tr(w*w*e), 0]
    for i in range(6):
        e = B[i]
        J[:, 4+i] = [0, 2*tr(Q*e), 2*tr(u*e), 2*tr(w*e),
                     0, 3*tr(Q*Q*e), 6*tr(Q*u*e), 3*tr(u*u*e)+6*tr(Q*w*e),
                     6*tr(u*w*e), 3*tr(w*w*e)]
    return F, J, u, w

def solve(z, Q, E, iters=80):
    for it in range(iters):
        F, J, u, w = F_J(z, Q, E)
        nF = np.max(abs(F))
        if not np.isfinite(nF) or nF > 1e8:
            return None
        if nF < 1e-13:
            return z
        try:
            dz = np.linalg.solve(J, -F)
        except np.linalg.LinAlgError:
            return None
        lam = 1.0
        while lam > 1e-4:
            z2 = z + lam*dz
            F2 = F_J(z2, Q, E)[0]
            if np.max(abs(F2)) < nF*(1 - 0.25*lam) or nF < 1e-6:
                break
            lam /= 2
        z = z + lam*dz
    F = F_J(z, Q, E)[0]
    return z if np.max(abs(F)) < 1e-10 else None

def polish(z, Q, E):
    for _ in range(5):
        F, J, u, w = F_J(z, Q, E)
        z = z + np.linalg.solve(J, -F)
    return z

def p4_realroots(Q, u, w):
    # p4(q(k)) degree 8 in k
    # coefficients via sampling
    ks = np.linspace(-1, 1, 9)
    vals = [tr((Q + k*u + k*k*w)**4) for k in ks]
    c = np.polyfit(ks, np.array(vals), 8)
    c = np.real_if_close(c, tol=1e6)
    rts = np.roots(np.real(c))
    return int(sum(abs(rt.imag) < 1e-7*max(1, abs(rt)) for rt in rts)), np.real(c)

def plane_sig(Q, u, w):
    V = [Q, u, w]
    G = np.array([[tr(x*y).real for y in V] for x in V])
    ev = np.linalg.eigvalsh(G)
    return int(sum(ev > 1e-9*abs(ev).max())), int(sum(ev < -1e-9*abs(ev).max()))

def main():
    r = int(sys.argv[1]); seed = int(sys.argv[2]); starts = int(sys.argv[3])
    cplx = len(sys.argv) > 4 and sys.argv[4] == 'complex'
    rng = np.random.default_rng(seed)
    r, s = model(r)
    def vec():
        if cplx:
            return rng.normal(size=9) + 1j*rng.normal(size=9)
        return realvec(rng, r, s)
    while True:
        Q, ok = newton_V3(vec(), not cplx)
        if ok and np.min(abs(Q[:, None]-Q[None, :])+np.eye(9)) > 1e-3:
            break
    E = []
    for i in range(5):
        e = vec(); e = e - tr(e)/9
        E.append(e)
    sols = []
    for t in range(starts):
        z0 = (rng.normal(size=10) + 1j*rng.normal(size=10)) * rng.choice([0.3, 1, 3])
        z = solve(z0, Q, E)
        if z is None:
            continue
        z = polish(z, Q, E)
        F, J, u, w = F_J(z, Q, E)
        sv = np.linalg.svd(np.array([Q, u, w]), compute_uv=False)
        if sv[-1] < 1e-8*sv[0]:
            continue
        if np.linalg.cond(J) > 1e12:
            continue
        if not any(np.max(abs(z - z1)) < 1e-7*(1+np.max(abs(z))) for z1 in sols):
            sols.append(z)
        if (t+1) % 200 == 0:
            print(f"starts {t+1}: distinct {len(sols)}", flush=True)
    print(f"r={r} seed={seed} complex={cplx}: distinct nondegenerate conics: {len(sols)}")
    if cplx:
        return
    nreal = 0
    tally = {}
    for z in sols:
        if np.max(abs(z.imag)) < 1e-7*(1+np.max(abs(z))):
            nreal += 1
            F, J, u, w = F_J(z.real.astype(complex), Q, E)
            sig = plane_sig(Q, u, w)
            nr, c = p4_realroots(Q, u, w)
            key = (sig, nr)
            tally[key] = tally.get(key, 0) + 1
            print(f"  real conic: plane sig {sig}, real roots of p4: {nr}, m=Tr(Qw)={tr(Q*w).real:.4f}")
    print(f"real conics: {nreal}; tally (sig, #real p4 roots): {tally}")

if __name__ == '__main__':
    main()
