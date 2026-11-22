#!/usr/bin/env python3
"""Session 52: conics through a point Q of V_S = {Tr y = 0, p_k(y) = 0 for k in S} (n = 9),
where the conic family through a general point is finite (e.g. S = {3,4}: V_{134}).

Conic q(k) = Q + k u + k^2 w, Tr u = Tr w = 0, gauge l0(u) = 0, l1(u) = 1.
Equations: coefficients k^1 .. k^{2d} of p_d(q(k)) for d in S.
Unknowns: 7 - 2 = 6 for u... (u: 9 - 1 - 2 = 6, w: 8) = 14 for S = {3,4}.

usage: conicV.py <S e.g. 3,4> <r> <seed> <starts> [complex] [last]
  'complex' -> generic complex Q; otherwise the real model R^r x C^s.
  last: the power sum to evaluate on real conics (default 2): prints its real-root count.
"""
import sys, numpy as np

def realvec(rng, r):
    s = (9 - r)//2
    x = rng.normal(size=r).astype(complex)
    out = list(x)
    for z in rng.normal(size=s) + 1j*rng.normal(size=s):
        out += [z, np.conj(z)]
    return np.array(out)

def powcoef(q, d):
    # q: (9,3) coefficient arrays (const, k, k^2); returns (9, 2d+1) coefficients of q_i^d
    out = np.ones((q.shape[0], 1), complex)
    for _ in range(d):
        out = np.array([np.convolve(o, qq) for o, qq in zip(out, q)])
    return out

def setup(S, rng, cplx, r):
    vec = (lambda: rng.normal(size=9)+1j*rng.normal(size=9)) if cplx else (lambda: realvec(rng, r))
    for attempt in range(200):
        y = vec()
        for _ in range(100):
            F = np.array([y.sum()] + [np.sum(y**d) for d in S])
            J = np.array([np.ones(9)] + [d*y**(d-1) for d in S])
            y = y + np.linalg.lstsq(J, -F, rcond=None)[0]
        F = np.array([y.sum()] + [np.sum(y**d) for d in S])
        if np.max(abs(F)) < 1e-12 and np.min(abs(y[:, None]-y[None, :])+np.eye(9)) > 1e-3:
            return y
    raise SystemExit("no base point")

def build(S, Q, rng, cplx, r):
    vec = (lambda: rng.normal(size=9)+1j*rng.normal(size=9)) if cplx else (lambda: realvec(rng, r).real if r == 9 else realvec(rng, r))
    # real functionals in the real model: use l(y) = Re-structured -> take l = Tr(c*y) with c real element
    c0 = vec(); c1 = vec()
    l0 = lambda y: np.sum(c0*y); l1 = lambda y: np.sum(c1*y)
    # affine param of u: Tr u = 0, l0(u) = 0, l1(u) = 1
    A = np.array([np.ones(9), c0, c1])
    rhs = np.array([0, 0, 1.0])
    u0 = np.linalg.lstsq(A, rhs, rcond=None)[0]
    Nu = null(A)
    Nw = null(np.ones((1, 9)))
    if not cplx:
        # real bases: make columns real elements of the model
        Nu = realify(Nu, r); Nw = realify(Nw, r); u0 = realify(u0[:, None], r)[:, 0] if False else u0
    return u0, Nu, Nw

def null(A):
    u, s, vh = np.linalg.svd(A)
    rk = int(sum(s > 1e-12*s[0]))
    return vh[rk:].conj().T

def realify(N, r):
    return N  # complex basis is fine: reality is tested on the conic itself

def F_J(z, S, Q, u0, Nu, Nw):
    nu = Nu.shape[1]
    u = u0 + Nu @ z[:nu]; w = Nw @ z[nu:]
    q = np.stack([Q, u, w], axis=1)
    Fs = []; Js = []
    for d in S:
        qd1 = powcoef(q, d-1)            # (9, 2d-1)
        qd = np.array([np.convolve(a, b) for a, b in zip(qd1, q)])  # (9, 2d+1)
        Fs.append(qd.sum(0)[1:])
        # derivatives
        du = np.zeros((2*d, 9), complex); dw = np.zeros((2*d, 9), complex)
        for i in range(9):
            cu = d*np.convolve(qd1[i], [0, 1])  # length 2d
            cw = d*np.convolve(qd1[i], [0, 0, 1])
            du[:, i] = cu[1:2*d+1] if len(cu) >= 2*d+1 else np.pad(cu, (0, 2*d+1-len(cu)))[1:]
            dw[:, i] = cw[1:2*d+1]
        Js.append(np.hstack([du @ Nu, dw @ Nw]))
    return np.concatenate(Fs), np.vstack(Js), u, w

def newton(z, *args, iters=80):
    for _ in range(iters):
        F, J, u, w = F_J(z, *args)
        nF = np.max(abs(F))
        if not np.isfinite(nF) or nF > 1e10:
            return None
        if nF < 1e-12:
            break
        try:
            dz = np.linalg.solve(J, -F)
        except np.linalg.LinAlgError:
            return None
        lam = 1.0
        while lam > 1e-4:
            if np.max(abs(F_J(z+lam*dz, *args)[0])) < nF*(1-0.25*lam) or nF < 1e-6:
                break
            lam /= 2
        z = z + lam*dz
    F, J, u, w = F_J(z, *args)
    if np.max(abs(F)) > 1e-9:
        return None
    for _ in range(3):
        z = z + np.linalg.solve(J, -F); F, J, u, w = F_J(z, *args)
    return z

def main():
    S = [int(t) for t in sys.argv[1].split(',')]
    r = int(sys.argv[2]); seed = int(sys.argv[3]); starts = int(sys.argv[4])
    cplx = len(sys.argv) > 5 and sys.argv[5] == 'complex'
    last = int(sys.argv[6]) if len(sys.argv) > 6 else 2
    rng = np.random.default_rng(seed)
    Q = setup(S, rng, cplx, r)
    u0, Nu, Nw = build(S, Q, rng, cplx, r)
    args = (S, Q, u0, Nu, Nw)
    nunk = Nu.shape[1] + Nw.shape[1]; neq = sum(2*d for d in S)
    print(f"S={S} unknowns {nunk} equations {neq}", flush=True)
    sols = []; us = []
    for t in range(starts):
        z0 = (rng.normal(size=nunk)+1j*rng.normal(size=nunk))*rng.choice([0.3, 1, 3])
        z = newton(z0, *args)
        if z is None:
            continue
        F, J, u, w = F_J(z, *args)
        sv = np.linalg.svd(np.array([Q, u, w]), compute_uv=False)
        if sv[-1] < 1e-7*sv[0] or np.linalg.cond(J) > 1e12:
            continue
        # canonical conic data independent of gauge: (u, w) already gauge-fixed
        if not any(np.max(abs(z-z1)) < 1e-6*(1+np.max(abs(z))) for z1 in sols):
            sols.append(z); us.append((u, w))
        if (t+1) % 200 == 0:
            print(f"starts {t+1}: distinct {len(sols)}", flush=True)
    print(f"S={S} r={r} seed={seed} complex={cplx}: distinct nondegenerate conics: {len(sols)}")
    if cplx:
        return
    s = (9-r)//2
    def isreal(v):
        x = v[:r]; zz = v[r:]
        return np.max(abs(x.imag)) < 1e-7*(1+np.max(abs(v))) and np.max(abs(zz[0::2]-np.conj(zz[1::2]))) < 1e-7*(1+np.max(abs(v)))
    tally = {}
    for (u, w) in us:
        if isreal(u) and isreal(w):
            G = np.array([[np.sum(a*b).real for b in (Q, u, w)] for a in (Q, u, w)])
            ev = np.linalg.eigvalsh(G); sig = (int(sum(ev > 0)), int(sum(ev < 0)))
            ks = np.linspace(-1, 1, 2*last+1)
            vals = [np.sum((Q+k*u+k*k*w)**last).real for k in ks]
            c = np.polyfit(ks, vals, 2*last)
            rts = np.roots(c); nr = int(sum(abs(x.imag) < 1e-7*max(1, abs(x)) for x in rts))
            tally[(sig, nr)] = tally.get((sig, nr), 0) + 1
            print(f"  real conic: plane sig {sig}, real roots of p{last}: {nr}")
    print(f"real conics: {sum(tally.values())}; tally (plane sig, #real roots of p{last}): {tally}")

if __name__ == '__main__':
    main()
