#!/usr/bin/env python3
"""Session 65: singularities of Vbar = {p1 = p3 = p5 = 0} in P^9 (the common
geometric model of V_K (nonics, K x Q) and W_K (decics)).

Modes
  hess <trials> <seed>   type 1: generic point a*e_A + b*e_B of a singular line;
                         rank of the Hessian of L = p5 - lam*p3 - mu*p1 (grad L = 0
                         at y) on T = ker dp1 ∩ ker dp3 (dim 8); expected 6
                         (transversal ordinary double point, radical = line span).
  type3                  type 3: tangent cone at e = (1^5, (-1)^5): Y = {sum z = 0,
                         z1 = 0, sum e_i z_i^2 = 0, sum z_i^3 = 0} in P^9 (a (2,3)
                         complete intersection 5-fold in P^7); Singular: dim, degree
                         and dimension / degree of Sing(Y).
  type2 <z>              type 2 (y = e_B, z zero coordinates): the cubic
                         C = {sum u = 0, sum u^3 = 0} in P^{z-1}; dim/deg of Sing(C).
  vbar <seed> [p]        Sing(Vbar) on a random hyperplane section mod p: dimension
                         and degree (expected: 0-dimensional, = #lines meeting it).
"""
import sys, subprocess, itertools
import numpy as np

def run_sing(src):
    r = subprocess.run(['Singular', '-q'], input=src, capture_output=True, text=True, timeout=3000)
    return r.stdout + r.stderr

def hess(trials, seed):
    rng = np.random.default_rng(seed)
    out = []
    for t in range(trials):
        k = rng.integers(1, 5)            # pairs carrying the value a
        perm = rng.permutation(10)
        y = np.zeros(10)
        a, b = rng.normal(), rng.normal()
        for j in range(k):
            y[perm[2*j]], y[perm[2*j+1]] = a, -a
        for j in range(k, 5):
            y[perm[2*j]], y[perm[2*j+1]] = b, -b
        g1, g3, g5 = np.ones(10), 3*y**2, 5*y**4
        # solve g5 = lam*g3 + mu*g1
        M = np.stack([g3, g1], 1)
        (lam, mu), res, *_ = np.linalg.lstsq(M, g5, rcond=None)
        resid = np.linalg.norm(M @ np.array([lam, mu]) - g5)
        H = np.diag(20*y**3 - 6*lam*y)
        J = np.stack([g1, g3])
        _, s, Vt = np.linalg.svd(J)
        T = Vt[2:].T                       # 10 x 8 basis of ker
        HT = T.T @ H @ T
        ev = np.linalg.eigvalsh(HT)
        rank = int(np.sum(np.abs(ev) > 1e-8*max(1, np.abs(ev).max())))
        # radical contains the line directions e_A, e_B ?
        eA = np.where(np.abs(y - a) < 1e-12, 1., 0) - np.where(np.abs(y + a) < 1e-12, 1., 0)
        eB = np.where(np.abs(y - b) < 1e-12, 1., 0) - np.where(np.abs(y + b) < 1e-12, 1., 0)
        rad = max(np.linalg.norm(T.T @ H @ eA), np.linalg.norm(T.T @ H @ eB))
        out.append((k, rank, resid, rad))
        print(f"trial {t}: k={k} resid={resid:.1e} rank(Hess|T)={rank} |H e_A|,|H e_B| on T={rad:.1e}")
    print("ranks:", sorted(set(o[1] for o in out)))

def type3():
    e = [1]*5 + [-1]*5
    v = ','.join(f'z{i}' for i in range(10))
    q = '+'.join(f'({e[i]})*z{i}^2' for i in range(10))
    c = '+'.join(f'z{i}^3' for i in range(10))
    s = '+'.join(f'z{i}' for i in range(10))
    src = f"""LIB "primdec.lib";
ring R=0,({v}),dp;
ideal I = {s}, z0, {q}, {c};
I = std(I);
print("dim Y (affine cone), mult:"); print(dim(I)); print(mult(I));
ideal J = I, minor(jacob(I),4);
J = std(J);
print("dim Sing cone:"); print(dim(J)); print("deg:"); print(mult(J));
ideal Jr = radical(J); Jr = std(Jr);
print("radical: dim, deg:"); print(dim(Jr)); print(mult(Jr));
quit;
"""
    print(run_sing(src))

def type2(z):
    v = ','.join(f'u{i}' for i in range(z))
    s = '+'.join(f'u{i}' for i in range(z))
    c = '+'.join(f'u{i}^3' for i in range(z))
    src = f"""LIB "primdec.lib";
ring R=0,({v}),dp;
ideal I = {s}, {c};
ideal J = I, minor(jacob(I),2);
J = std(J);
print("dim Sing cone (affine):"); print(dim(J)); print("deg:"); print(mult(J));
ideal Jr = radical(J); Jr=std(Jr); print("radical deg:"); print(mult(Jr));
quit;
"""
    print(run_sing(src))

def vbar(seed, p=32003):
    rng = np.random.default_rng(seed)
    v = ','.join(f'y{i}' for i in range(10))
    def ps(k): return '+'.join(f'y{i}^{k}' for i in range(10))
    h = '+'.join(f'{int(rng.integers(1, p))}*y{i}' for i in range(10))
    h2 = '+'.join(f'{int(rng.integers(1, p))}*y{i}' for i in range(10))
    src = f"""LIB "primdec.lib";
ring R={p},({v}),dp;
ideal I = {ps(1)}, {ps(3)}, {ps(5)}, {h};
ideal J = I, minor(jacob(I),4);
J = std(J);
print("dim (affine cone) of Sing(Vbar) ∩ H:"); print(dim(J));
ideal Jr = radical(J); Jr = std(Jr); print("deg of radical:"); print(mult(Jr));
ideal K = Jr, {h2}-1; K = std(K); print("points (vdim with second chart):"); print(vdim(K));
quit;
"""
    print(run_sing(src))

if __name__ == '__main__':
    m = sys.argv[1]
    if m == 'hess': hess(int(sys.argv[2]), int(sys.argv[3]))
    elif m == 'type3': type3()
    elif m == 'type2': type2(int(sys.argv[2]))
    elif m == 'vbar': vbar(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 32003)
