# Session 44: one real sample with margins for the V_4 chain (r = 1 or 3).
# Usage: python3 v4cert.py <r> <seed>
# Checks, at a real point Q of V_3 and a real direction t0 on C_Q:
#  (a) V_3 smooth at Q (Jacobian singular values),
#  (b) C_Q smooth at t0,
#  (c) p4 on the line Q + k v0 has a simple real root k0,
#  (d) a real singular member l0*A1 + A2 of the pencil of rank 4 and signature (2,2),
#  (e) the conic of that ruling through t0 meets C_Q transversally at t0 (simple root of the sextic),
# and prints y = Q + k0 v0: p1..p4, charpoly coefficients e1..e4, number of real roots.
import sys, numpy as np
sys.argv = ['v4chain.py', sys.argv[1], '0', sys.argv[2]]
exec(open('v4chain.py').read().split("\ntot_real_C")[0])
np.set_printoptions(precision=4, suppress=True, linewidth=150)

for attempt in range(50):
    Q = v3_point(); E = frame(Q); A1, A2, C3, Z = forms(Q, E)
    # (a)
    J = np.zeros((3, 9))
    for j in range(9):
        e = np.zeros(9); e[j] = 1; ze = zc(e); z = zc(Q)
        J[0, j] = np.sum(ze).real; J[1, j] = 2 * np.sum(z * ze).real; J[2, j] = 3 * np.sum(z ** 2 * ze).real
    JQ = J - np.outer(J @ Q, Q)  # tangent to the sphere
    sa = np.linalg.svd(JQ, compute_uv=False)[-1]
    deg, pen = pencil(A1, A2)
    p22 = [l for l, a, b in pen if a == 2 and b == 2]
    if not p22: continue
    pts = cq_points(A1, A2, C3, 60)
    good = None
    for t0 in pts:
        v0 = E @ t0
        rts, co = p4_roots(Q, v0)
        if not rts: continue
        dq = np.polyder(np.poly1d(co[::-1]))
        k0 = max(rts, key=lambda k: abs(dq(k)) / (1 + abs(k)) ** 3)
        Jc = np.vstack([2 * A1 @ t0, 2 * A2 @ t0, 3 * np.einsum('abc,b,c->a', C3, t0, t0), t0])
        sb = np.linalg.svd(Jc, compute_uv=False)[-1]
        good = (t0, v0, k0, abs(dq(k0)), sb, co); break
    if good is None: continue
    t0, v0, k0, dqk, sb, co = good
    l0 = p22[0]; M = l0 * A1 + A2
    ev, evec = np.linalg.eigh(M)
    order = np.argsort(abs(ev)); kvec = evec[:, order[0]]
    gap = sorted(abs(ev))[1] / max(abs(ev))
    # (e) ruling line of the quadric M through t0 (mod the vertex kvec): isotropic directions d of M
    # in {d : M(t0, d) = 0, d orthogonal to t0 and kvec}
    B = np.linalg.svd(np.vstack([M @ t0, t0, kvec]))[2][3:].T   # 5 x 2 basis
    m2 = B.T @ M @ B
    w, U = np.linalg.eigh(m2)
    if w[0] * w[1] >= 0: continue
    d = B @ (U[:, 0] * np.sqrt(abs(w[1])) + U[:, 1] * np.sqrt(abs(w[0])))   # M(d,d) = 0
    # plane spanned by t0, d, kvec: conic = {A1 = 0} in it; parametrise points t0 + s*(d + mu*kvec)
    # A1(t0 + s u, .) = 2 s A1(t0,u) + s^2 A1(u,u) = 0  ->  s = -2 A1(t0,u)/A1(u,u)
    def conic_pt(mu):
        u = d + mu * kvec
        return t0 - 2 * (t0 @ A1 @ u) / (u @ A1 @ u) * u
    mus = np.linspace(-50, 50, 200001)
    cub = lambda t: np.einsum('abc,a,b,c', C3, t, t, t)
    # transversality at t0: the cubic restricted to the conic has a simple zero at t0 (mu -> infinity
    # corresponds to t0 itself since s -> 0); test via the tangent direction of the conic at t0
    # the conic's tangent at t0 is the direction u0 with A1(t0, u0) = 0 inside the plane
    P2 = np.vstack([t0, d, kvec]).T
    # tangent: u in span(d, kvec) with A1(t0,u)=0
    a_ = t0 @ A1 @ d; b_ = t0 @ A1 @ kvec
    u0 = b_ * d - a_ * kvec; u0 /= np.linalg.norm(u0)
    gradc = 3 * np.einsum('abc,b,c->a', C3, t0, t0)
    trans = abs(gradc @ u0) / np.linalg.norm(gradc)
    # check the conic lies on S_Q (A1 = A2 = 0) at a sample point
    tt = conic_pt(0.37); tt /= np.linalg.norm(tt)
    on_S = max(abs(tt @ A1 @ tt), abs(tt @ A2 @ tt))
    y = Q + k0 * v0; zy = zc(y)
    ps = [np.sum(zy ** k).real / np.linalg.norm(y) ** k for k in range(1, 6)]
    cp = np.poly(zy).real
    nreal = int(sum(abs(np.roots(cp).imag) < 1e-7))
    print(f'r={r}, attempt {attempt}')
    print(f' (a) V3 smooth at Q: smallest singular value {sa:.3g}')
    print(f' (b) C_Q smooth at t0: smallest singular value {sb:.3g}')
    print(f" (c) p4 on the line: coefficients {np.round(co, 4)}, real roots {np.round(p4_roots(Q, v0)[0], 4)}, |q'(k0)| = {dqk:.3g}")
    print(f' (d) pencil: real singular members {[(round(l, 4), a, b) for l, a, b in pen]}; l0 = {l0:.4f}, relative eigen-gap {gap:.3g}')
    print(f' (e) ruling conic through t0: on S_Q to {on_S:.1e}; transversality |grad c . tangent|/|grad c| = {trans:.3g}')
    print(f' y = Q + k0 v0: normalised p1..p5 = {np.round(ps, 12)}; charpoly e1..e4 = {np.round(cp[1:5], 12)}; real roots {nreal}')
    break
