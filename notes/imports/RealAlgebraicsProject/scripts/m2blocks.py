# S58: orbit and block structure of the M2 monodromy (partial permutations from m2mono.py)
# usage: python3 m2blocks.py <pkl> [<pkl> ...]   (same seed runs, later file extends the earlier)
import pickle, sys, numpy as np
tau0, S, perms = pickle.load(open(sys.argv[1], 'rb')); S = [np.array(x) for x in S]
for f in sys.argv[2:]:   # other runs from the same base (resumed with another seed): merge by coordinates
    t2, S2, p2 = pickle.load(open(f, 'rb')); assert np.allclose(t2, tau0)
    A = np.array(S); remap = []
    for x in S2:
        d = np.linalg.norm(A - x, axis=1); j = int(np.argmin(d))
        if d[j] < 1e-7*(1+np.linalg.norm(x)): remap.append(j)
        else: S.append(np.array(x)); A = np.vstack([A, x]); remap.append(len(S)-1)
    perms = perms + [[(remap[j] if j >= 0 else -1) for j in img] for img in p2]
N = len(S); S = np.array(S)
sg = np.array([-1]*4 + [1]*5)
sg = np.array([-1]*4 + [1]*5)
def iota(x):
    z, q, e = x[:4], x[4:8], x[8]; q2 = -q.copy(); q2[0] += 1
    return np.concatenate([z/(1+e), q2, [-e/(1+e)]])
def idx(y):
    d = np.linalg.norm(S - y, axis=1); j = int(np.argmin(d))
    return j if d[j] < 1e-7*(1+np.linalg.norm(y)) else -1
# classes = orbits of the Klein group <Z -> -Z, iota> (S58.2)
cls = np.full(N, -1); nc = 0; full = 0
for i in range(N):
    if cls[i] >= 0: continue
    orb = {i}
    for y in (S[i]*sg, iota(S[i]), iota(S[i])*sg):
        j = idx(y)
        if j >= 0: orb.add(j)
    full += len(orb) == 4
    for j in orb: cls[j] = nc
    nc += 1
print("N =", N, " Klein classes:", nc, " complete classes:", full)
maps = []
for img in perms:
    m = {i: j for i, j in enumerate(img) if j >= 0}
    if len(set(m.values())) == len(m): maps.append(m)
    else: print("non-injective loop dropped")
print("loops used:", len(maps), " defined points per loop:", [len(m) for m in maps])
# orbit of 0 (forward and inverse)
adj = [[] for _ in range(N)]
for m in maps:
    for a, b in m.items(): adj[a].append(b); adj[b].append(a)
seen = {0}; st = [0]
while st:
    a = st.pop()
    for b in adj[a]:
        if b not in seen: seen.add(b); st.append(b)
print("orbit of 0:", len(seen), "of", N)
P = list(cls); M = nc
pmaps = []; bad = 0
from collections import Counter, defaultdict
for m in maps:
    votes = defaultdict(Counter)
    for a_, b_ in m.items(): votes[P[a_]][P[b_]] += 1
    pm = {}
    for c, ct in votes.items():
        (tgt, k), = ct.most_common(1)
        if k == sum(ct.values()): pm[c] = tgt
        else: bad += 1
    if len(set(pm.values())) == len(pm): pmaps.append(pm)
print("class maps:", len(pmaps), " classes dropped for inconsistent images (path jumps):", bad)
# minimal block containing {0, i} at pair level (Atkinson, with partial maps: a lower bound for the true block)
def minblock(i, maps, n):
    par = list(range(n))
    def fd(a):
        while par[a] != a: par[a] = par[par[a]]; a = par[a]
        return a
    def un(a, b):
        a, b = fd(a), fd(b)
        if a == b: return False
        par[b] = a; return True
    un(0, i); changed = True
    while changed:
        changed = False
        cls = {}
        for m in maps:
            rep = {}
            for a, b in m.items():
                r = fd(a)
                if r in rep:
                    if un(rep[r], b): changed = True
                else: rep[r] = b
    r0 = fd(0); return sum(1 for a in range(n) if fd(a) == r0)
import random
random.seed(1)
test = list(range(1, M)) if len(sys.argv) < 0 or M <= 2000 else random.sample(range(1, M), 400)
sizes = [minblock(i, pmaps, M) for i in test]
print("min block sizes containing {0,i} at class level (tested %d i): min %d, max %d, count < M: %d" %
      (len(test), min(sizes), max(sizes), sum(1 for s in sizes if s < M)))
from collections import Counter as C2
print("block size histogram:", sorted(C2(sizes).items())[:12], "...", sorted(C2(sizes).items())[-3:])
small = [i for i, s_ in zip(test, sizes) if s_ <= 4]
print("i with block size <= 4:", small[:20])
for i in small[:5]:
    print(i, "defined for 0/i per loop:", [(0 in m, i in m, m.get(0), m.get(i)) for m in pmaps])
# cycles of each class-level loop that are fully defined
for m in pmaps:
    seen = set(); cyc = []
    for a in m:
        if a in seen: continue
        c = [a]; seen.add(a); b = m[a]; ok = True
        while b != a:
            if b not in m: ok = False; break
            c.append(b); seen.add(b); b = m[b]
        if ok: cyc.append(len(c))
    print("closed cycle lengths (largest 8):", sorted(cyc)[-8:], " fixed:", cyc.count(1), " covered:", sum(cyc), "of", M)
