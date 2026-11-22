import sys
from newton import setup, support
for pt in [(1,1),(4,-5),(-5,4)]:
  for g in ['V4xV4','Z4xV4','V4xZ4','Z4xZ4']:
    setup(*pt, 14, g)
    for nm in ['m13','R14']:
        sup = list(support(nm,14).keys())
        low = [m for m in sup if sum(m) <= 12]
        hi = [m for m in sup if sum(m) > 12]
        # undominated high monomial: not divisible by any low one -> could lead for some weight
        # (exact test: m leads for some w>0 iff m is a vertex of Newton polyhedron; divisibility is sufficient to exclude)
        und = [m for m in hi if not any(all(l[i] <= m[i] for i in range(7)) for l in low)]
        print(pt, g, nm, 'high-degree monomials', len(hi), 'not divisible by a lower one', len(und), und[:3])
