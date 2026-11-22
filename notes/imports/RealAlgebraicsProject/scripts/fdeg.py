# factor degrees mod p of msolve's eliminant (first polynomial of the parametrisation)
import sys, re, cypari
pari = cypari.pari
txt = open(sys.argv[1]).read()
p = int(re.search(r'\[0, \[(\d+),', txt).group(1))
m = re.search(r'\[1,\s*\[\[(\d+),\s*\[([0-9,\s]+)\]', txt)
d = int(m.group(1)); co = [int(c) for c in re.split(r'[,\s]+', m.group(2).strip())]
f = pari('Pol(' + str(co[::-1]) + ')') * pari(f'Mod(1,{p})')
fa = pari.factormod(pari.lift(f), p)
print(sys.argv[1], 'degree', d, 'factor degrees', sorted(int(pari.poldegree(g)) for g in fa[0]), 'squarefree', all(int(e)==1 for e in fa[1]))
