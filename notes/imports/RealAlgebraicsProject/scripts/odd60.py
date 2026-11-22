# odd60.py -- session 60: the odd part of row E (fixed sextic, P dials) for one generator tau.
# Equations p_k(tau + s) + p_k(z) = 0, k = 1,3,5,7, z = 3 auxiliary crossings (roots of a cubic).
# Eliminates e1,e2,e3 over Q (Singular, char 0) for integer tau and factors the s-eliminant.
# Usage: python3 odd60.py <seed> [real]   ('real': also count real s with real-coefficient cubic)
import sys, random, subprocess
seed = int(sys.argv[1]); random.seed(seed)
tau = [random.randint(-20, 20) for _ in range(9)]
taus = '+'.join(f"(({t})+s)^%d" for t in tau)
L = ['ring r = 0,(e1,e2,e3,s),dp;',
     'poly z1 = e1; poly z2 = e1*z1 - 2*e2; poly z3 = e1*z2 - e2*z1 + 3*e3;',
     'list Z = z1, z2, z3; int k; for (k = 4; k <= 7; k++) { Z = insert(Z, e1*Z[k-1] - e2*Z[k-2] + e3*Z[k-3], k-1); }',
     'ideal I = ' + ','.join(f"({taus % tuple([k]*9)}) + Z[{k}]" for k in (1, 3, 5, 7)) + ';',
     'ideal E = eliminate(std(I), e1*e2*e3); print(E[1]); print(factorize(E[1]));', 'quit;']
open(f'odd60_{seed}.sing', 'w').write('\n'.join(L) + '\n')
out = subprocess.run(['Singular', '-q', f'odd60_{seed}.sing'], capture_output=True, text=True).stdout
print('tau =', tau); print(out[-2500:])
