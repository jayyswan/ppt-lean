# Session 61: degree of the row-E3 hypersurface G3 (general cubic Bezier x T_6 graph) on a random line, mod p.
# Line u_i = a_i + k b_i (i = 1..9). Unknowns k, x0..x3 (X = x0 + x1 t + x2 t^2 + x3 t^3), saturation s, t.
# Equations: cleared divided differences on the 5 windows {j..j+4}: sum_i (-1)^pos f_i V(W \ i) = 0, f_i = T_6(X(u_i));
# s * l(x1,x2,x3) = 1 (X nonconstant); t * prod(k - k_mn) = 1 (no collisions u_m = u_n).
# Usage: python3 e3deg.py <seed> [p]   writes e3deg_<seed>.ms, runs msolve (background; may be slow).
import sys, random, subprocess
seed = int(sys.argv[1]); p = int(sys.argv[2]) if len(sys.argv) > 2 else 32003
random.seed(seed)
def inv(a): return pow(a % p, p - 2, p)
A = [random.randrange(p) for _ in range(9)]; B = [random.randrange(p) for _ in range(9)]
U = [f'({A[i]}+{B[i]}*k)' for i in range(9)]
X = lambda i: f'(x0+x1*{U[i]}+x2*{U[i]}^2+x3*{U[i]}^3)'
f = lambda i: f'(32*{X(i)}^6-48*{X(i)}^4+18*{X(i)}^2-1)'
def V(idx):
    terms = [f'({U[n]}-{U[m]})' for a_, m in enumerate(idx) for n in idx[a_+1:]]
    return '*'.join(terms) if terms else '1'
eqs = []
for j in range(5):
    W = list(range(j, j + 5))
    parts = []
    for pos, i in enumerate(W):
        rest = [w for w in W if w != i]
        parts.append(f'{("+" if pos else "") if pos % 2 == 0 else "-"}{f(i)}*{V(rest)}')
    eqs.append(''.join(parts))
l = [random.randrange(1, p) for _ in range(3)]
eqs.append(f's*({l[0]}*x1+{l[1]}*x2+{l[2]}*x3)-1')
kmn = sorted({(-(A[m]-A[n])*inv(B[m]-B[n])) % p for m in range(9) for n in range(m+1, 9) if abs(m-n) <= 4})
eqs.append('t*' + '*'.join(f'(k-{c})' for c in kmn) + '-1')
fn = f'e3deg_{seed}.ms'
# expand with Singular (msolve does not parse parentheses)
sing = f'ring R = {p},(k,x0,x1,x2,x3,s,t),dp;\nshort=0;\n' + ''.join(f'poly f{i} = {e};\nprint(f{i});\nprint("@@");\n' for i, e in enumerate(eqs)) + 'quit;\n'
out = subprocess.run(['Singular', '-q'], input=sing, capture_output=True, text=True).stdout
polys = [q.replace('\n', '').strip() for q in out.split('@@') if q.strip()]
assert len(polys) == len(eqs), (len(polys), out[:500])
open(fn, 'w').write('k,x0,x1,x2,x3,s,t\n' + str(p) + '\n' + ',\n'.join(polys) + '\n')
print('wrote', fn, ' collision values', len(kmn))
r = subprocess.run(['msolve', '-f', fn, '-o', fn + '.out', '-t', '2', '-v', '1'], capture_output=True, text=True)
print(r.stdout[-2000:]); print(open(fn + '.out').read()[:200])
