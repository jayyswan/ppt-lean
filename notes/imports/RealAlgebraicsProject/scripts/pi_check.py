"""Session 10: on the plane Pi = {(a,a,a,a,b,b,b,b,c)}, fixed pointwise by the 4+4+1 subgroups,
is the quartic Q4(s' + t (s^2)') in t separable (so W is smooth over a general point of Pi)?"""
import cypari; pari = cypari.pari
a, b, t = pari('a'), pari('b'), pari('t')
s = [a]*4 + [b]*4 + [-4*a - 4*b]
m = sum(v**2 for v in s) / 9; w = [v**2 - m for v in s]
y = [u + t*v for u, v in zip(s, w)]
pw = lambda k: sum(v**k for v in y)
q = 6*pw(4) - pw(2)**2
d = pari.poldisc(q, t)
print('disc_t on Pi (factored):', pari.factor(d))
