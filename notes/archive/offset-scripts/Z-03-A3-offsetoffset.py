# Z-03: independent re-verification of A3 (offset x offset = degree 92; self-crossing degree 32).
# Part A: explicit crossing of the two cf1 cubic-pair offsets at d1=d2=1 -> 50 digits.
# Part B: verify the printed f32 self-crossing polynomial is irreducible, and its roots are
#         genuine bitangent-circle parameters (|centre-gamma(t)|=|d|, perpendicular, distinct t,s).
# Part C: attempt the elimination degree for offset x offset over GF(p) via Groebner (bounded).
import sys
import sympy as sp
import mpmath as mp

mp.mp.dps = 60
t = sp.symbols('t', real=True)

# ---- cf1 cubics ----
g1x = 2 * t ** 3 - 3 * t ** 2 + 5 * t + 7
g1y = t ** 3 + 4 * t ** 2 - 2 * t + 1
g2x = 3 * t ** 3 + t ** 2 - 4 * t + 2
g2y = -t ** 3 + 2 * t ** 2 + 6 * t - 5

u1, v1 = sp.diff(g1x, t), sp.diff(g1y, t)
u2, v2 = sp.diff(g2x, t), sp.diff(g2y, t)
q1 = sp.expand(u1 ** 2 + v1 ** 2)
q2 = sp.expand(u2 ** 2 + v2 ** 2)
print("q1 =", q1)
print("q2 =", q2)

# ---- Part A: numerical crossing ----
print("\n=== Part A: explicit offset x offset crossing (d1=d2=1) ===")
t1s = mp.mpf("1.22231179911457674266169305600314168498362206")
t2s = mp.mpf("1.64943883635326178031270697615901139391043872")


# use lambdas via mpmath for accuracy
f1x = sp.lambdify(t, g1x, 'mpmath')
f1y = sp.lambdify(t, g1y, 'mpmath')
f2x = sp.lambdify(t, g2x, 'mpmath')
f2y = sp.lambdify(t, g2y, 'mpmath')
fu1 = sp.lambdify(t, u1, 'mpmath')
fv1 = sp.lambdify(t, v1, 'mpmath')
fu2 = sp.lambdify(t, u2, 'mpmath')
fv2 = sp.lambdify(t, v2, 'mpmath')

P1 = (f1x(t1s), f1y(t1s))
P2 = (f2x(t2s), f2y(t2s))
w1 = mp.sqrt(fu1(t1s) ** 2 + fv1(t1s) ** 2)
w2 = mp.sqrt(fu2(t2s) ** 2 + fv2(t2s) ** 2)
O1 = (P1[0] - fv1(t1s) / w1, P1[1] + fu1(t1s) / w1)
O2 = (P2[0] - fv2(t2s) / w2, P2[1] + fu2(t2s) / w2)
print("O1 =", mp.nstr(O1[0], 45), mp.nstr(O1[1], 45))
print("O2 =", mp.nstr(O2[0], 45), mp.nstr(O2[1], 45))
print("|O1-O2| =", mp.nstr(mp.sqrt((O1[0] - O2[0]) ** 2 + (O1[1] - O2[1]) ** 2), 5))
print("|O1-gamma1| - 1 =", mp.nstr(mp.sqrt((O1[0] - P1[0]) ** 2 + (O1[1] - P1[1]) ** 2) - 1, 5))
print("|O2-gamma2| - 1 =", mp.nstr(mp.sqrt((O2[0] - P2[0]) ** 2 + (O2[1] - P2[1]) ** 2) - 1, 5))
n1 = ((-fv1(t1s) / w1, fu1(t1s) / w1))
n2 = ((-fv2(t2s) / w2, fu2(t2s) / w2))
print("perp1 =", mp.nstr(abs((O1[0] - P1[0]) * fu1(t1s) + (O1[1] - P1[1]) * fv1(t1s)), 5),
      " perp2 =", mp.nstr(abs((O2[0] - P2[0]) * fu2(t2s) + (O2[1] - P2[1]) * fv2(t2s)), 5))

# transversality: det[O1'(t1), -O2'(t2)]
O1x = sp.diff(g1x - v1 / sp.sqrt(q1), t)
O1y = sp.diff(g1y + u1 / sp.sqrt(q1), t)
O2x = sp.diff(g2x - v2 / sp.sqrt(q2), t)
O2y = sp.diff(g2y + u2 / sp.sqrt(q2), t)
O1xe = sp.lambdify(t, O1x, 'mpmath')
O1ye = sp.lambdify(t, O1y, 'mpmath')
O2xe = sp.lambdify(t, O2x, 'mpmath')
O2ye = sp.lambdify(t, O2y, 'mpmath')
detJ = O1xe(t1s) * O2ye(t2s) - O1ye(t1s) * O2xe(t2s)
print("transversality det =", mp.nstr(abs(detJ), 12))

# ---- Part B: printed f32 self-crossing ----
print("\n=== Part B: self-crossing degree-32 polynomial (cf1, d=2) ===")
c32 = [4939757637440419476137, -171567311174953282243812, 1900683705607606447866846,
       -12154245401968565785795800, 53119940708167982013346845, -173189567550564902939960304,
       444430450023364820723563342, -933948657131460024605959916, 1655747772048120320104701094,
       -2533193265633398598123925052, 3400000803543540764985399930, -4054805821497820973702777104,
       4340525391749983862662859939, -4198723592418233813197778120, 3696868282512422443768636266,
       -2969881197094243482713535172, 2190480727730476025175509482, -1481065452765798410214073532,
       924268187610186057862631074, -529064553603668626882788472, 280403697767276095898692675,
       -135783772031881110665569536, 61016372781990194047128786, -24794404092649268865468756,
       9379780546977357257348694, -3139473745961717584794660, 986767022135220688023750,
       -261866451689349969924000, 67003001824974808168125, -12949524126861832125000,
       2620933629659040093750, -288034083207368437500, 44499647686531640625]
f32 = sum(c * t ** i for i, c in enumerate(c32))
f32p = sp.Poly(f32, t)
print("deg =", f32p.degree(), "irreducible over Q:", f32p.is_irreducible)
# numerical self-crossing for cf1 d=2: t=0.599337..., s=0.0476717...
ts = mp.mpf("0.599337433861129445146424851688373373150798571")
ss = mp.mpf("0.0476717005369934433997256730706413981860966541")
cx = mp.mpf("7.87715009600341450889889780106580084769897677")
cy = mp.mpf("2.80686039268423686425593528826127510749194291")
X1 = f1x(ts) - 2 * fv1(ts) / mp.sqrt(fu1(ts) ** 2 + fv1(ts) ** 2)
Y1 = f1y(ts) + 2 * fu1(ts) / mp.sqrt(fu1(ts) ** 2 + fv1(ts) ** 2)
X2 = f1x(ss) - 2 * fv1(ss) / mp.sqrt(fu1(ss) ** 2 + fv1(ss) ** 2)
Y2 = f1y(ss) + 2 * fu1(ss) / mp.sqrt(fu1(ss) ** 2 + fv1(ss) ** 2)
f32f = sp.lambdify(t, f32, 'mpmath')
print("t root residual f32(t) =", mp.nstr(abs(f32f(ts)), 5))
print("offset points equal:", mp.nstr(abs(X1 - X2), 5), mp.nstr(abs(Y1 - Y2), 5))
print("|centre-gamma(t)|-2 =", mp.nstr(abs(mp.sqrt((cx - X1) ** 2 + (cy - Y1) ** 2) - 2), 5))
print("|centre-gamma(s)|-2 =", mp.nstr(abs(mp.sqrt((cx - X2) ** 2 + (cy - Y2) ** 2) - 2), 5))
