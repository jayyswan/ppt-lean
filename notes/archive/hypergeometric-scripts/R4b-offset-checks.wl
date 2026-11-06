(* ::Package:: *)

(* ============================================================================
   R4b-offset-checks.wl
   Task R4b of PLAN-hypergeometric-00-overview: "offset-curve arc length as 2F1?"
   Backend: Wolfram Language kernel (wolfram_WolframLanguageEvaluator).

   Conventions (match Pptc/Defs.lean):
     speed gamma t  = Sqrt(x'^2 + y'^2)
     unitNormal     = (-y'/w, x'/w)      (velocity turned +90 deg, the LEFT normal)
     offsetParam    = gamma + d * unitNormal
     signed curvature kappa = (x' y'' - y' x'') / w^3   (left-turning positive)
   Under these conventions   speed(offsetParam gamma d .) = |1 - d kappa| * speed gamma.

   Everything below is a check of a claimed identity, to >= 15 significant digits
   (most to 40-60 digits) against high-precision numerical quadrature.
   ============================================================================ *)

Print["=== (A) general symbolic identity: |Gamma'|^2 = (1 - d kappa)^2 w^2 ==="];
ClearAll[x, y, d, t, w, kap, gamA];
w = Sqrt[x'[t]^2 + y'[t]^2];
gamA = {x[t] - d*y'[t]/w, y[t] + d*x'[t]/w};
spd2 = Simplify[D[gamA, t] . D[gamA, t]];
kap = (x'[t]*y''[t] - y'[t]*x''[t])/w^3;
Print["  residual spd2 - (1-d kap)^2 w^2 = ",
  Simplify[spd2 - (1 - d*kap)^2*w^2]];

Print["=== (B) ellipse a=2,b=1,d=3/10, theta in [0,1] ==="];
ClearAll[a, b, dd, xe, ye, we, ke, Game, phie, cc, basePhi];
a = 2; b = 1; dd = 3/10;
xe[t_] := a Cos[t]; ye[t_] := b Sin[t];
we[t_] := Sqrt[xe'[t]^2 + ye'[t]^2];
ke[t_] := (xe'[t] ye''[t] - ye'[t] xe''[t])/we[t]^3;
Game[t_] := {xe[t], ye[t]} + dd {-ye'[t]/we[t], xe'[t]/we[t]};
spdOff[t_] := Sqrt[Game'[t] . Game'[t]];
phie[t_] := ArcTan[xe'[t], ye'[t]];
cc = 1 - b^2/a^2;
basePhi[ph_] := a Sqrt[1 - cc] EllipticE[ph, -cc/(1 - cc)];
numE = NIntegrate[spdOff[t], {t, 0, 1}, WorkingPrecision -> 60, MaxRecursion -> 40];
clE = basePhi[1] - dd (phie[1] - phie[0]);
Print["  numeric offset length     = ", numE];
Print["  E-base + d*turning angle  = ", clE];
Print["  residual                  = ", numE - clE];
Print["  base length (quadrature)   = ",
  NIntegrate[we[t], {t, 0, 1}, WorkingPrecision -> 60, MaxRecursion -> 40]];
Print["  base length (E closed form)= ", basePhi[1]];

Print["=== (C) monomial graph f=C x^n, C=1/10, n=5 (m=8), d=1/3, x in [1/2,1] ==="];
ClearAll[f5, w5, k5, gam5, spd5, nn, mm, bb2, gg];
Cc = 1/10; nn = 5; dd = 1/3;
f5[x_] := Cc x^nn; w5[x_] := Sqrt[1 + f5'[x]^2]; k5[x_] := f5''[x]/w5[x]^3;
gam5[x_] := {x, f5[x]} + dd {-f5'[x]/w5[x], 1/w5[x]};
spd5[x_] := Sqrt[gam5'[x] . gam5'[x]];
num5 = NIntegrate[spd5[t], {t, 1/2, 1}, WorkingPrecision -> 60, MaxRecursion -> 40];
mm = 2 nn - 2; bb2 = (nn Cc)^2;
gg[X_] := X Hypergeometric2F1[-1/2, 1/mm, 1 + 1/mm, -bb2 X^mm];
cl5 = (gg[1] - gg[1/2]) - dd (ArcTan[f5'[1]] - ArcTan[f5'[1/2]]);
Print["  numeric offset length     = ", num5];
Print["  V4 2F1 part               = ", gg[1] - gg[1/2]];
Print["  -d*arctan(f') part        = ", -dd (ArcTan[f5'[1]] - ArcTan[f5'[1/2]])];
Print["  residual                  = ", num5 - cl5];

Print["=== (D) monomial graph f=C x^n, C=1/4, n=3 (m=4, elliptic), d=2/5, x in [1/2,1] ==="];
ClearAll[f3, w3, k3, gam3, spd3];
Cc = 1/4; nn = 3; dd = 2/5;
f3[x_] := Cc x^nn; w3[x_] := Sqrt[1 + f3'[x]^2]; k3[x_] := f3''[x]/w3[x]^3;
gam3[x_] := {x, f3[x]} + dd {-f3'[x]/w3[x], 1/w3[x]};
spd3[x_] := Sqrt[gam3'[x] . gam3'[x]];
num3 = NIntegrate[spd3[t], {t, 1/2, 1}, WorkingPrecision -> 60, MaxRecursion -> 40];
mm = 2 nn - 2; bb2 = (nn Cc)^2;
gg[X_] := X Hypergeometric2F1[-1/2, 1/mm, 1 + 1/mm, -bb2 X^mm];
cl3 = (gg[1] - gg[1/2]) - dd (ArcTan[f3'[1]] - ArcTan[f3'[1/2]]);
Print["  numeric offset length     = ", num3];
Print["  closed form               = ", cl3];
Print["  residual                  = ", num3 - cl3];

Print["=== (E) cubic pair of Offset.lean: x=t^3-t^2+2t+1, y=-(t^3/3+t^2/2+t), d=1/2, t in [0,1] ==="];
ClearAll[xx, yy, wc, kc, Gamc, spdc, phic];
xx[t_] := t^3 - t^2 + 2 t + 1; yy[t_] := -(t^3/3 + t^2/2 + t); dd = 1/2;
wc[t_] := Sqrt[xx'[t]^2 + yy'[t]^2];
kc[t_] := (xx'[t] yy''[t] - yy'[t] xx''[t])/wc[t]^3;
Gamc[t_] := {xx[t], yy[t]} + dd {-yy'[t]/wc[t], xx'[t]/wc[t]};
spdc[t_] := Sqrt[Gamc'[t] . Gamc'[t]];
phic[t_] := ArcTan[xx'[t], yy'[t]];
numc = NIntegrate[spdc[t], {t, 0, 1}, WorkingPrecision -> 40, MaxRecursion -> 40];
basec = NIntegrate[wc[t], {t, 0, 1}, WorkingPrecision -> 40, MaxRecursion -> 40];
kint = NIntegrate[kc[t] wc[t], {t, 0, 1}, WorkingPrecision -> 40, MaxRecursion -> 40];
clc = basec - dd kint;
Print["  numeric offset length     = ", numc];
Print["  base length (3rd-kind)    = ", basec];
Print["  -d*int(kappa ds)          = ", -dd kint];
Print["  turning angle = phi(1)-phi(0) = ", N[phic[1] - phic[0], 40]];
Print["  residual                  = ", numc - clc];

Print["=== (F) curvature of y=C x^n: correct formula vs the task's guess ==="];
ClearAll[Cx, nx, xs];
Cx = 3/2; nx = 5;
kappaCorrect[xs_] := nx (nx - 1) Cx xs^(nx - 2)/(1 + nx^2 Cx^2 xs^(2 nx - 2))^(3/2);
kappaTaskGuess[xs_] := nx (nx - 1) (Cx xs)^(nx - 2)/(1 + nx^2 Cx^2 xs^(2 nx - 2))^(3/2);
kb[xs_] := (Cx nx xs^(nx - 1));
Print["  at x=1: correct = ", kappaCorrect[1], "  task guess = ", kappaTaskGuess[1],
  "  ratio = ", kappaCorrect[1]/kappaTaskGuess[1]];

Print["=== (G) elementary integral  int dtheta/(a^2 sin^2 + b^2 cos^2) ==="];
ClearAll[aa, bbb, th];
Print["  symbolic: ",
  Simplify[D[1/(aa bbb) ArcTan[(aa/bbb) Tan[th]], th] -
    (1/(aa^2 Sin[th]^2 + bbb^2 Cos[th]^2))]];
