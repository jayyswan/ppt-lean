(* R4c-01-sine-exp-rect.wl
   Task R4c: are the arc lengths of `sine`, `exp_two` and the `rectangle` boundary
   (or their affine images) new 2F1 sources?

   Backend: Wolfram Language kernel (wolfram_WolframLanguageEvaluator).
   Mathematica conventions used:
     EllipticE[phi, m]  has parameter m = k^2   (repo convention c = k^2).
     Hypergeometric2F1[a,b,c,z] = 2F1.
     AppellF1[a;b1,b2;c;x,y]    = Appell F1.
   All comparisons are to 40 working digits; deviations print at ~1e-39..1e-88
   (i.e. exact up to the working precision).
*)

wp = 40;

(* ------------------------------------------------------------------ *)
(* 0. Classification facts                                             *)
(* ------------------------------------------------------------------ *)

Print["== sine: symbolic antiderivative check =="];
Print["D[Sqrt[2] EllipticE[t,1/2], t] - Sqrt[1+Cos[t]^2] simplifies to ",
  Simplify[D[Sqrt[2] EllipticE[t, 1/2], t] - Sqrt[1 + Cos[t]^2]]];
Print["Integrate gives: ", Integrate[Sqrt[1 + Cos[t]^2], t]];

Print["== sine: incomplete E is Appell F1 (PLAN section 1) =="];
phi = 7/10;
lhs = EllipticE[phi, 1/2];
rhs = Sin[phi] AppellF1[1/2, 1/2, -1/2, 3/2, Sin[phi]^2, (1/2) Sin[phi]^2];
Print["E(phi|1/2)                            = ", N[lhs, wp]];
Print["sin phi F1(1/2;1/2,-1/2;3/2;sin^2,.) = ", N[rhs, wp]];
Print["difference                            = ", N[lhs - rhs, wp]];

Print["== complete E(k2) = (pi/2) 2F1(-1/2,1/2;1;k2) =="];
Do[
  k2 = kk;
  Print["k2=", k2, "  diff=",
    N[EllipticE[k2] - (Pi/2) Hypergeometric2F1[-1/2, 1/2, 1, k2], wp]],
  {kk, {1/2, 3/10, 1/5}}
];

(* ------------------------------------------------------------------ *)
(* 1. sine  y = sin x : arc length  Int Sqrt[1+cos^2 t] dt             *)
(*    closed form  = Sqrt[2] (E(b|1/2) - E(a|1/2))                     *)
(* ------------------------------------------------------------------ *)

sineArcClosed[a_, b_] := Sqrt[2] (EllipticE[b, 1/2] - EllipticE[a, 1/2]);

Print["== sine: closed form vs high-precision quadrature =="];
Do[
  {a, b} = pr;
  closed = N[sineArcClosed[a, b], wp];
  quad = NIntegrate[Sqrt[1 + Cos[t]^2], {t, a, b},
     WorkingPrecision -> wp, MaxRecursion -> 50];
  Print["[", a, ",", b, "] closed=", closed, "  diff=", closed - quad],
  {pr, {{0, 1}, {1/3, 5/4}, {-2/5, 7/3}, {0, Pi/2}, {0, Pi}, {0, 2 Pi}}}
];

Print["== sine: complete-period values =="];
Print["[0,pi/2] sqrt2 E(1/2)   = ", N[Sqrt[2] EllipticE[1/2], wp]];
Print["[0,pi]   2 sqrt2 E(1/2) = ", N[2 Sqrt[2] EllipticE[1/2], wp],
  "  quad=", NIntegrate[Sqrt[1 + Cos[t]^2], {t, 0, Pi}, WorkingPrecision -> wp]];
Print["[0,2pi]  4 sqrt2 E(1/2) = ", N[4 Sqrt[2] EllipticE[1/2], wp],
  "  quad=", NIntegrate[Sqrt[1 + Cos[t]^2], {t, 0, 2 Pi}, WorkingPrecision -> wp]];
Print["complete [0,pi/2] = (pi/sqrt2) 2F1(-1/2,1/2;1;1/2) = ",
  N[(Pi/Sqrt[2]) Hypergeometric2F1[-1/2, 1/2, 1, 1/2], wp]];

(* ------------------------------------------------------------------ *)
(* 2. affine sine  y = amp sin(frq x + ph) + off                       *)
(*    closed form = Sqrt[1+amp^2 frq^2]/|frq| (E(frq b+ph|k2)-...)     *)
(*    with k2 = amp^2 frq^2/(1+amp^2 frq^2).                           *)
(* ------------------------------------------------------------------ *)

affineArcClosed[a_, b_, amp_, frq_, ph_] :=
  Module[{k2 = amp^2 frq^2/(1 + amp^2 frq^2)},
    Sqrt[1 + amp^2 frq^2]/Abs[frq] (EllipticE[frq b + ph, k2] -
      EllipticE[frq a + ph, k2])];

Print["== affine sine: closed form vs quadrature =="];
Do[
  {amp, frq, ph, a, b} = p;
  closed = N[affineArcClosed[a, b, amp, frq, ph], wp];
  quad = NIntegrate[Sqrt[1 + amp^2 frq^2 Cos[frq t + ph]^2], {t, a, b},
     WorkingPrecision -> wp, MaxRecursion -> 50];
  Print["amp=", amp, " frq=", frq, " ph=", ph, " [", a, ",", b,
    "] closed=", closed, "  diff=", closed - quad,
    "  k2=", N[amp^2 frq^2/(1 + amp^2 frq^2), 20]],
  {p, {{3/2, 2, 1/3, 0, 1}, {5/7, 3/2, -2/5, -1/3, 4/5},
       {1, 1, 0, 0, Pi/2}, {1, 1, 0, 0, Pi}}}
];

Print["== affine complete quarter-period reduces to (pi/2) 2F1(-1/2,1/2;1;k2) =="];
Do[
  {amp, frq} = p;
  k2 = amp^2 frq^2/(1 + amp^2 frq^2);
  lhs = Sqrt[1 + amp^2 frq^2]/Abs[frq] EllipticE[k2];
  rhs = Sqrt[1 + amp^2 frq^2]/Abs[frq] (Pi/2) Hypergeometric2F1[-1/2, 1/2, 1, k2];
  Print["amp=", amp, " frq=", frq, " k2=", k2, " diff=", N[lhs - rhs, wp]],
  {p, {{3/2, 2}, {5/7, 3/2}, {1, 1}}}
];

(* ------------------------------------------------------------------ *)
(* 3. exp_two  y = 2^x : arc length                                    *)
(*    u = Log[2] 2^x,  Int Sqrt[1+(Log2)^2 2^(2x)] dx                  *)
(*      = (1/Log2) Int Sqrt[1+u^2]/u du                                *)
(*      = (1/Log2) [ Sqrt[1+u^2] - ArcSinh[1/u] ]                      *)
(* ------------------------------------------------------------------ *)

F[u_] := Sqrt[1 + u^2] - ArcSinh[1/u];

Print["== exp_two antiderivative: FullSimplify residual =="];
Print["D[F[u],u] - Sqrt[1+u^2]/u = ",
  FullSimplify[D[F[u], u] - Sqrt[1 + u^2]/u, Assumptions -> u > 0]];

expArcClosed[a_, b_] :=
  Module[{ua = Log[2] 2^a, ub = Log[2] 2^b}, (F[ub] - F[ua])/Log[2]];

Print["== exp_two: closed form vs quadrature =="];
Do[
  {a, b} = pr;
  Print["[", a, ",", b, "] closed=", N[expArcClosed[a, b], wp],
    "  diff=", N[expArcClosed[a, b] -
      NIntegrate[Sqrt[1 + Log[2]^2 2^(2 t)], {t, a, b},
        WorkingPrecision -> wp], wp]],
  {pr, {{0, 1}, {1/3, 5/4}, {-1/3, 3/2}}}
];

(* ------------------------------------------------------------------ *)
(* 4. rectangle: an edge is straight; length = coordinate difference.  *)
(* ------------------------------------------------------------------ *)

Print["== rectangle edge length = coordinate difference =="];
Print["seg (0,0)->(3/2,0): ", N[Abs[3/2 - 0], 30]];
Print["affine image of a line is a line, so the image is still elementary"];
