(* Numerical checks cited in PLAN-hypergeometric-00-overview.md.
   Run in a Wolfram Language kernel. Results recorded 2026-09-15 are in the comments;
   "0``69" means zero to about 69 digits of accuracy. *)

m = 3/10; phi = 7/10; n = 2/5; b = 5/2; X = 7/10; mm = 2 b - 2; x = 3/10; z = 1/5;
checks = {
 (* V1, V2: complete K and E are 2F1 values.                       -> 0 (exact) *)
 "K" -> N[EllipticK[m] - Pi/2 Hypergeometric2F1[1/2, 1/2, 1, m], 20],
 "E" -> N[EllipticE[m] - Pi/2 Hypergeometric2F1[-1/2, 1/2, 1, m], 20],
 (* V3: incomplete F and complete Pi are Appell F1, not 2F1.       -> 0``69, 0``68 *)
 "F-inc-Appell" -> N[EllipticF[phi, m] - Sin[phi] AppellF1[1/2, 1/2, 1/2, 3/2, Sin[phi]^2, m Sin[phi]^2], 20],
 "Pi-complete-Appell" -> N[EllipticPi[n, m] - Pi/2 AppellF1[1/2, 1, 1/2, 1, n, m], 20],
 (* V4: arc length of y = x^b as a 2F1.                            -> 0``29 *)
 "powerlaw-arc" -> NIntegrate[Sqrt[1 + b^2 t^(2 b - 2)], {t, 0, X}, WorkingPrecision -> 30] -
   N[X Hypergeometric2F1[-1/2, 1/mm, 1 + 1/mm, -b^2 X^mm], 30],
 (* V5: Gauss's second summation theorem, Ramanujan signatures.    -> all 0 *)
 "Gauss2-1/4" -> N[Hypergeometric2F1[1/4, 3/4, 1, 1/2] - Sqrt[Pi]/(Gamma[5/8] Gamma[7/8]), 20],
 "Gauss2-1/3" -> N[Hypergeometric2F1[1/3, 2/3, 1, 1/2] - Sqrt[Pi]/(Gamma[2/3] Gamma[5/6]), 20],
 "Gauss2-1/6" -> N[Hypergeometric2F1[1/6, 5/6, 1, 1/2] - Sqrt[Pi]/(Gamma[7/12] Gamma[11/12]), 20],
 "Gauss2-1/2" -> N[Hypergeometric2F1[1/2, 1/2, 1, 1/2] - Sqrt[Pi]/(Gamma[3/4]^2), 20],
 (* V6: quadratic transformation, Clausen.                         -> 0``68, 0``69 *)
 "quadratic" -> N[Hypergeometric2F1[1/2, 1/2, 1, z] - Hypergeometric2F1[1/4, 1/4, 1, 4 z (1 - z)], 20],
 "Clausen" -> N[Hypergeometric2F1[1/4, 1/4, 1, x]^2 - HypergeometricPFQ[{1/2, 1/2, 1/2}, {1, 1}, x], 20],
 (* V7: quartic signature reduces to K.                            -> 0 *)
 "quartic-sig" -> N[Hypergeometric2F1[1/4, 3/4, 1, z] -
   (1 + Sqrt[z])^(-1/2) Hypergeometric2F1[1/2, 1/2, 1, 2 Sqrt[z]/(1 + Sqrt[z])], 20],
 (* V8: Legendre function.                                         -> 0``69 *)
 "Legendre" -> N[LegendreP[-1/3, x] - Hypergeometric2F1[1/3, 2/3, 1, (1 - x)/2], 20],
 (* V9: Euler integral, trigonometric form.                        -> 0``30 *)
 "Euler-trig" -> NIntegrate[Sin[t]^4 Cos[t]^2 (1 - 2/5 Sin[t]^2)^(1/2), {t, 0, Pi/2}, WorkingPrecision -> 30] -
   N[1/2 Beta[5/2, 3/2] Hypergeometric2F1[-1/2, 5/2, 4, 2/5], 30],
 (* V10: Kummer's theorem instance.                                -> 0``69 *)
 "Kummer" -> N[Hypergeometric2F1[1/3, 1/6, 1 + 1/3 - 1/6, -1] -
   Gamma[1 + 1/3 - 1/6] Gamma[1 + 1/6]/(Gamma[1 + 1/3] Gamma[1 + 1/6 - 1/6]), 20]
};
checks

(* V11: Polya's cubic-lattice constant u(3).
   uG = 1.51638605915197801816;  uK - uG -> 0``67;  MinimalPolynomial[k6] = x^4+12x^3+2x^2-12x+1.
   Bessel integral (machine precision, asymptotic tail beyond t = 700) gave 1.5163727,
   agreeing to ~5 digits; the gap is the truncated slowly-convergent tail. *)
k6 = (2 - Sqrt[3]) (Sqrt[3] - Sqrt[2]);
uG = Sqrt[6]/(32 Pi^3) Gamma[1/24] Gamma[5/24] Gamma[7/24] Gamma[11/24];
uK = 12/Pi^2 (18 + 12 Sqrt[2] - 10 Sqrt[3] - 7 Sqrt[6]) EllipticK[k6^2]^2;
{N[uG, 20], N[uK - uG, 20], MinimalPolynomial[k6, y], N[1 - 1/uG, 15]}

f[t_?NumericQ] := If[t < 700, (Exp[-t/3] BesselI[0, t/3])^3, (3/(2 Pi t))^(3/2)];
NIntegrate[f[t], {t, 0, 1, 10, 100, 1000, Infinity}, PrecisionGoal -> 10, AccuracyGoal -> 12, MaxRecursion -> 50]
