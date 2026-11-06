(* R5-box-b6-checks.wl
   R5: does the bounding-box machinery move the B6 obstruction?
   All values at high precision with the Wolfram kernel. *)

wp = 50;

(* ---------- 0. Box-produced constants (values from the Lean PLAN/notes) ---------- *)
parabolaHalfArc = x /. FindRoot[NIntegrate[Sqrt[1 + 4 t^2], {t, 0, x},
     WorkingPrecision -> wp] - 1/2, {x, 0.4463}, WorkingPrecision -> wp];
backParabola = NIntegrate[Sqrt[1 + 4 t^2], {t, 0, parabolaHalfArc}, WorkingPrecision -> wp];

cubicUnitArc = x /. FindRoot[NIntegrate[Sqrt[1 + 9 t^4], {t, 0, x},
     WorkingPrecision -> wp] - 1, {x, 0.79}, WorkingPrecision -> wp];
backCubic = NIntegrate[Sqrt[1 + 9 t^4], {t, 0, cubicUnitArc}, WorkingPrecision -> wp];

quarticUnitArc = x /. FindRoot[NIntegrate[Sqrt[1 + 16 t^6], {t, 0, x},
     WorkingPrecision -> wp] - 1, {x, 0.81}, WorkingPrecision -> wp];
backQuartic = NIntegrate[Sqrt[1 + 16 t^6], {t, 0, quarticUnitArc}, WorkingPrecision -> wp];

offsetCusp = 3.015151812639309983896917609276868074014;

boxVals = <|"parabola(1/2)" -> parabolaHalfArc, "cubic(1)" -> cubicUnitArc,
   "quartic(1)" -> quarticUnitArc, "offsetCusp" -> offsetCusp|>;

Print["--- box constants and back-substitution residuals ---"];
Print["parabola b = ", NumberForm[parabolaHalfArc, 25], "  resid ",
  backParabola - 1/2];
Print["cubic    b = ", NumberForm[cubicUnitArc, 25], "  resid ", backCubic - 1];
Print["quartic  b = ", NumberForm[quarticUnitArc, 25], "  resid ", backQuartic - 1];

(* ---------- 1. The m=10 first-kind periods ---------- *)
Print["\n--- m=10 Beta periods (first kind) ---"];
b11025 = (1/10) Beta[1/10, 2/5];
b15310 = (1/10) Beta[1/5, 3/10];
Print["(1/10)B(1/10,2/5) = ", NumberForm[b11025, 30]];
Print["(1/10)B(1/5,3/10) = ", NumberForm[b15310, 30]];

(* ---------- 2. second-kind incomplete integrals at the box abscissas ---------- *)
Print["\n--- first-kind incomplete integral at each box abscissa, m=10 ---"];
ik10b[b_] := NIntegrate[t^(1/2)/Sqrt[1 + t^10], {t, 0, b}, WorkingPrecision -> wp];
Do[Print[k, ": I0(b) = ", NumberForm[ik10b[boxVals[k]], 25]], {k, Keys[boxVals]}];

(* ---------- 3. coincidence test: box value vs Beta periods ---------- *)
Print["\n--- coincidence tests (box value - Beta period) ---"];
Do[Print[k, " : ", NumberForm[N[boxVals[k] - b11025, 30], 20], "  |  ",
   NumberForm[N[boxVals[k] - b15310, 30], 20]], {k, Keys[boxVals]}];

(* ---------- 4. PSLQ: are the box values integer combinations of the periods? ---------- *)
Print["\n--- PSLQ relations among {1, b11025, b15310, box value} ---"];
Do[
  rel = FindIntegerNullVector[N[{1, b11025, b15310, boxVals[k]}, 40]];
  Print[k, ": ", rel],
  {k, Keys[boxVals]}];

Print["PSLQ {1,B(1/10,2/5)/10,B(1/5,3/10)/10}: ",
  FindIntegerNullVector[N[{1, b11025, b15310}, 40]]];
Print["PSLQ {1,Gamma[1/10],Gamma[1/5],Gamma[3/10],Gamma[2/5]}: ",
  FindIntegerNullVector[N[{1, Gamma[1/10], Gamma[1/5], Gamma[3/10], Gamma[2/5]}, 40]]];

(* ---------- 5. is the offset cusp abscissa algebraic? minimal polynomial ---------- *)
Print["\n--- offset cusp abscissa: minimal polynomial degree ---"];
mp = MinimalPolynomial[SetPrecision[offsetCusp, 40], x, WorkingPrecision -> 60];
Print["degree = ", Exponent[mp, x]];
Print["coeffs : ", CoefficientList[mp, x]];

(* ---------- 6. are the other box numbers algebraic? ---------- *)
Print["\n--- RootApproximant of the arc abscissas (should fail: transcendental) ---"];
Print["parabola: ", RootApproximant[parabolaHalfArc]];
Print["cubic: ", RootApproximant[cubicUnitArc]];
Print["quartic: ", RootApproximant[quarticUnitArc]];

(* ---------- 7. ds = dx/Sqrt[1+x^m] forces y'^2 = x^m ---------- *)
Print["\n--- ds^2 = dx^2 + dy^2 ; ds/dx = 1/Sqrt[1+x^m] -> y'^2 = x^m ---"];
Clear[x, y, yp];
sol = Solve[(1 + yp^2) == 1/(1 + x^m), yp^2, Reals];
Print["y'^2 = ", Simplify[yp^2 /. sol], "   (negative for x>0, m>0: no real arc)"];

(* ---------- 8. does integral_0^b dx/Sqrt(1+x^m) equal a fixed value independent of b? ---------- *)
Print["\n--- I0(b) = int_0^b dx/Sqrt[1+x^m] is strictly increasing (m=10) ---"];
Print["I0(0.446)= ", NumberForm[ik10b[0.4463338855175907289381314252826248172], 20]];
Print["I0(0.790)= ", NumberForm[ik10b[0.7907068936276048430784], 20]];
Print["I0(3.015)= ", NumberForm[ik10b[3.0151518126393099839], 20]];
Print["(1/10)B(1/10,3/10) over unbounded = ", NumberForm[(1/10) Beta[1/10, 2/5], 25]];

(* ---------- 9. Legendre relation at k=1/Sqrt[2] (Q4 sanity) ---------- *)
Print["\n--- Legendre relation at k=1/Sqrt[2] ---"];
k = 1/Sqrt[2];
Print[EllipticK[k^2] EllipticE[1 - k^2] + EllipticK[1 - k^2] EllipticE[k^2] -
   EllipticK[k^2] EllipticK[1 - k^2] - Pi/2];

(* ---------- 10. Kummer/other m=10 signatures? Gauss 2F1(1/10,9/10;1;1/2) ---------- *)
Print["\n--- 2F1(1/10,9/10;1;1/2) via Gauss second theorem ---"];
v = Sqrt[Pi]/(Gamma[(1 + 1/10)/2] Gamma[1 - (1/10)/2]);
Print["value = ", NumberForm[v, 30]];
Print["2F1 = ", NumberForm[Hypergeometric2F1[1/10, 9/10, 1, 1/2], 30]];
Print["difference = ", NumberForm[v - Hypergeometric2F1[1/10, 9/10, 1, 1/2], 25]];
Print["Gamma product Gamma[11/20]Gamma[19/20] = ", NumberForm[Gamma[11/20] Gamma[19/20], 30]];

Print["\ndone"];
