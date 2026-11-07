(* Section 14.7, route 3: which cubic-guide heights are "first kind + algebraic".
   For Q = q0 + q1 X + q2 X^2 + q3 X^3 + q4 X^4:
     Int Sqrt[Q] = [(X/3 + q3/(12 q4)) Sqrt[Q]] + Int (c0 + c1 X + c2 X^2)/Sqrt[Q]
   with c0, c1, c2 below; verified to 24 digits on two random quartics. *)
red[{q0_, q1_, q2_, q3_, q4_}] := {(2 q0 - q1 q3/(8 q4))/3, (3 q1/2 - q2 q3/(4 q4))/3, (q2 - 3 q3^2/(8 q4))/3};
check[qs_, T_] := Module[{Qf, c, lhs, rhs},
  Qf[x_] := qs.{1, x, x^2, x^3, x^4}; c = red[qs];
  lhs = NIntegrate[Sqrt[Qf[x]], {x, 0, T}, WorkingPrecision -> 25];
  rhs = ((T/3 + qs[[4]]/(12 qs[[5]])) Sqrt[Qf[T]] - (qs[[4]]/(12 qs[[5]])) Sqrt[Qf[0]]) +
    NIntegrate[(c[[1]] + c[[2]] x + c[[3]] x^2)/Sqrt[Qf[x]], {x, 0, T}, WorkingPrecision -> 25];
  N[lhs - rhs, 5]];
Print[check[{2.1`30, 0.7`30, -0.4`30, 0.3`30, 1.3`30}, 0.9`30]];
Print[check[{1.5`30, -0.9`30, 1.1`30, 0.6`30, 0.8`30}, 1.2`30]];
(* pure first kind iff c1 = c2 = 0, for g' = al x^2 + be x + ga and Q = 1 + g'^2 *)
qs = CoefficientList[1 + (al x^2 + be x + ga)^2, x];
Print[FullSimplify[Solve[(red[qs][[2]] == 0) && (red[qs][[3]] == 0), {be, ga}, Reals]]];
(* -> ga = be^2/(4 al) (g' a perfect square), or be = ga = 0.  Wave: g' ~ 3 Z^2 - 1, discriminant 12;
   Curve top: g' ~ 3/4 - 9/2 X + 3/2 X^2, discriminant 63/4: neither vanishes. *)
Print[{Discriminant[3 z^2 - 1, z], Discriminant[3/4 - 9/2 x + 3/2 x^2, x]}];
