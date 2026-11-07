(* Thread T1 test (TEXT-WARP-THEORY.md section 12). Wolfram Language, 130-digit working precision.
   Warp Up in a 4 x 4 box at handle 3/4: top guide = upper half of the ellipse with centre (2, 1),
   semi-axes (2, 1); B = T + (0, 3). The glyph edge is the diagonal v = u of the unit square.
   Its image (psi = phi - Pi in [0, Pi], arc length measured from the left end):
     x = 2 - 2 Cos[psi],  y = 1 - Sin[psi] + kappa EllipticE[psi, -3],  kappa = 3 / L,
   L = 2 EllipticE[-3] the half-ellipse's arc length. *)
Lh = 2 EllipticE[-3`130];
kap = 3/Lh;
yf[psi_] := 1 - Sin[psi] + kap EllipticE[psi, -3];
f[psi_] := yf[psi] - ((2 - 2 Cos[psi])/2 + 3/2);     (* line y = x/2 + 3/2 *)
r = psi /. FindRoot[f[psi], {psi, 2.8`130}, WorkingPrecision -> 125, AccuracyGoal -> 110,
      PrecisionGoal -> 110];
rel[v_, deg_] := Quiet[Check[FindIntegerNullVector[Table[v^k, {k, 0, deg}], 10^5], "none"]];
res[v_, deg_] := With[{o = rel[v, deg]}, If[ListQ[o], o, "no relation"]];
Print["control, Cos[2Pi/13], deg 6: ", res[N[Cos[2 Pi/13], 125], 6]];     (* found *)
Print["control, Sqrt[2]+Pi, deg 8: ", res[N[Sqrt[2] + Pi, 125], 8]];     (* none *)
Print["cos psi*, deg 4/8/12: ", res[Cos[r], 4], " | ", res[Cos[r], 8], " | ", res[Cos[r], 12]];
Print["x* = 2-2cos, deg 8/12: ", res[2 - 2 Cos[r], 8], " | ", res[2 - 2 Cos[r], 12]];
Print["psi*, deg 8/12: ", res[r, 8], " | ", res[r, 12]];
(* extreme: dy/dpsi = -Cos psi + kappa Sqrt[1 + 3 Sin^2 psi] = 0  =>  Cos^2 = 4k^2/(1 + 3k^2) *)
Print["extreme: cos^2 - 4k^2/(1+3k^2) = ",
  N[Cos[psi /. FindRoot[-Cos[psi] + kap Sqrt[1 + 3 Sin[psi]^2], {psi, 0.56`130},
      WorkingPrecision -> 125]]^2 - 4 kap^2/(1 + 3 kap^2), 5]];
