(* Thread T6 (TEXT-WARP-THEORY.md section 13): the arc length of a warped slanted edge.
   Warp Up, 4 x 4 box, handle 3/4: top guide = upper half of the ellipse with centre (2, 1),
   semi-axes (2, 1); B = T + (0, 3); psi = angle from the left end; kappa = 3/L, L = 2 EllipticE[-3].
   Edge v = u (the hypotenuse of U+25E3):  x = 2 - 2 Cos[psi],  y = 1 - Sin[psi] + kappa E(psi | -3).
   Edge v = 1 - u (the hypotenuse of U+25E2): y = 4 - Sin[psi] - kappa E(psi | -3).  Same length
   by psi -> Pi - psi. *)
Lh = 2 EllipticE[-3`70];
kap = 3/Lh;
sp[psi_] := Sqrt[1 + 3 Sin[psi]^2];
speedUp[psi_] := Sqrt[4 Sin[psi]^2 + (-Cos[psi] + kap sp[psi])^2];     (* v = u *)
speedDn[psi_] := Sqrt[4 Sin[psi]^2 + (-Cos[psi] - kap sp[psi])^2];     (* v = 1 - u *)
nint[f_] := NIntegrate[f[psi], {psi, 0, Pi}, WorkingPrecision -> 60, PrecisionGoal -> 50, MaxRecursion -> 30];
N1 = nint[speedUp]; N2 = nint[speedDn];
Print["N1 (v = u)     = ", N1];
Print["N2 (v = 1 - u) = ", N2];
Print["difference     = ", N[N1 - N2, 5]];
(* speed^2 = sp^2 (1 + k^2) - 2 k Cos sp: nested radical in c = Cos[psi] *)
Print["identity check: ", N[speedUp[0.7]^2 - ((1 + kap^2) sp[0.7]^2 - 2 kap Cos[0.7] sp[0.7]), 10]];
(* denesting needs P^2 - Q^2 R a square: P = (1+k^2)(4-3c^2), Q = -2kc, R = 4-3c^2 *)
Print["P^2 - Q^2 R = ", Factor[((1 + k^2) (4 - 3 c^2))^2 - (2 k c)^2 (4 - 3 c^2)]];
(* circle control: semi-axes (1, 1): speed^2 = (1+k^2) - 2 k Cos psi, elliptic *)
kc = 3/Pi;
Print["circle control: ", NIntegrate[Sqrt[(1 + kc^2) - 2 kc Cos[psi]], {psi, 0, Pi}, WorkingPrecision -> 30],
  " vs 2 Sqrt[a+b] E[2b/(a+b)] = ", N[2 Sqrt[1 + kc^2 + 2 kc] EllipticE[4 kc/(1 + kc^2 + 2 kc)], 30]];
