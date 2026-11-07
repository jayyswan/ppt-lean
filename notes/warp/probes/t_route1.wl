(* Section 14.6, route 1: the pure cubic guide y = x^3.
   Fact 1: J(T) = (T/3) Sqrt[1 + 9 T^4] + (2/3) Int_0^T dx/Sqrt[1 + 9 x^4]; the tangent at (T, T^3) meets the
   x-axis at 2T/3, at distance (T/3) Sqrt[Q(T)] from the point (the boundary term).
   Fact 2: for an even quartic Q = a Z^4 + b Z^2 + c,
           Int Sqrt[Q] = Z Sqrt[Q]/3 + (1/3) Int (b Z^2 + 2 c)/Sqrt[Q];  the Wave guide has b = -6 k^2 != 0.
   Both were checked to 24-29 digits (T = 0.8; k = 1.3, Z = 0.6). *)
Q[x_] := 1 + 9 x^4;
T0 = 0.8`40;
J = NIntegrate[Sqrt[Q[x]], {x, 0, T0}, WorkingPrecision -> 30];
Bd = T0 Sqrt[Q[T0]]/3;
Phi = (2/3) NIntegrate[1/Sqrt[Q[x]], {x, 0, T0}, WorkingPrecision -> 30];
Print["J - (boundary + first kind) = ", N[J - Bd - Phi, 5]];
xint = T0 - T0^3/(3 T0^2);
Print["tangent distance to the x-axis = ", Sqrt[(T0 - xint)^2 + T0^6], "  boundary term = ", Bd];
k = 1.3`30; Z0 = 0.6`30;
QW[z_] := 1 + (k (3 z^2 - 1))^2;
lhs = NIntegrate[Sqrt[QW[z]], {z, 0, Z0}, WorkingPrecision -> 25];
rhs = Z0 Sqrt[QW[Z0]]/3 + (1/3) NIntegrate[(-6 k^2 z^2 + 2 (1 + k^2))/Sqrt[QW[z]], {z, 0, Z0}, WorkingPrecision -> 25];
Print["reduction check: ", N[lhs - rhs, 5]];
(* The obstruction for a glyph-circle crossing: p^2 + (kappa0 X)^2 + (3 c kappa0 X^3)^2 = (tau r)^2 would be a sum of
   squares of real polynomials equal to a constant, impossible. *)
