(* Thread T6, section 13.1: is the genus-2 curve  Z^2 = t (t - t0)(t^2 + 1)(3 t^2 - 1)  of the form
   Z^2 = 1 + q(x)^2  (q a cubic: the arc-length curve of a degree-4 polynomial graph)?

   Fact used: Z^2 = 1 + q^2 with q a cubic exists iff the six branch points split into two triples
   T1, T2 and, in some coordinate (the pole p of q moved to infinity), the monic cubics with roots T1
   and T2 differ by a constant, i.e. have equal sums of roots and equal sums of pairwise products.
   For a finite pole p the roots become 1/(r - p).
   Tested on the control q = x^3 - 2x (residual 0 at infinity and after moving the pole to p = 3). *)

(* ---- part 1: our curve, numerically at 60 and 120 digits ---- *)
(* kap = 3/(2 EllipticE[-3]); t0 = 2 kap/(Sqrt[3](1 + kap^2)) = 0.516867565868...
   roots = {0, t0, I, -I, 1/Sqrt[3], -1/Sqrt[3]}
   - no nontrivial Moebius automorphism of the six-point set (0 of 719 permutations); the control
     (sixth roots of unity) has 11.
   - best partition {0, i, -i} | {t0, 1/Sqrt[3], -1/Sqrt[3]} with p = -5.5233608...: e2 residual
     0.00146 absolute, 0.0154 relative, identical at 60 and 120 digits: a genuine miss. *)

(* ---- part 2: where the family meets the 1 + q^2 locus ---- *)
r = {0, s, I, -I, 1/Sqrt[3], -1/Sqrt[3]};
parts = DeleteDuplicates[Sort[{#, Complement[Range[6], #]}] & /@ Subsets[Range[6], {3}]];
degenerate[sv_] := MemberQ[Table[Abs[sv - x] < 10^-12, {x, {0, I, -I, 1/Sqrt[3], -1/Sqrt[3]}}], True];
cand = {};
Do[Module[{A = pr[[1]], B = pr[[2]], E1, E2, res, ss},
  E1 = Total[1/(r[[A]] - p)] - Total[1/(r[[B]] - p)];
  E2 = Total[Times @@@ Subsets[1/(r[[A]] - p), {2}]] - Total[Times @@@ Subsets[1/(r[[B]] - p), {2}]];
  res = Resultant[Numerator[Together[E1]], Numerator[Together[E2]], p];
  ss = s /. NSolve[res == 0, s, WorkingPrecision -> 40];
  cand = Join[cand, Select[ss, ! degenerate[#] &]];
  Module[{d1 = Total[r[[A]]] - Total[r[[B]]],
          d2 = Total[Times @@@ Subsets[r[[A]], {2}]] - Total[Times @@@ Subsets[r[[B]], {2}]], sol},
    sol = Quiet[Solve[d1 == 0 && d2 == 0, s]];
    If[sol =!= {} && Head[sol] === List,
      cand = Join[cand, Select[N[s /. sol, 30], ! degenerate[#] &]]]]],
 {pr, parts}];
cand = DeleteDuplicates[N[cand, 20], Abs[#1 - #2] < 10^-10 &];
Print[Length[cand], " candidate t0 values (6 real: +-2/Sqrt[3], +-3 Sqrt[3]/7, +-0.335657855782)"];
(* the e1 resultants factor as, e.g., (2 Sqrt[3] + 3 s)(73 s^3 + 3 Sqrt[3] s^2 + 9 s + 3 Sqrt[3]) for the
   partition {1,2,5}|{3,4,6}, (3 Sqrt[3] - 7 s)(3 Sqrt[3] + 7 s) for {1,5,6}|{2,3,4}, ... *)
(* our t0 = 0.516867565868: nearest candidate at distance 0.111157 *)
