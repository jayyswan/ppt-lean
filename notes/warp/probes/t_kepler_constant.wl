(* Section 14.4: the Warp Up diagonal constant delta_W.
   Black Lower Right Triangle (U+25E2) in a square box, Warp Up at its default handle 85714,
   the hypotenuse v = 1 - u against the box diagonal y = x. Scale-invariant: any square box. *)
frac[w_] := Module[{h = w, a = 85714/100000, Ax, dd, Bx, mu, s, Lh, X, Y, f, r, tau, kap, Phi},
  Ax = w/2; dd = (1 - a) h; Bx = dd; tau = h - dd;
  mu = -(Ax^2 - Bx^2)/Bx^2;                         (* s(psi) = Bx EllipticE[psi, mu] *)
  s[psi_] := Bx EllipticE[psi, mu]; Lh = s[Pi];
  X[psi_] := Ax (1 - Cos[psi]);
  Y[psi_] := dd - Bx Sin[psi] + tau (1 - s[psi]/Lh);
  f[psi_] := Y[psi] - X[psi];
  r = psi /. FindRoot[f[psi], {psi, 1.5}, WorkingPrecision -> 60];
  (* the Kepler form: kappa E(psi|mu) - B sin psi + lambda A cos psi = c0, kappa = tau sigma B/L, sigma = -1 *)
  kap = -tau Bx/Lh;
  Phi[psi_] := kap EllipticE[psi, mu] - Bx Sin[psi] + Ax Cos[psi];
  {N[r, 40], N[X[r]/w, 40], N[Phi[r] - (Ax - dd - tau), 5],
   Length[Select[Partition[Table[Sign[f[t]], {t, 0, N[Pi, 20], N[Pi, 20]/2000}], 2, 1], #[[1]] != #[[2]] &]]}];
Print[frac[288]];     (* psi*, delta_W, Kepler residual (0), number of crossings (1) *)
Print[frac[72][[2]], "  ", frac[1000][[2]]];
(* min handle stop 66667: delta = 0.3943289301622131448248201... (same code with a = 66667/100000) *)
