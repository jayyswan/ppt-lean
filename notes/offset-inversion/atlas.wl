(* ::Package:: *)

(* =====================================================================
   atlas.wl  --  W0 offset-inversion atlas (Wolfram Language)
   ---------------------------------------------------------------------
   Purpose: the standard toolbox that every later offset-inversion
   stream loads with

       Get["C:/dev/Powerpoint/lean/notes/offset-inversion/atlas.wl"]

   at the top of its single computation.  Nothing here depends on
   session state: the file defines every symbol it uses.  All names
   live in the default Global` context, so that

       Get[ "...atlas.wl" ];  whewell[ parabolaCurve[], w ]

   works inside ONE cell (the whole cell is parsed before Get runs, so
   a package context would leave the later names unresolved).

   The file uses the symbols oaT and oaTau internally; do not assign
   values to them.  Public functions always return expressions in the
   symbol you pass in.

   Curve representation
   --------------------
   A curve is an Association

       <| "name"    -> string,
          "param"   -> Function[t, {x(t), y(t)}],      (* mandatory *)
          "tmin"    -> real or -Infinity,              (* optional *)
          "tmax"    -> real or  Infinity,              (* optional *)
          "sbase"   -> real, default 0,                (* optional *)
          "assumptions" -> list of assumptions on t     (* optional *) |>

   Build one with mkCurve.  A bare Function[t,...] or an expression
   pair {x, y} (plus its variable) is also accepted everywhere and is
   normalised internally, so all of

       parabolaCurve[]
       mkCurve[Function[t, {t, t^2/2}]]
       mkCurve[{t, t^2/2}, t]

   are the same curve.

   Conventions
   -----------
   *  psi(t) = ArcTan[x'(t), y'(t)]   (two-argument ArcTan: angle of
      the velocity vector, measured from +x).
   *  speed(t) = Sqrt[x'^2 + y'^2] >= 0.
   *  curvature(t) = (x' y'' - y' x'') / speed^3   (signed).
   *  unit normal n = (-y', x')/speed  (left normal), so that the
      offset is P_d = gamma + d n and
          P_d' = (1 - d kappa) gamma' ,
      hence speed(P_d) = |1 - d kappa| * speed(gamma).
   *  The Whewell function is s = R(psi), i.e. whewell returns
      {psi(t), s(t)} with s measured from the curve's "sbase".
   *  offsetArc returns the *signed* integral Int_{t0}^{t1}
      |1-d kappa(t)| speed(t) dt (NIntegrate convention): it is the
      arc length when t0 < t1 and minus the arc length when t0 > t1.
      This is exactly what the inversion routine needs.

   Everything numeric is done at WorkingPrecision (default 40 for
   offsetArc, 30 for offsetInvert, 40 for checkIdentity).
   ===================================================================== *)

$atlasVersion = "W0-1.0 (2026-11-03)";

(* ------------------------------------------------------------------ *)
(* usage                                                              *)
(* ------------------------------------------------------------------ *)

mkCurve::usage =
  "mkCurve[Function[t,{x,y}], opts] or mkCurve[{x,y}, t, opts] builds the \
curve Association with keys name, param, tmin, tmax, sbase, assumptions. \
Options are given as rules, e.g. \"tmin\" -> 0.";

curveQ::usage = "curveQ[c] is True if c is a normalised curve Association.";

whewell::usage =
  "whewell[curve, t] gives {psi(t), s(t)}: the tangent angle and the arc \
length measured from the curve's sbase (default 0). Symbolic where \
possible; if Integrate fails s is an unevaluated Integrate, which still \
evaluates numerically via N.";

speed::usage = "speed[curve, t] gives the speed Sqrt[x'^2+y'^2] of the curve.";
curvature::usage = "curvature[curve, t] gives the signed curvature (x'y''-y'x'')/speed^3.";
tangentAngle::usage = "tangentAngle[curve, t] gives psi(t) = ArcTan[x'(t), y'(t)].";
normalVector::usage = "normalVector[curve, t] gives the left unit normal (-y',x')/speed.";
offsetCurve::usage =
  "offsetCurve[curve, d] returns the curve gamma + d n (left normal), as a \
curve Association. d may be negative.";

offsetArc::usage =
  "offsetArc[curve, d, {t0, t1}] numerically integrates \
|1 - d kappa(t)| * speed(t) over [t0,t1] at WorkingPrecision (default 40). \
Signed NIntegrate convention: negative if t1 < t0. Option Method -> \
\"Formula\" (default) uses |1-d kappa| speed; Method -> \"Direct\" integrates \
the speed of the actual offset parametrisation Sqrt[P_d'.P_d']; the two must \
agree. Cusps of the offset are located automatically and passed to \
NIntegrate as Exclusions.";

cuspParams::usage =
  "cuspParams[curve, d, {a, b}] returns the sorted list of parameters in \
[a,b] where 1 - d kappa(t) vanishes (offset cusps / vertices of the offset).";

offsetInvert::usage =
  "offsetInvert[curve, d, t0, x] solves offsetArc[curve,d,{t0,t1}] == x for \
t1, searching in the monotone window that contains t0 and continuing across \
cusps if x is larger than the current window's arc. Returns an Association \
with keys t1, arc, residual, cuspsCrossed, window, offsetPoint, converged, \
direction. Options: WorkingPrecision (30), \"Direction\" (1 or -1), \
\"SearchRange\" (Automatic).";

checkIdentity::usage =
  "checkIdentity[lhs, rhs, pts] evaluates lhs-rhs at 40-digit working \
precision at each point of pts (a list of rule lists, e.g. \
{{w -> 7/10}, {w -> 3}}) and returns <|residuals -> signed residuals, \
maxAbs -> Max[Abs[...]], workingPrecision -> wp|>.";

parabolaCurve::usage = "parabolaCurve[] is y = x^2/2 parametrised as (t, t^2/2).";
parabolaWhewell::usage = "parabolaWhewell[w] = (w Sqrt[1+w^2] + ArcSinh[w])/2, the Whewell function of y=x^2/2 in the slope w = tan psi.";
parabolaOffsetArc::usage = "parabolaOffsetArc[w, d] = parabolaWhewell[w] - d ArcTan[w], the offset arc length L_d(w) of y=x^2/2 from the vertex.";

powerLawCurve::usage = "powerLawCurve[a, p] is y = a x^p parametrised as (t, a t^p); domain t > 0 by default.";
ellipseCurve::usage = "ellipseCurve[a, b] is (a Cos[t], b Sin[t]), t in [0, 2 Pi].";
expCurve::usage = "expCurve[] is (t, Exp[t]).";
shearedSineCurve::usage = "shearedSineCurve[a, b] is (-b t + Sin[t], a t).";
cubicBezierCurve::usage = "cubicBezierCurve[p0, p1, p2, p3] is the cubic Bezier with those control points, t in [0,1].";

parabolaSelfTest::usage =
  "parabolaSelfTest[] runs the W0 acceptance test on y = x^2/2: symbolic \
checks of R'(w) = Sqrt[1+w^2] and of the offset arc element, numerical \
residuals of L_d(w) against offsetArc for d in {1/2,-3,9/10}, \
w in {7/10,3}, cusp and monotonicity checks for d < 1, and one offsetInvert \
recovery. Returns an Association; also Prints a readable report.";

(* ------------------------------------------------------------------ *)
(* curve representation                                               *)
(* ------------------------------------------------------------------ *)

mkCurve[f_Function, opts___Rule] :=
  Join[<|"name" -> "unnamed", "param" -> f,
         "tmin" -> -Infinity, "tmax" -> Infinity,
         "sbase" -> 0, "assumptions" -> {}|>,
       Association[opts]];

mkCurve[{x_, y_}, v_Symbol, opts___Rule] := mkCurve[Function[v, {x, y}], opts];

oaAsCurve[c_] := Which[
  AssociationQ[c] && KeyExistsQ[c, "param"], c,
  MatchQ[c, _Function], mkCurve[c],
  True, c];

curveQ[c_] := AssociationQ[oaAsCurve[c]] && KeyExistsQ[oaAsCurve[c], "param"] &&
   MatchQ[oaAsCurve[c]["param"], _Function];

oaParam[c_] := oaAsCurve[c]["param"];

oaX[c_] := oaParam[c][oaT][[1]];
oaY[c_] := oaParam[c][oaT][[2]];
oaDx[c_] := D[oaX[c], oaT];
oaDy[c_] := D[oaY[c], oaT];

oaSpeedT[c_] := Sqrt[oaDx[c]^2 + oaDy[c]^2];
oaPsiT[c_] := ArcTan[oaDx[c], oaDy[c]];
oaKappaT[c_] := (oaDx[c] D[oaDy[c], oaT] - oaDy[c] D[oaDx[c], oaT]) / oaSpeedT[c]^3;
oaNormalT[c_] := {-oaDy[c], oaDx[c]} / oaSpeedT[c];

(* public, expressed in the caller's symbol *)
speed[c_, v_Symbol] := oaSpeedT[c] /. oaT -> v;
tangentAngle[c_, v_Symbol] := oaPsiT[c] /. oaT -> v;
curvature[c_, v_Symbol] := oaKappaT[c] /. oaT -> v;
normalVector[c_, v_Symbol] := oaNormalT[c] /. oaT -> v;

(* ------------------------------------------------------------------ *)
(* Whewell function                                                   *)
(* ------------------------------------------------------------------ *)

whewell::timeout = "Symbolic integration timed out; returning an unevaluated Integrate.";

whewell[c_, v_Symbol] := Module[{cc, sp, base, s},
  cc = oaAsCurve[c];
  sp = oaSpeedT[cc];
  base = cc["sbase"];
  s = TimeConstrained[
        Integrate[sp, {oaTau, base, oaT},
          Assumptions -> cc["assumptions"]],
        30,
        Message[whewell::timeout];
        Inactive[Integrate][sp, {oaTau, base, oaT}]];
  {oaPsiT[cc], s} /. oaT -> v];

(* ------------------------------------------------------------------ *)
(* offsets                                                            *)
(* ------------------------------------------------------------------ *)

offsetCurve[c_, d_] := Module[{cc = oaAsCurve[c], xx, yy, nn},
  xx = oaX[cc]; yy = oaY[cc]; nn = oaNormalT[cc];
  mkCurve[Function[oaT, {xx + d nn[[1]], yy + d nn[[2]]}],
    "name" -> "offset[" <> ToString[cc["name"]] <> "," <> ToString[d] <> "]",
    "sbase" -> cc["sbase"],
    "tmin" -> cc["tmin"], "tmax" -> cc["tmax"],
    "assumptions" -> cc["assumptions"]]];

offsetPoint[c_, d_, tv_?NumericQ] :=
  Module[{cc = oaAsCurve[c]}, N[oaParam[offsetCurve[cc, d]][tv], 40]];

(* ------------------------------------------------------------------ *)
(* cusps: zeros of 1 - d kappa                                        *)
(* ------------------------------------------------------------------ *)

cuspParams::range = "cuspParams needs a finite range; got `1`.";

cuspParams[c_, d_, {a0_, b0_}] := Module[
  {a, b, n = 400, xs, g, vals, cand, roots, tt},

  a = Min[a0, b0]; b = Max[a0, b0];
  If[! NumericQ[a] || ! NumericQ[b] || a === -Infinity || b === Infinity,
    Message[cuspParams::range, {a, b}]; Return[{}]];
  If[b - a < 10^-30, Return[{}]];

  g[tt_] := 1 - d*(oaKappaT[c] /. oaT -> tt);

  xs = N[Subdivide[a, b, n]];
  vals = Map[g, xs];

  (* brackets around sign changes, and exact zeros at the nodes *)
  cand = Table[
    Which[
      ! (NumericQ[vals[[i]]] && NumericQ[vals[[i + 1]]]), Nothing,
      vals[[i]] == 0, {xs[[i]], xs[[i]]},
      vals[[i + 1]] == 0, {xs[[i + 1]], xs[[i + 1]]},
      vals[[i]]*vals[[i + 1]] < 0, {xs[[i]], xs[[i + 1]]},
      True, Nothing],
    {i, 1, Length[xs] - 1}];

  If[cand === {}, Return[{}]];

  roots = Map[
    Function[br,
      If[br[[1]] == br[[2]], br[[1]],
        Quiet[tt /. FindRoot[g[tt] == 0,
           {tt, (br[[1]] + br[[2]])/2, br[[1]], br[[2]]}]]]],
    cand];

  roots = Select[roots, NumericQ[#] && Abs[g[#]] < 10^-15 &];

  Sort[DeleteDuplicates[roots, Abs[#1 - #2] < 10^-8 &]]];

(* ------------------------------------------------------------------ *)
(* offset arc length                                                  *)
(* ------------------------------------------------------------------ *)

Options[offsetArc] = {
  WorkingPrecision -> 40,
  Method -> "Formula",
  "Exclusions" -> Automatic,
  MaxRecursion -> 20};

offsetArc[c_, d_, {t0_?NumericQ, t1_?NumericQ}, OptionsPattern[]] := Module[
  {wp, meth, excl, exclCond, integrand, tt},

  wp = OptionValue[WorkingPrecision];
  meth = OptionValue[Method];
  excl = OptionValue["Exclusions"];

  If[excl === Automatic, excl = cuspParams[c, d, {t0, t1}]];
  excl = Select[excl, NumericQ];

  integrand = Switch[meth,
    "Direct", oaSpeedT[offsetCurve[c, d]],
    "Formula", Abs[1 - d*oaKappaT[c]]*oaSpeedT[c],
    _, Abs[1 - d*oaKappaT[c]]*oaSpeedT[c]];

  exclCond = If[excl === {}, None, Map[tt == # &, excl]];

  NIntegrate[integrand /. oaT -> tt, {tt, t0, t1},
    WorkingPrecision -> wp + 10,
    PrecisionGoal -> wp + 7,
    AccuracyGoal -> wp + 10,
    MaxRecursion -> OptionValue[MaxRecursion],
    Exclusions -> exclCond,
    Method -> "GlobalAdaptive"] // N[#, wp] &];

(* ------------------------------------------------------------------ *)
(* inversion                                                          *)
(* ------------------------------------------------------------------ *)

Options[offsetInvert] = {
  WorkingPrecision -> 30,
  "Direction" -> 1,
  "SearchRange" -> Automatic,
  "MaxBisections" -> Automatic};

offsetInvert::range = "offsetInvert needs a finite search range; using t0 plus-minus 10.";
offsetInvert::unreachable = "x = `1` exceeds the offset arc available from t0 = `2` to `3`.";

offsetInvert[c_, d_, t0_, x_, OptionsPattern[]] := Module[
  {wp, dir, rng, a, b, end, cusps, cuts, wins, arcs, cum, k, target,
   ws, we, left, right, mid, fm, t1, arc, resid, crossed, tol, iter, cc,
   maxIter},

  wp = OptionValue[WorkingPrecision];
  dir = OptionValue["Direction"];
  cc = oaAsCurve[c];

  rng = OptionValue["SearchRange"];
  If[rng === Automatic, rng = {cc["tmin"], cc["tmax"]}];
  If[! NumericQ[rng[[1]]] || rng[[1]] === -Infinity, rng[[1]] = t0 - 10];
  If[! NumericQ[rng[[2]]] || rng[[2]] === Infinity, rng[[2]] = t0 + 10];
  a = Min[rng]; b = Max[rng];
  If[t0 < a || t0 > b, Message[offsetInvert::range]; a = Min[a, t0]; b = Max[b, t0]];

  end = If[dir >= 0, b, a];
  cusps = cuspParams[c, d, {t0, end}];

  cuts = Join[{t0}, cusps, {end}];
  cuts = If[dir >= 0, Sort[cuts], Sort[cuts, Greater]];

  wins = Partition[cuts, 2, 1];
  If[wins === {}, Return[<|"t1" -> t0, "arc" -> 0, "residual" -> -x,
      "cuspsCrossed" -> {}, "window" -> {t0, t0},
      "offsetPoint" -> offsetPoint[c, d, t0], "converged" -> (x == 0),
      "direction" -> dir|>]];

  arcs = Map[Abs[offsetArc[c, d, #, WorkingPrecision -> wp,
        "Exclusions" -> {}]] &, wins];
  cum = Accumulate[arcs];

  k = SelectFirst[Range[Length[cum]], cum[[#]] >= x &, None];
  If[k === None,
    Message[offsetInvert::unreachable, x, t0, end];
    Return[<|"t1" -> end,
      "arc" -> Abs[offsetArc[c, d, {t0, end}, WorkingPrecision -> wp]],
      "residual" -> Abs[offsetArc[c, d, {t0, end}, WorkingPrecision -> wp]] - x,
      "cuspsCrossed" -> cusps, "window" -> {t0, end},
      "offsetPoint" -> offsetPoint[c, d, end], "converged" -> False,
      "direction" -> dir|>]];

  target = x - If[k == 1, 0, cum[[k - 1]]];
  {ws, we} = wins[[k]];

  (* bisection on the monotone window: F(s) = |arc(ws -> s)| is strictly
     increasing in the traversal direction *)
  left = N[ws, wp]; right = N[we, wp];
  tol = 10^-wp;
  maxIter = OptionValue["MaxBisections"];
  If[maxIter === Automatic,
    maxIter = Min[Ceiling[Log[2, Max[Abs[we - ws], 1]/tol]] + 5, 4*wp + 60]];
  iter = 0;
  While[Abs[right - left] > tol*Max[1, Abs[left]] &&
        iter < maxIter,
    iter++;
    mid = N[(left + right)/2, wp];
    fm = Abs[offsetArc[c, d, {ws, mid}, WorkingPrecision -> wp,
           "Exclusions" -> {}]] - target;
    If[fm < 0, left = mid, right = mid]];
  t1 = N[(left + right)/2, wp];

  arc = Abs[offsetArc[c, d, {t0, t1}, WorkingPrecision -> wp]];
  resid = arc - x;
  crossed = If[dir >= 0,
    Select[cusps, t0 < # < t1 &],
    Select[cusps, t1 < # < t0 &]];

  <|"t1" -> t1,
    "arc" -> arc,
    "residual" -> resid,
    "cuspsCrossed" -> crossed,
    "window" -> {ws, t1},
    "offsetPoint" -> offsetPoint[c, d, t1],
    "converged" -> (Abs[resid] < 10^(3 - wp)),
    "direction" -> dir,
    "bisections" -> iter|>];

(* ------------------------------------------------------------------ *)
(* 40-digit identity checker                                          *)
(* ------------------------------------------------------------------ *)

Options[checkIdentity] = {WorkingPrecision -> 40};

checkIdentity[lhs_, rhs_, pts_List, OptionsPattern[]] := Module[
  {wp, pl, res},

  wp = OptionValue[WorkingPrecision];
  Block[{$MaxExtraPrecision = 20000},
    pl = Map[
       Function[pt,
         Map[Function[rule,
            rule[[1]] -> SetPrecision[rule[[2]], wp + 10]], pt]],
       pts];
    res = Map[
       Function[pt,
         With[{l = SetPrecision[(lhs /. pt), wp + 10],
               r = SetPrecision[(rhs /. pt), wp + 10]},
           N[l - r, wp]]],
       pl]];

  <|"residuals" -> res,
    "maxAbs" -> If[res === {}, 0, Max[Abs[res]]],
    "workingPrecision" -> wp|>];

checkIdentity[lhs_, rhs_, pt_Rule, opts___Rule] :=
  checkIdentity[lhs, rhs, {pt}, opts];

(* ------------------------------------------------------------------ *)
(* curve library                                                      *)
(* ------------------------------------------------------------------ *)

parabolaCurve[] := mkCurve[Function[t, {t, t^2/2}],
  "name" -> "parabola y=x^2/2", "tmin" -> -Infinity, "tmax" -> Infinity,
  "sbase" -> 0];

parabolaWhewell[w_] := (w*Sqrt[1 + w^2] + ArcSinh[w])/2;
parabolaOffsetArc[w_, d_] := parabolaWhewell[w] - d*ArcTan[w];

powerLawCurve[a_, p_] := mkCurve[Function[t, {t, a t^p}],
  "name" -> "power law y=" <> ToString[a] <> " x^" <> ToString[p],
  "tmin" -> 0, "tmax" -> Infinity, "sbase" -> 0,
  "assumptions" -> {t > 0}];

ellipseCurve[a_, b_] := mkCurve[Function[t, {a Cos[t], b Sin[t]}],
  "name" -> "ellipse (" <> ToString[a] <> "," <> ToString[b] <> ")",
  "tmin" -> 0, "tmax" -> 2 Pi, "sbase" -> 0];

expCurve[] := mkCurve[Function[t, {t, Exp[t]}],
  "name" -> "exp (t, e^t)", "tmin" -> -Infinity, "tmax" -> Infinity,
  "sbase" -> 0];

shearedSineCurve[a_, b_] := mkCurve[Function[t, {-b t + Sin[t], a t}],
  "name" -> "sheared sine (-" <> ToString[b] <> "t+sin t, " <> ToString[a] <> "t)",
  "tmin" -> -Infinity, "tmax" -> Infinity, "sbase" -> 0];

cubicBezierCurve[p0_, p1_, p2_, p3_] := mkCurve[
  Function[t, (1 - t)^3 p0 + 3 (1 - t)^2 t p1 + 3 (1 - t) t^2 p2 + t^3 p3],
  "name" -> "cubic Bezier", "tmin" -> 0, "tmax" -> 1, "sbase" -> 0];

(* ------------------------------------------------------------------ *)
(* acceptance test                                                    *)
(* ------------------------------------------------------------------ *)

parabolaSelfTest[] := Module[
  {gw = Global`w, gd = Global`d,
   symR, symL, symAbs, symPsi, symJac, kappaMax, derivG, signReduce,
   derivVals, cuspLess1, cuspEq1, cuspGt1, tests, rows, xtarget, inv,
   str, report, assoc},

  (* ---- 1. symbolic checks --- *)
  symR = FullSimplify[D[parabolaWhewell[gw], gw] - Sqrt[1 + gw^2]];

  symL = FullSimplify[
     D[parabolaWhewell[gw] - gd*ArcTan[gw], gw] -
       (Sqrt[1 + gw^2] - gd/(1 + gw^2))];

  (* psi' = kappa * speed  (the chain rule that turns dt into dw) *)
  symPsi = FullSimplify[
     D[ArcTan[oaT], oaT] - oaKappaT[parabolaCurve[]]*oaSpeedT[parabolaCurve[]]];

  (* for the graph parametrisation t = x = w, so dw/dt = 1 *)
  symJac = FullSimplify[D[Tan[ArcTan[oaT]], oaT] - 1];

  (* the Abs is resolved because 1 - d kappa > 0 for d < 1 *)
  symAbs = FullSimplify[
     (Sqrt[1 + gw^2] - gd/(1 + gw^2)) -
       Abs[1 - gd/(1 + gw^2)^(3/2)]*Sqrt[1 + gw^2],
     Assumptions -> Element[gw, Reals] && Element[gd, Reals] && gd < 1];

  (* ---- 3. cusps and monotonicity --- *)
  kappaMax = Maximize[{1/(1 + gw^2)^(3/2), Element[gw, Reals]}, gw];
  derivG = FullSimplify[D[gw*(1 - gd/Sqrt[1 + gw^2]), gw]];
  signReduce = Reduce[derivG > 0 && gd < 1 && Element[gw, Reals] &&
      Element[gd, Reals], {gw, gd}];

  derivVals = Table[
    {dd, ww, N[1 - dd/(1 + ww^2)^(3/2), 30]},
    {dd, {1/2, -3, 9/10}}, {ww, {7/10, 3}}];

  cuspLess1 = Table[{dd, cuspParams[parabolaCurve[], dd, {-5, 5}]},
     {dd, {1/2, -3, 9/10}}];
  cuspEq1 = cuspParams[parabolaCurve[], 1, {-5, 5}];
  cuspGt1 = Table[{dd, cuspParams[parabolaCurve[], dd, {-5, 5}]}, {dd, {2, 3}}];

  (* ---- 2. numerical residuals --- *)
  tests = Flatten[Table[{dd, ww}, {dd, {1/2, -3, 9/10}}, {ww, {7/10, 3}}], 1];

  rows = Map[
    Function[{pair},
      Module[{dd = pair[[1]], ww = pair[[2]], Lv, afv, adv, rf, rd},
        Lv = N[parabolaOffsetArc[ww, dd], 50];
        afv = offsetArc[parabolaCurve[], dd, {0, ww}, WorkingPrecision -> 50];
        adv = offsetArc[parabolaCurve[], dd, {0, ww}, WorkingPrecision -> 50,
                Method -> "Direct"];
        rf = N[Lv - afv, 50];
        rd = N[Lv - adv, 50];
        <|"d" -> dd, "w" -> ww,
          "Ld" -> Lv, "arcFormula" -> afv, "arcDirect" -> adv,
          "residualFormula" -> rf, "residualDirect" -> rd,
          "accuracyFormula" -> N[Accuracy[rf]],
          "accuracyDirect" -> N[Accuracy[rd]]|>]],
    tests];

  (* ---- offsetInvert round trip --- *)
  xtarget = N[parabolaOffsetArc[3, 1/2], 40];
  inv = offsetInvert[parabolaCurve[], 1/2, 0, xtarget,
     WorkingPrecision -> 30, "SearchRange" -> {0, 5}];

  assoc = <|
    "version" -> $atlasVersion,
    "symRprime" -> symR,
    "symArcElement" -> symL,
    "symPsiEqualsKappaSpeed" -> symPsi,
    "symJacobianDwDt" -> symJac,
    "symAbsResolved" -> symAbs,
    "kappaMax" -> kappaMax,
    "derivG" -> derivG,
    "derivPositiveReduce" -> signReduce,
    "derivValues" -> derivVals,
    "cuspsForDless1" -> cuspLess1,
    "cuspsForDequal1" -> cuspEq1,
    "cuspsForDgreater1" -> cuspGt1,
    "rows" -> rows,
    "minAccuracyFormula" -> Min[Lookup[rows, "accuracyFormula"]],
    "minAccuracyDirect" -> Min[Lookup[rows, "accuracyDirect"]],
    "invert" -> inv|>;

  (* ---- readable printout --- *)
  str[n_] := ToString[n, InputForm];
  report = {
    "=== atlas.wl " <> $atlasVersion <> " :: parabola self-test ===",
    "",
    "symbolic:",
    "  D[R(w),w] - Sqrt[1+w^2]                    = " <> str[symR],
    "  D[L_d(w),w] - (Sqrt[1+w^2] - d/(1+w^2))    = " <> str[symL],
    "  psi'(t) - kappa(t) speed(t)                = " <> str[symPsi],
    "  d/dt tan(psi(t)) - 1                       = " <> str[symJac],
    "  arc element, Abs resolved (d<1)            = " <> str[symAbs],
    "  Maximize[kappa]                            = " <> str[kappaMax],
    "  d/dw [w(1-d/Sqrt[1+w^2])]                  = " <> str[derivG],
    "  Reduce[deriv > 0, d<1]                     = " <> str[signReduce],
    "",
    "derivative 1 - d kappa(w) at the test points:",
    "  " <> str[derivVals],
    "",
    "cusps (zeros of 1-d kappa) on [-5,5]:",
    "  d<1  : " <> str[cuspLess1],
    "  d=1  : " <> str[cuspEq1],
    "  d>1  : " <> str[cuspGt1],
    "",
    "numerical residuals, L_d(w) vs offsetArc (50 digits):",
    "  d, w, L_d(w), arcFormula, residualFormula (0``a means zero to a digits), residualDirect"};

  report = Join[report,
    Map[Function[r,
       "  " <> str[r["d"]] <> ", " <> str[r["w"]] <> ", " <>
        str[r["Ld"]] <> ", " <> str[r["arcFormula"]] <> ", " <>
        str[r["residualFormula"]] <> " [acc " <>
        str[r["accuracyFormula"]] <> "], " <>
        str[r["residualDirect"]] <> " [acc " <>
        str[r["accuracyDirect"]] <> "]"],
      rows]];

  report = Join[report, {
    "",
    "offsetInvert round trip (d=1/2, target = L_{1/2}(3)):",
    "  t1        = " <> str[inv["t1"]],
    "  arc       = " <> str[inv["arc"]],
    "  residual  = " <> str[inv["residual"]],
    "  cusps     = " <> str[inv["cuspsCrossed"]],
    "  converged = " <> str[inv["converged"]]}];

  Scan[Print, report];
  assoc];

(* ------------------------------------------------------------------ *)
(* end                                                                *)
(* ------------------------------------------------------------------ *)
