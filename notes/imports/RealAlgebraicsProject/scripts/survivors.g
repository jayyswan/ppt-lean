# Session 5: pairs (G, c) not ruled out by facts 1-3 and fact 7 (a = 0).
# G = Gal(N/P), c = complex conjugation on N (c^2 = 1).  Constraints:
#  (S1) G has a perfect normal subgroup G0 of index <= 2 with G = G0<c>; index 2 forces c not in G0.
#  (S2) no proper subgroup of index <= 8 contains a conjugate of c.
InvReps := function(G)
  local L; L := Filtered(List(ConjugacyClasses(G), Representative), x -> Order(x) <= 2); return L;
end;
InSmallIndex := function(G, c, bound)
  local M, x;
  for M in MaximalSubgroupClassReps(G) do
    if Index(G, M) <= bound then
      if IsOne(c) then return true; fi;
      for x in InvReps(M) do
        if (not IsOne(x)) and IsConjugate(G, c, x) then return true; fi;
      od;
    fi;
  od;
  return false;
end;
# admissible classes c for a permutation group G; returns list of [c, iInN]
Admissible := function(G)
  local D, res, c;
  res := [];
  D := DerivedSubgroup(G);
  if Size(D) = Size(G) then
    for c in InvReps(G) do Add(res, [c, false]); od;
  elif Index(G, D) = 2 and IsPerfectGroup(D) then
    for c in InvReps(G) do if not c in D then Add(res, [c, true]); fi; od;
  fi;
  return res;
end;
Report := function(d)
  local k, G, pr, c, r, rs, nm, big;
  for k in [1..NrPrimitiveGroups(d)] do
    G := PrimitiveGroup(d, k);
    if IsSolvableGroup(G) then continue; fi;
    big := IsNaturalAlternatingGroup(G) or IsNaturalSymmetricGroup(G);
    rs := [];
    for pr in Admissible(G) do
      c := pr[1]; r := d - NrMovedPoints(c);
      if r = 0 then continue; fi;
      if big or not InSmallIndex(G, c, 8) then AddSet(rs, r); fi;
    od;
    if Length(rs) > 0 then
      Print(d, " | ", Name(G), " | order ", Size(G), " | i in N: ", Size(DerivedSubgroup(G)) < Size(G), " | r in ", rs, "\n");
    fi;
  od;
end;
for d in [9..24] do Report(d); Print("-- done ", d, "\n"); od;
QUIT;
