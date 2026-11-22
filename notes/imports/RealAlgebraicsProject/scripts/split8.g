# Which (G, c) with G <= S_8 are not forced to be trivial?  (Splitting of polynomials of degree <= 8 over P(i).)
# N splits over P(i) iff G0 = 1.  Survivors: G0 nontrivial perfect of index <= 2, c in G \ G0 if index 2,
# and no proper subgroup of index <= 8 contains a conjugate of c.
InvReps := G -> Filtered(List(ConjugacyClasses(G), Representative), x -> Order(x) <= 2);
InSmallIndex := function(G, c, bound)
  local M, x;
  for M in MaximalSubgroupClassReps(G) do
    if Index(G, M) <= bound then
      if IsOne(c) then return true; fi;
      for x in InvReps(M) do if (not IsOne(x)) and IsConjugate(G, c, x) then return true; fi; od;
    fi;
  od;
  return false;
end;
S := SymmetricGroup(8);
cnt := 0;
for cl in ConjugacyClassesSubgroups(S) do
  G := Representative(cl); D := DerivedSubgroup(G);
  if IsSolvableGroup(G) then continue; fi;
  cands := [];
  if Size(D) = Size(G) then cands := InvReps(G);
  elif Index(G, D) = 2 and IsPerfectGroup(D) then cands := Filtered(InvReps(G), x -> not x in D); fi;
  cnt := cnt + 1;
  for c in cands do
    if not InSmallIndex(G, c, 8) then
      Print("survivor: ", StructureDescription(G), " order ", Size(G), " orbits ", List(Orbits(G,[1..8]),Length), " | cycle type of c: ", CycleStructurePerm(c), " | fixed points ", 8-NrMovedPoints(c), "\n");
    fi;
  od;
od;
Print("non-solvable subgroup classes of S_8 examined: ", cnt, "\n");
QUIT;
