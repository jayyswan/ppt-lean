# Session 6: abelian p-subgroups of PSL(2,8), A9, S9 up to conjugacy (input for fixpts.py)
# Abelian prime-power subgroups (up to conjugacy) of PSL(2,8), A9, S9 on 9 points.
# For each: independent generators with orders, and every element with its exponent vector.
psl := Image(ActionHomomorphism(SL(2,8), NormedRowVectors(GF(8)^2), OnLines));;
Print("check: ", StructureDescription(psl), " ", Size(psl), "\n");
groups := [ ["PSL28", psl], ["A9", AlternatingGroup(9)], ["S9", SymmetricGroup(9)] ];;
out := OutputTextFile("absub.txt", false);; SetPrintFormattingStatus(out, false);
for pr in groups do
  G := pr[2];
  for p in Set(Factors(Size(G))) do
    S := SylowSubgroup(G, p);
    subs := Filtered(List(ConjugacyClassesSubgroups(S), Representative), H -> IsAbelian(H) and Size(H) > 1);
    reps := [];
    for H in subs do
      if ForAll(reps, K -> Size(K) <> Size(H) or not IsConjugate(G, K, H)) then Add(reps, H); fi;
    od;
    for H in reps do
      gens := IndependentGeneratorsOfAbelianGroup(H);
      ords := List(gens, Order);
      els := [];
      for e in Cartesian(List(ords, o -> [0..o-1])) do
        h := Product(List([1..Length(gens)], i -> gens[i]^e[i]));
        Add(els, [ListPerm(h, 9), e]);
      od;
      AppendTo(out, pr[1], "|", p, "|", ords, "|", els, "\n");
    od;
  od;
od;
CloseStream(out);
QUIT;
