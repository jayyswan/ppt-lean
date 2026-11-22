# Abelian 2-subgroups of S9 and A9 up to conjugacy (session 8). Run: gap -q ab2.g > ab2.out
for G in [SymmetricGroup(9), AlternatingGroup(9)] do
  P:=SylowSubgroup(G,2);
  cl:=List(ConjugacyClassesSubgroups(P),Representative);
  cl:=Filtered(cl,IsAbelian);
  reps:=[];
  for H in cl do
    if ForAll(reps,K->not IsConjugate(G,H,K)) then Add(reps,H); fi;
  od;
  Print("GROUP ",Size(G)," ",Length(reps),"\n");
  for H in reps do Print("SUB ",List(GeneratorsOfGroup(H),g->ListPerm(g,9)),"\n"); od;
od;
QUIT;
