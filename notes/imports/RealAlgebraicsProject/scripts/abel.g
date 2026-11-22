out := OutputTextFile("abel.txt", false);
SetPrintFormattingStatus(out, false);
for name in ["PSL28","A9","S9"] do
  if name = "PSL28" then G := PSL(2,8); elif name = "A9" then G := AlternatingGroup(9); else G := SymmetricGroup(9); fi;
  Print(name, " ", NrMovedPoints(G), " ", Size(G), "\n");
  cls := Filtered(ConjugacyClassesSubgroups(G), c -> IsAbelian(Representative(c)) and Size(Representative(c)) > 1);
  for c in cls do
    H := Representative(c);
    gens := MinimalGeneratingSet(H);
    PrintTo(out, name, ";", Size(H), ";", StructureDescription(H), ";", List(gens, g -> ListPerm(g, 9)), "\n");
  od;
  Print(name, " abelian classes: ", Length(cls), "\n");
od;
CloseStream(out);
QUIT;
