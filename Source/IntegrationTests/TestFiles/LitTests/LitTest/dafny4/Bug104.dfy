// RUN: %testDafnyForEachResolver "%s"


datatype PartRealPartGhost = PartRealPartGhost(x:int, ghost y:int)

method UpdateField()
{
 var v := PartRealPartGhost(3, 4);
 ghost var g := 5;
 v := v.(y := g);
}
