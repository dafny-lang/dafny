// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype PartRealPartGhost = PartRealPartGhost(x:int, ghost y:int)

method UpdateField()
{
 var v := PartRealPartGhost(3, 4);
 ghost var g := 5;
 v := v.(y := g);
}
