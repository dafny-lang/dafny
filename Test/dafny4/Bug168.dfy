// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List = Nil | Cons(int, List)

function Crash(xs: List): int
  requires xs.Cons?
{
  var Cons(h, Nil) := xs; h
}