// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List = Nil | Cons(head: int, tail: List)

ghost function Crash(xs: List): int
  requires xs.Cons?
  ensures Crash(xs) == xs.head
{
  var Cons(h, Nil) := xs; h // ERROR: xs may not match Cons(_, Nil)
}

ghost function Crash2(xs: List): int
  requires xs.Cons?
  ensures Crash2(xs) == xs.head
{
  var Cons(h, _) := xs; h
}

ghost function Crash3(xs: List): int
  requires xs.Cons? && xs.tail.Nil?
  ensures Crash3(xs) == xs.head
{
  var Cons(h, Nil) := xs; h
}
