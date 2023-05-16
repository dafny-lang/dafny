// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Foo {
  ghost var Repr: set<object>
}

ghost function SeqRepr(s:seq<Foo>) : set<object>
  reads set b | b in s
{
  set o,b | b in s && o in b.Repr :: o     // Works if you say "set b,o | ..."
}
