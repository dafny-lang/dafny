// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref<T> {
  ghost var hogp: T
  constructor()
}

method Main()
  ensures false
{
  var r := new Ref<() ~> int>();
  // error: r.hogp calls itself without decreasing
  r.hogp := () reads r, r.hogp.reads() => if r.hogp.requires() then 1 + r.hogp() else 0;
}