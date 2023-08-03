// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref1 {
  ghost var hogp: () ~> int
}

class Ref2 {
  ghost var r: Ref1
  constructor()
}

method Main()
  ensures false
{
  var r := new Ref2();
  r.r := new Ref1;
  // error: r.r.hogp calls itself without decreasing
  r.r.hogp := () reads r, r.r, r.r.hogp.reads() => if r.r.hogp.requires() then 1 + r.r.hogp() else 0;
}