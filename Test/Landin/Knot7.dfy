// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref {
  ghost var hogp: Ref ~> int
}

ghost function F(r: Ref): int
  reads r, r.hogp.reads(r)
{
  if r.hogp.requires(r) then 1 + r.hogp(r) else 0
}


method Main()
  ensures false
{
  var r := new Ref;
  r.hogp := F;
  // error: r.hogp calls itself without decreasing
  var f := r.hogp(r);
}