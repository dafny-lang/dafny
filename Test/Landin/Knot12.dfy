// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Pack<T> = Pack(ghost c: T)

method M()
  ensures false
{
  var r := new array<Pack<() ~> bool>>[1];
  r[0] := new Pack<() ~> bool>[1];
  r[0][0] := Pack(() => false);
  var tf := Pack(() reads r, r[0], r[0][0].c.reads => 
                     if r[0][0].c.requires() then !r[0][0].c() else false
                   );
  // error: r[0][0].c calls itself without decreasing
  r[0][0] := tf;
}