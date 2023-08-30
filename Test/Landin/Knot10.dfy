// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


datatype Pack<T> = Pack(ghost c: T)

method M()
  ensures false
{
  var r := new Pack<() ~> bool>[1];
  r[0] := Pack(() => false);
  var tf := Pack(() reads r, r[0].c.reads => 
                     if r[0].c.requires() then !r[0].c() else false
                   );
  // error: r[0] calls itself without decreasing
  r[0] := tf;
}