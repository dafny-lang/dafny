// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

iterator Repeat(val: int, count: nat) yields (res: int)
  yield ensures res == val
{
  for i := 0 to count { yield val; }
}

class C {}

method Main() {
  var repeat := new Repeat(0, 10);
  var c := new C;
  while true
     invariant repeat.Valid() && fresh(repeat._new)
  {
    repeat._new := repeat._new + { c };
    var next := repeat.MoveNext();
    if (!next) { break; }
    print next;
  }
}