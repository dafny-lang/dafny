// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function missing_number(nums: seq<nat>): nat
  requires |set i | i in nums| == |nums|
  requires forall x :: x in nums ==> 0 <= x <= |nums|
{
  var p := x => 0 <= x <= |nums| && x !in nums;
  assert exists x :: p(x) && forall y :: p(y) ==> y == x by {
    var range := set i | 0 <= i <= |nums|;
    assume |range| == |nums| + 1;
    var missing := range - set i | i in nums;
    assert |missing| == 1;
    var x :| x in missing;
    assert p(x);
    var y: int;
    forall y | p(y) ensures y in missing {}
    assume forall x, y :: x in missing && y in missing ==> x == y;
    forall y | p(y) ensures y == x {}
  }
  var x :| p(x);
  x
}
