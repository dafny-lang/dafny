// RUN: %dafny /compile:0 "%s" > "%t"
method Foo() {
  var myMap := map[1 := [1], 2 := [4], 3 := [9]];
  var s: seq<nat> := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
  var s' := seq i <- s | i > 3, 
                j <- f(i) 
                :: j;
  var s'' := seq i <- s | i in myMap, 
                 j <- myMap[i] 
                 :: j;
  assert forall i <- s :: i > 0;
}

function f(x: nat): seq<nat>
  requires x > 3
{
  [x - 3, x - 2, x - 1, x]
}
