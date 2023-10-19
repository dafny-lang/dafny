// RUN: %baredafny run %args --input %s %S/random.dfy --input %S/randomCSharp.dfy > "%t"
// RUN: %diff "%s.expect" "%t"

import Random

method Main() {
  var x := Random.GetRandomNat(10);
  print x;
}