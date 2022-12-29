// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class X {
  function method F(): int { 2 }
  var J: int
}

class K { }

method P0(x: X, k: K) {
  var o; // type inferred to be object
  o := x;
  o := k;
  var u := o.F(); // F does not exist in object
}

method P1(x: X, k: K) {
  var o; // type inferred to be object
  o := x;
  o := k;
  var u := o.J; // J does not exist in object
}

method Q0(x: X, k: K) {
  var o; // type inferred to be object
  o := x;
  var u := o.F(); // F does not exist in object
  o := k;
}


