// RUN: ! %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D(z: int, 2: int)
method m1(s: seq<int>) {
  var a := 1 ! ! 1;
  var a := 1 ! 1;
}

method m2() {
  assert true <== true ==> true ==> true <== true;
  assert 1 !! 1 != 1;
}
