// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type pos = x | 1 <= x witness 3

method ImplicitConversions(f: bool ~> nat) {
  var g: bool ~> int := f;
  var h: bool ~> pos := f; // error (case in point: f(true) may be 0)
}

method CompareRegression(f: bool ~> nat) {
  var g := f as bool ~> int;
  var h := f as bool ~> pos; // error (case in point: f(true) may be 0)
}
