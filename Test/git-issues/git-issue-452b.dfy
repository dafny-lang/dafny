// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Record = Record(a: int, ghost b: int)

function method TwinPrimes(): Record {
  Record(41, 43)
}

method Main() {
  var w := var Record(x, y) := TwinPrimes(); x; // x and w are non-ghost
  var u := var Record(x, y) := TwinPrimes(); y; // y and u are ghost
  print w, " ", u, "\n"; // ERROR on u, not on w
}
