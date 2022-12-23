// RUN: %testDafnyForEachCompiler "%s"

datatype Record = Record(a: int, ghost b: int)

function method TwinPrimes(): Record {
  Record(41, 43)
}

method Main() {
  var u := var Record(x, y) := TwinPrimes(); y; // x is non-ghost
  var w := var Record(x, y) := TwinPrimes(); x; // x and w are non-ghost
  //@ assert u == 43;
  print w, "\n";
}
