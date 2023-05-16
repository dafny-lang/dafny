// RUN: %testDafnyForEachCompiler "%s"

ghost function TwinPrimes(): (int, int) {
  (41, 43)
}

function TwinPrimesM(): (int, int) {
  (41, 43)
}

method Main() {
  var (x, y) := TwinPrimesM();  // x and y are not ghost
  var p := TwinPrimesM();  // p is not ghost
  print x, " ", y, " ", p, "\n"; // OK
}

