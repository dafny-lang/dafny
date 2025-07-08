// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


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
method mg() {
  ghost var (x, y) := TwinPrimesM();
  ghost var p := TwinPrimesM();
  print x, " ", y, " ", p, "\n"; // ERROR
}
method m() {
  var (x, y) := TwinPrimes();  // OK: x and y are ghost
  var p := TwinPrimes();  // OK: p is ghost
  print x, " ", y, " ", p, "\n"; // ERROR: x, y, p are ghost
}

