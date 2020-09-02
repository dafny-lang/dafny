// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function TwinPrimes(): (int, int) {
  (41, 43)
}

method Main() {
  var (x, y) := TwinPrimes();  // this should not be allowed, but the Resolver didn't do the check
  var p := TwinPrimes();  // uncommented, this gives an error, as expected
  print x, " ", y, "\n";
}

