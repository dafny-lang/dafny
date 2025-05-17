// RUN: %exits-with 2 %resolve --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Test {
  var x: Test?
  var y: Test?
  const z: Test? := null;
}

datatype X = X()

method Test() {
  assert referrers(X()) == {}; // Error, referrers should be applied to a single object or array, got X
  assert referrers(1) == {}; // Error, referrers should be applied to a single object or array, got int
}