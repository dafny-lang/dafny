// RUN: %exits-with 2 %resolve --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class TheObject {
}

datatype X = X(t: TheObject) | None

method Test(t: TheObject) {
  assert referrers(1) == {}; // Error, referrers should be applied to a single object or array, got int
  assert referrers(X(t)) == {locals`t}; // Referrers should be applied to a single object or array ,got datatype
}