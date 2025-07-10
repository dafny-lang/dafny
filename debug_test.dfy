method Test() {
  ghost var x: int := *;
  assert x == x; // This should work
}

method Test2() {
  ghost var s: set<int> := *;
  assert s == s; // This should work
}
