method Test() {
  ghost var x: int;
  x := 5;
  assert x == x; // This should work
}

method Test2() {
  ghost var s: set<int>;
  s := {};
  assert s == s; // This should work
}
