// RUN: %tobinary %s > %t.assertFalse.dbin
// RUN: %verify --input-format Binary --stdin < %t.assertFalse.dbin > %t
// RUN: %diff "%s.expect" "%t"

method Sets() {
  // Displays
  var s0: set<int> := {};
  var s1: set<int> := {1};
  var s2: set<int> := {2, 3};
  assert s0 + s1 + s2 == {1, 2, 3};
  var i0 := iset{};
  var i1 := iset{1};
  var i2 := iset{2, 3};
  assert i0 + i1 + i2 == iset{1, 2, 3};

  // Comprehensions
  var sc0 := set x: nat {:trigger x} | x < 4;
  assert sc0 == {0, 1, 2, 3};
  var sc1 := set x <- sc0 | x % 2 == 0, y <- sc0 | y % 2 == 1 :: x * y;
  expect sc1 == {0, 2, 6};
  assert sc1 == {0, 2, 6};
}