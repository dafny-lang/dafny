// RUN: %tobinary %s > %t.assertFalse.dbin
// RUN: %verify --input-format Binary --stdin < %t.assertFalse.dbin > %t
// RUN: %diff "%s.expect" "%t"

method Seqs() {
  // Displays
  var s0: seq<int> := [];
  var s1: seq<int> := [1];
  var s2: seq<int> := [2, 3];
  assert s0 + s1 + s2 == [1, 2, 3];
 
  // Constructions
  var sc0 := seq(5, i => i + 1);
  assert sc0 == [1, 2, 3, 4, 5];
  var sc1 := seq<nat>(4, i => i * i);
  assert sc1 == [0, 1, 4, 9];
 
  // Updates
  var su0 := sc0[1 := -1];
  assert su0 == [1, -1, 3, 4, 5];
  var su1 := su0[3 := -3][4 := -4];
  assert su1 == [1, -1, 3, -3, -4];
}

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
  var m0: multiset<int> := multiset{};
  var m1: multiset<int> := multiset{1};
  var m2: multiset<int> := multiset{2, 2, 3, 3, 3};
  assert m0 + m1 + m2 == multiset{1, 2, 2, 3, 3, 3};
  assert m2[3 := 1] == multiset{2, 2, 3};

  // Comprehensions
  var sc0 := set x: nat {:trigger x} | x < 4;
  assert sc0 == {0, 1, 2, 3};
  var sc1 := set x <- sc0 | x % 2 == 0, y <- sc0 | y % 2 == 1 :: x * y;
  expect sc1 == {0, 2, 6};
  assert sc1 == {0, 2, 6};
}

method Maps() {
  // Displays
  var m0: map<int, bool> := map[];
  var m1 := map[1 := true, 2 := false];
  assert m1[1] != m1[2];
  var i0: imap<int, bool> := imap[];
  var i1 := imap[3 := true, 4 := false];
  assert i1[3] != i1[4];

  // Comprehensions
  var c0 := map x | 0 <= x < 10 :: x * x;
  assert c0[4] == 16;
  var c1 := imap x: nat | 0 <= x < 10 :: x + 1 := x * 2;
  expect 4 in c1 && c1[4] == 6;
  assert c1[4] == 6;
}