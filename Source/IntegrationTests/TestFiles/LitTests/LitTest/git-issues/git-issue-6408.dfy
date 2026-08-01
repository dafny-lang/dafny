// RUN: %testDafnyForEachResolver "%s"

// Set, multiset, and map displays that differ only in the order of their elements -- and set displays that
// differ by a repeated element -- denote equal values, and are now emitted so that this equality holds by
// construction. This lets such displays be used interchangeably as, e.g., map keys or set-of-set elements.

method Sets() {
  // Reordered set literals are equal, including when used as a map key.
  assert {1, 2, 3} == {3, 2, 1};
  var m: map<set<int>, int> := map[{1, 2, 3} := 7];
  assert {3, 2, 1} in m.Keys;
  assert m[{3, 2, 1}] == 7;

  // A repeated element does not change a set.
  assert {1, 1, 2} == {1, 2};
  assert |{1, 1, 2}| == 2;

  // Reordering works with variable elements too, and for nested sets.
  var ss: set<set<int>> := {{1, 2}, {3}};
  assert {2, 1} in ss;
}

method SetsVars(a: int, b: int) {
  var m: map<set<int>, int> := map[{a, b} := 7];
  assert {b, a} in m.Keys;
  assert m[{b, a}] == 7;
}

method Multisets() {
  // Reordered multiset literals are equal, but multiplicity is significant.
  assert multiset{1, 2, 3} == multiset{3, 2, 1};
  assert multiset{1, 1, 2} == multiset{2, 1, 1};
  assert multiset{1, 1, 2} != multiset{1, 2};
  assert |multiset{1, 1, 2}| == 3;
  var m: map<multiset<int>, int> := map[multiset{1, 2, 3} := 7];
  assert multiset{3, 2, 1} in m.Keys;
}

method Maps() {
  // Reordered map displays are equal, including when used as a set element.
  assert map[1 := 10, 2 := 20] == map[2 := 20, 1 := 10];
  var s: set<map<int, int>> := {map[1 := 10, 2 := 20]};
  assert map[2 := 20, 1 := 10] in s;

  // A repeated key takes its last-written value (last-write-wins).
  assert map[1 := 10, 1 := 20] == map[1 := 20];
  assert map[1 := 10, 1 := 20][1] == 20;
}

method Sequences() {
  // Sequences are ordered, so element order is significant (unchanged behavior).
  assert [1, 2, 3] != [3, 2, 1];
  assert [1, 2, 3] == [1, 2, 3];
}
