// RUN: %testDafnyForEachResolver "%s"

// Set and multiset displays that differ only in the order of their elements denote equal values. Their emitted
// Set#UnionOne / MultiSet#UnionOne chains are now built in a canonical element order, so such displays produce
// the identical term and can be used interchangeably as, e.g., map keys or set-of-set elements -- even when the
// equality would otherwise only be provable, not syntactic (as in a buried subgoal like `k in m.Keys`).

method Sets() {
  // Reordered set literals used as a map key: the lookup key must match the stored key by construction.
  var m: map<set<int>, int> := map[{1, 2, 3} := 7];
  assert {3, 2, 1} in m.Keys;
  assert m[{3, 2, 1}] == 7;

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
  // Reordered multiset literals as a map key. Multiplicity is significant, so only the order is canonicalized.
  var m: map<multiset<int>, int> := map[multiset{1, 2, 3} := 7];
  assert multiset{3, 2, 1} in m.Keys;
  assert multiset{1, 1, 2} != multiset{1, 2};
}

datatype Color = Red | Green | Blue

method DatatypeAndOtherElements() {
  // Canonicalization is only ever a reordering, so distinct elements are never conflated, whatever their shape.
  assert |{Red, Green, Blue}| == 3;
  assert Red in {Red, Green};
  assert |{"ab", "cd"}| == 2;
  assert |{'a', 'b'}| == 2;
  assert |{{1, 2}, {3, 4}}| == 2;
  assert |multiset{Red, Green}| == 2;
  var mc: map<Color, int> := map[Red := 1, Green := 2];
  assert Red in mc.Keys && Green in mc.Keys;
}

function Id<T>(x: T): T { x }
datatype Box<T> = Box(v: T)

method FunctionApplicationElements() {
  // Distinct applications of the same function or constructor print differently and so are not conflated.
  var s: set<Box<int>> := {Box(1), Box(2)};
  assert Box(1) in s && Box(2) in s;
  var t := {Id(1), Id(2)};
  assert Id(1) in t && Id(2) in t;
}

method Sequences() {
  // Sequences are ordered, so element order stays significant (unchanged behavior).
  assert [1, 2, 3] != [3, 2, 1];
  assert [1, 2, 3] == [1, 2, 3];
}
