// The same crash ("a.equals is not a function") was reachable without any extern code: a
// multi-dimensional array and an iterator are both plain JavaScript objects with no equals
// method, so comparing them generically -- here, through a set -- used to crash
// (https://github.com/dafny-lang/dafny/issues/6491). They now compare by identity, which is
// the equality Dafny gives reference types.
// RUN: %run --target js "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Arrays() {
  var a := new int[2, 2];
  var b := new int[2, 2];
  var s: set<array2<int>> := {a};
  assert a in s && b !in s;
  print a in s, " ", b in s, "\n";  // true false
}

iterator Iter() yields (x: int) { }

method Iterators() {
  var i := new Iter();
  var j := new Iter();
  var s: set<Iter> := {i};
  assert i in s && j !in s;
  print i in s, " ", j in s, "\n";  // true false
}

method Main() {
  Arrays();
  Iterators();
}
