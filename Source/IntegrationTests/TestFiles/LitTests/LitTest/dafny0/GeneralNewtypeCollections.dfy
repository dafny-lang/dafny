// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh --general-newtypes --general-traits=datatype --reads-clauses-on-methods

method Main() {
  TestSet();
  var dt := Dt;
  print |dt.FFF(15)|, "\n"; // 15
  Frames.CallEm();
}

newtype IntSet = s: set<int> | true

method TestSet() {
  var s: IntSet;
  s := {};
  print s, " "; // {}
  s := {6, 19};
  print |s|, " "; // 2
  s := set x: int | 6 <= x < 10 && 2 * x < 300;
  print |s|, " ", 7 in s, " "; // 4 true
  s := set x: int | 6 <= x < 10 :: 2 * x;
  print |s|, " ", 7 in s, "\n"; // 4 false

  var bb := [5 in s, 12 in s, 19 !in s];

  var t: IntSet := s;

  s := s + t;
  s := s - t;
  s := s * t;
  var disjoint := s !! t;

  print bb, " ", s, " ", disjoint, "\n"; // [false, true, true] {} true

  var u: set<int>;
  u := s as set<int>;
  s := u as IntSet;
  var b0 := s is set<int>;
  var b1 := u is IntSet;

  print |s|, " ", |u|, " ", b0, " ", b1, "\n"; // 0 0 true true

  b0 := s <= t;
  b1 := s < t;
  var b2 := s > s;
  var b3 := s >= s;
  print b0, " ", b1, " ", b2, " ", b3, "\n"; // true true false true

  b0 := s == t;
  b1 := s != t;
  print b0, " ", b1, "\n"; // false true
}

// auto-accumulator tail recursive function in trait (this has a special case in the compiler code)
trait Trait {
  function FFF(n: nat): IntSet {
    if n == 0 then {} else {n} + FFF(n - 1)
  }
}

datatype Dt extends Trait = Dt

module Frames {
  method CallEm() {
    var o := new object;
    label Recently:
    M({o}, iset{o}, multiset{o, o}, [o, o, o]);
    var u := F({o}, iset{o}, multiset{o, o}, [o, o, o]);
    ghost var b := P2@Recently({o}, iset{o}, multiset{o, o}, [o, o, o]);
  }
  
  newtype ObjectSet = s: set<object> | true
  newtype ObjectISet = ss: iset<object> | true
  /*new*/type ObjectMultiset = m: multiset<object> | true
  /*new*/type ObjectSeq = q: seq<object> | true

  function R(x: int): ObjectSet {
    {}
  }

  method M(s: ObjectSet, ss: ObjectISet, m: ObjectMultiset, q: ObjectSeq)
    modifies s
    modifies ss
    modifies m
    modifies q
    reads s
    reads ss
    reads m
    reads q
  {
    assert unchanged(s);
    assert unchanged(ss);
    assert unchanged(m);
    assert unchanged(q);
    modify s;
    modify ss;
    modify m;
    modify q;
    for i := 0 to 100
      modifies s
      modifies ss
      modifies m
      modifies q
    {
    }
    ghost var g: bool;
    g := fresh(s);
    g := fresh(ss);
    g := fresh(q);
  }

  function F(s: ObjectSet, ss: ObjectISet, m: ObjectMultiset, q: ObjectSeq): int
    reads s
    reads ss
    reads m
    reads q
    reads R
  {
    6
  }

  twostate predicate P2(s: ObjectSet, ss: ObjectISet, m: ObjectMultiset, q: ObjectSeq)
    reads s
    reads ss
    reads m
    reads q
    reads R
  {
    true
  }
}
