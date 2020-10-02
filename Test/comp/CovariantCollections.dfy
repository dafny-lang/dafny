// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  // TODO: include tests of assignments from coll<Number> back to coll<Integer> when all elements are known to be Integer
  Sequences();
  Sets();
  Multisets();
  Maps();
}

trait Number {
  const value: int
  method Print()
}

class Integer extends Number {
  constructor(value: int) {
    this.value := value;
  }
  method Print() {
    print value;
  }
}

// -------------------- seq --------------------

method PrintSeq(prefix: string, s: seq<Number>) {
  print prefix, "[";
  var i, sep := 0, "";
  while i < |s| {
    print sep;
    s[i].Print();
    i, sep := i + 1, ", ";
  }
  print "]";
}

method Sequences() {
  var twelve := new Integer(12);
  var seventeen := new Integer(17);
  var fortyTwo := new Integer(42);
  var eightyTwo := new Integer(82);

  var a := [];
  var b: seq<Number> := [seventeen, eightyTwo, seventeen, eightyTwo];
  var c := [twelve, seventeen];

  PrintSeq("Sequences: ", a);
  PrintSeq(" ", b);
  PrintSeq(" ", c);
  print "\n";

  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  PrintSeq("  update: ", b[0 := fortyTwo]);
  PrintSeq(" ", c[0 := fortyTwo]);
  print "\n";

  print "  index: ";
  b[0].Print();
  print " ";
  c[0].Print();
  print "\n";

  PrintSeq("  subsequence ([lo..hi]): ", b[1..3]);
  PrintSeq(" ", c[1..2]);
  print "\n";

  PrintSeq("  subsequence ([lo..]): ", b[1..]);
  PrintSeq(" ", c[1..]);
  print "\n";

  PrintSeq("  subsequence ([..hi]): ", b[..3]);
  PrintSeq(" ", c[..2]);
  print "\n";

  PrintSeq("  subsequence ([..]): ", a[..]);
  PrintSeq(" ", b[..]);
  PrintSeq(" ", c[..]);
  print "\n";

  PrintSeq("  concatenation: ", a + b);
  PrintSeq(" ", b + c);
  print "\n";

  print "  prefix: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper prefix: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  membership: ", seventeen in a, " ", seventeen in b, " ", seventeen in c, "\n";
}

// -------------------- set --------------------

method PrintSet(prefix: string, S: set<Number>) {
  print prefix, "{";
  var s: set<Number>, sep := S, "";
  while |s| != 0 {
    print sep;
    // pick smallest Number in s
    ghost var m := ThereIsASmallest(s);
    var x :| x in s && forall y :: y in s ==> x.value <= y.value;
    x.Print();
    s, sep := s - {x}, ", ";
  }
  print "}";
}

lemma ThereIsASmallest(s: set<Number>) returns (m: Number)
  requires s != {}
  ensures m in s && forall y :: y in s ==> m.value <= y.value;
{
  m :| m in s;
  if y :| y in s && y.value < m.value {
    var s' := s - {m};
    assert y in s';
    m := ThereIsASmallest(s');
  }
}

method Sets() {
  var twelve := new Integer(12);
  var seventeen := new Integer(17);
  var fortyTwo := new Integer(42);
  var eightyTwo := new Integer(82);

  var a := {};
  var b: set<Number> := {seventeen, eightyTwo, seventeen, eightyTwo};
  var c := {twelve, seventeen};

  PrintSet("Sets: ", a);
  PrintSet(" ", b);
  PrintSet(" ", c);
  print "\n";

  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";

  var comprehension := set n | n in b && n.value % 2 == 0;
  PrintSet("  comprehension: ", comprehension);
  print "\n";

  PrintSet("  union: ", a + b);
  PrintSet(" ", b + c);
  print "\n";

  PrintSet("  intersection: ", a * b);
  PrintSet(" ", b * c);
  print "\n";

  PrintSet("  difference: ", a - b);
  PrintSet(" ", b - c);
  print "\n";

  print "  subset: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper subset: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  membership: ", seventeen in a, " ", seventeen in b, " ", seventeen in c, "\n";
}

// -------------------- multiset --------------------

method PrintMultiset(prefix: string, S: multiset<Number>) {
  print prefix, "{";
  var s: multiset<Number>, sep := S, "";
  while |s| != 0 {
    print sep;
    // pick smallest Number in s
    ghost var m := ThereIsASmallestInMultiset(s);
    var x :| x in s && forall y :: y in s ==> x.value <= y.value;
    x.Print();
    s, sep := s - multiset{x}, ", ";
  }
  print "}";
}

lemma ThereIsASmallestInMultiset(s: multiset<Number>) returns (m: Number)
  requires s != multiset{}
  ensures m in s && forall y :: y in s ==> m.value <= y.value;
{
  m :| m in s;
  if y :| y in s && y.value < m.value {
    var s' := s - multiset{m};
    assert y in s';
    m := ThereIsASmallestInMultiset(s');
  }
}

method Multisets() {
  var twelve := new Integer(12);
  var seventeen := new Integer(17);
  var fortyTwo := new Integer(42);
  var eightyTwo := new Integer(82);

  var a := multiset{};
  var b: multiset<Number> := multiset{seventeen, eightyTwo, seventeen, eightyTwo};
  var c := multiset{twelve, seventeen};

  PrintMultiset("Multisets: ", a);
  PrintMultiset(" ", b);
  PrintMultiset(" ", c);
  print "\n";

  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";

  PrintMultiset("  update: ", b[fortyTwo := 3][eightyTwo := 0]);
  PrintMultiset(" ", c[fortyTwo := 1]);
  print "\n";

  print "  multiplicity: ", b[eightyTwo], " ", c[eightyTwo], " ", c[fortyTwo := 20][fortyTwo], "\n";

  PrintMultiset("  union: ", a + b);
  PrintMultiset(" ", b + c);
  print "\n";

  PrintMultiset("  intersection: ", a * b);
  PrintMultiset(" ", b * c[eightyTwo := 100]);
  print "\n";

  PrintMultiset("  difference: ", a - b);
  PrintMultiset(" ", b - c);
  print "\n";

  print "  subset: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper subset: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  membership: ", seventeen in a, " ", seventeen in b, " ", seventeen in c, "\n";
}

// -------------------- map --------------------

method PrintMap(prefix: string, M: map<Number, Number>) {
  print prefix, "{";
  var m: map<Number, Number>, sep := M, "";
  var s := m.Keys;
  while |s| != 0
    invariant s <= m.Keys
  {
    print sep;
    // pick smallest Number in s
    ghost var min := ThereIsASmallest(s);
    var x :| x in s && forall y :: y in s ==> x.value <= y.value;
    x.Print();
    print " := ";
    m[x].Print();
    s, sep := s - {x}, ", ";
  }
  print "}";
}

method Maps() {
  var twelve := new Integer(12);
  var seventeen := new Integer(17);
  var fortyTwo := new Integer(42);
  var eightyTwo := new Integer(82);

  var a := map[];
  var b: map<Number, Number> := map[seventeen := eightyTwo, eightyTwo := seventeen, twelve := seventeen];
  var c := map[twelve := seventeen, seventeen := seventeen];

  PrintMap("Maps: ", a);
  PrintMap(" ", b);
  PrintMap(" ", c);
  print "\n";

  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";

  PrintMap("  update: ", b[fortyTwo := seventeen]);
  PrintMap(" ", c[twelve := fortyTwo]);
  print "\n";

  var comprehension: map<Integer, Integer> := map n,p | n in b.Keys && p in b.Keys && b[n] == p && b[p] == n :: n := twelve;  // map[17 := 12, 82 := 12]
  PrintMap("  comprehension: ", comprehension);
  print "\n";

  PrintSet("  Keys: ", b.Keys); print "\n";
  PrintSet("  Values: ", b.Values); print "\n";
  //SOON (requires covariant datatypes):  PrintPairs("  Items: ", b.Items); print "\n";
  print "  eq: ", a == b, " ", comprehension == comprehension, " ", c == map[seventeen := seventeen, twelve := seventeen], "\n"; // false true true

  // covariance issues with equality
  var m00: map<Number, Number> := map[seventeen := fortyTwo];
  var m01: map<Number, Integer> := map[seventeen := fortyTwo];
  var m10: map<Integer, Number> := map[seventeen := fortyTwo];
  var m11: map<Integer, Integer> := map[seventeen := fortyTwo];
  print "  eq: ", m00 == m01, " ", m00 == m10, " ", m00 == m11, " ", m01 == m10, " ", m01 == m11, " ", m10 == m11, "\n"; // true^6
  print "  eq: ", m01 == m00, " ", m10 == m00, " ", m11 == m00, " ", m10 == m01, " ", m11 == m01, " ", m11 == m10, "\n"; // true^6

  // covariance issues with equality
  var n00: map<Number?, Number> := map[seventeen := fortyTwo, null := eightyTwo];
  var n01: map<Number?, Integer> := map[seventeen := fortyTwo, null := eightyTwo];
  var n10: map<Integer?, Number> := map[seventeen := fortyTwo];
  var n11: map<Integer?, Integer> := map[seventeen := fortyTwo, null := eightyTwo];
  print "  eq: ", n00 == n01, " ", n00 == n10, " ", n00 == n11, " ", n01 == n10, " ", n01 == n11, " ", n10 == n11, "\n"; // t F t F t F
  print "  eq: ", n01 == n00, " ", n10 == n00, " ", n11 == n00, " ", n10 == n01, " ", n11 == n01, " ", n11 == n10, "\n"; // F t F t F t
  n10 := n10[null := eightyTwo];
  print "  eq: ", n00 == n01, " ", n00 == n10, " ", n00 == n11, " ", n01 == n10, " ", n01 == n11, " ", n10 == n11, "\n"; // true^6
  print "  eq: ", n01 == n00, " ", n10 == n00, " ", n11 == n00, " ", n10 == n01, " ", n11 == n01, " ", n11 == n10, "\n"; // true^6
}

/*SOON (requires covariant datatypes):
method PrintPairs(prefix: string, S: set<(Number, Number)>) {
  print prefix, "{";
  var s: set<Number>, sep := set pair | pair in S :: pair.0, "";
  while |s| != 0
    invariant forall x :: x in s ==> exists y :: (x,y) in S
  {
    print sep;
    // pick smallest Number in s
    ghost var m := ThereIsASmallest(s);
    var x :| x in s && forall y :: y in s ==> x.value <= y.value;
    var pair :| pair in S && pair.0 == x;
    print "(";
    pair.0.Print();
    print ", ";
    pair.1.Print();
    print ")";
    s, sep := s - {x}, ", ";
  }
  print "}";
}
*/
