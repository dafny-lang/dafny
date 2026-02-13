// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh=false --general-newtypes=false --relax-definite-assignment --spill-translation

method Main() {
  Sequences();
  Sets();
  Multisets();
  Maps();
  Downcasts();
  DeepDowncast();
  CovarianceRegressions.Test();
}

trait Number extends object {
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
  ensures m in s && forall y :: y in s ==> m.value <= y.value
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
  ensures m in s && forall y :: y in s ==> m.value <= y.value
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
    var x: Number :| x in s && forall y: Number :: y in s ==> x.value <= y.value;
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

// -------------------- downcasts --------------------

method Downcasts() {
  var a := new Integer(20);
  var b := new Integer(30);

  var m: set<Number>, n: multiset<Number>, o: seq<Number>, p: map<Number, Number>;
  var s: set<Integer>, t: multiset<Integer>, u: seq<Integer>, v: map<Integer, Integer>;
  m, n, o, p := Create<Number>(a, b);
  s, t, u, v := m, n, o, p;  // in C#, this requires a downcast clone
  m, n, o, p := s, t, u, v;
  s, t, u, v := m, n, o, p;  // here, the downcast clone is the identity
  m, n, o, p := s, t, u, v;

  PrintSet("set: ", m); print "\n";
  PrintMultiset("multiset: ", n); print "\n";
  PrintSeq("seq: ", o); print "\n";
  PrintMap("map: ", p); print "\n";

  s := DowncastF(m);  // cast in, cast out
  s := DowncastM(m);  // cast in, cast out
  var s': set<Integer>;
  s, s' := DowncastM2(m);  // cast in, cast out
  s := var v: set<Integer> := m; v;  // regression test -- this once tripped up the compilation to Java, whereas the next line had not
  s' := var u: set<Number> := var v: set<Integer> := m; v; u;
  var s'' := DowncastFunction(a, b); // regression test -- the same error was later discovered in top-level function bodies
  var eq := s == m && m == s && s == s'';
  print eq, "\n";  // true

  s := FId<Integer>(m);  // cast in
  s := FId<Number>(s);  // cast out
  s := MId<Integer>(m);  // cast in
  s := MId<Number>(s);  // cast out
  s, s' := MId2<Integer>(m);  // cast in
  s, s' := MId2<Number>(m);  // cast out
  eq := s == m && m == s;
  print eq, "\n";  // true

  TailRecursiveMethod(12, 1, s);
  var f16 := TailRecursiveFunction(12, 1, s);
}

// This method will create the collections of type coll<T>
method Create<T>(a: T, b: T) returns (m: set<T>, n: multiset<T>, o: seq<T>, p: map<T, T>)
  ensures m == {a, b} && n == multiset{a, b} && o == [a, b]
  ensures p == map[a := b, b := a]
{
  m, n, o := {a, b}, multiset{a, b}, [a, b];
  p := map[a := b, b := a];
}

function DowncastFunction(a: Integer, b: Integer): set<Integer> {
  var m: set<Number> := {a, b};
  var v: set<Integer> := m;
  v
}

function DowncastF(s: set<Integer>): set<Number> { s }
method DowncastM(s: set<Integer>) returns (r: set<Number>)
  ensures r == s
{
  r := s;
}
method DowncastM2(s: set<Integer>) returns (r0: set<Number>, r1: set<Number>)
  ensures r0 == r1 == s
{
  r0, r1 := s, s;
}

function FId<T>(s: set<T>): set<T> { s }
method MId<T>(s: set<T>) returns (r: set<T>)
  ensures r == s
{
  r := s;
}
method MId2<T>(s: set<T>) returns (r0: set<T>, r1: set<T>)
  ensures r0 == r1 == s
{
  r0, r1 := s, s;
}

method {:tailrecursion} TailRecursiveMethod(x: nat, ghost u: int, s: set<Integer>) {
  var n: set<Number> := s;
  if x != 0 {
    TailRecursiveMethod(x - 1, 100 * u, n);
  }
}

function {:tailrecursion} TailRecursiveFunction(x: nat, ghost u: int, s: set<Integer>): int {
  var n: set<Number> := s;
  if x == 0 then 16 else TailRecursiveFunction(x - 1, 100 * u, n)
}

class Class {
  constructor (s: set<Integer>) {
    ns, js := s, s;
  }
  var ns: set<Number>
  var js: set<Integer>
}

method HeapAssignmentDowncasts() {
  var n: Number := new Integer(22);
  var ns: set<Number> := {n};
  var c := new Class(ns);
  c.ns := c.js;
  c.js := c.ns;
  PrintSet("c.js: ", c.js); print " ";

  var a := new set<Integer>[20];
  var m := new set<Integer>[18, 18];
  a[7] := ns;
  // m[7, 9] := ns;  // TODO: type checking gives an error, which is questionable (see https://github.com/dafny-lang/dafny/issues/885)
  ns := a[1];
  ns := m[3, 3];
  PrintSet(" a[7]: ", a[7]); print "\n";
}

method DeepDowncast() {
  // test covariant types whose components are also of a covariant type
  // (this requires some machinery to accomplish in C#)

  var t: Number := new Integer(4);
  var ttt: set<seq<Number>> := SetOfSeqOf<Number>(t);
  var ccc: set<seq<Integer>> := ttt;
  print |ttt|, " ", |ccc|, "\n";

  var o := new object;
  var mtt: map<seq<Number>, object> := MapOfSeqOf<Number, object>(t, o);
  var mcc: map<seq<Integer>, object> := mtt;
  print |mtt|, " ", |mcc|, "\n";
}

function SetOfSeqOf<T(==)>(t: T): set<seq<T>> {
  {[t]}
}

function MapOfSeqOf<T(==), U>(t: T, u: U): map<seq<T>, U> {
  map[[t] := u]
}

// -------------------- some regression tets --------------------

module CovarianceRegressions {
  trait Trait extends object { }

  method Test() {
    var a: set<Trait>;
    var b: seq<Trait>;
    var c: multiset<Trait>;
    var d: map<Trait, Trait>;
    Ins(a, b, c, d);
    a, b, c, d := Outs();

    Anything(a);
    Anything(b);
    Anything(c);
    Anything(d);
  }

  method Anything<X>(x: X) { }

  method Ins(a: set<Trait>, b: seq<Trait>, c: multiset<Trait>, d: map<Trait, Trait>) {
  }

  method Outs() returns (a: set<Trait>, b: seq<Trait>, c: multiset<Trait>, d: map<Trait, Trait>) {
  }

  class Class extends Trait { }

  method TestDisjointTypeArgument_Set(a: set<Trait>, b: set<Class>) {
    var x := a !! b;
    var y := b !! a;
  }

  method TestDisjointTypeArgument_MultiSet(a: multiset<Trait>, b: multiset<Class>) {
    var x := a !! b;
    var y := b !! a;
  }
}
