// RUN: %dafny /compile:0 /unicodeChar:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Sets();
  SubSets();
  MultiSets();
  Sequences();
  Strings();
  Maps();
  MultiSetForming();
  TestExplosiveUnion();
  Regressions.Test();
}

// -------------------------------------------------------------------------------------------

trait Trait { }
class Class extends Trait { }

type IntSet = set<int>

method Sets() {
  var a := {};
  var b : IntSet := {17, 82, 17, 82};
  var c := {12, 17};
  print "Sets: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  union: ", a + b, " ", b + c, "\n";
  print "  intersection: ", a * b, " ", b * c, "\n";
  print "  difference: ", a - b, " ", b - c, "\n";
  print "  disjoint: ", a !! b, " ", b !! c, "\n";
  print "  subset: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper subset: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  superset: ", a >= b, " ", b >= a, " ", c >= c, "\n";
  print "  proper superset: ", a > b, " ", b > a, " ", c > c, "\n";
  print "  membership: ", 17 in a, " ", 17 in b, " ", 17 in c, "\n";

  var cl := new Class;
  var tr: Trait := cl;
  var xtrait: set<Trait> := {cl, tr};
  var xclass: set<Class> := {cl, cl};
  print "  eq covariance: ", |xtrait|, " ", xtrait == xclass, " ", xclass == xtrait, "\n";  // 1 true true
}

// -------------------------------------------------------------------------------------------

abstract module Order {
  type T(==)
  method lt(a: T, b: T) returns (r: bool)
}

module CharOrder refines Order {
  type T = char
  method lt(a: T, b: T) returns (r: bool) {
    r := a < b;
  }
}

module CharSetSetOrder refines Order {
  type T = set<char>

  function Pow2(i: nat) : nat {
    if i == 0 then 1 else 2 * Pow2(i-1)
  }

  method SetAsInt(s: set<char>) returns (r: int) {
    var ss := s;
    var acc := 0;
    while ss != {} {
      var i: char :| i in ss;
      ss := ss - {i};
      acc := acc + Pow2(i as nat);
    }
    r := acc;
  }

  method lt(a: T, b: T) returns (r: bool) {
    var aInt := SetAsInt(a);
    var bInt := SetAsInt(b);
    r := |a| < |b| || (|a| == |b| && aInt <= bInt);
  }
}

abstract module PrintOrderedSet {
  import O : Order

  method PrintElem(e: O.T)

  method Minimum(s: set<O.T>) returns (r: O.T)
    requires |s| > 0
    ensures r in s
  {
    var ss := s;
    r :| r in ss;
    ss := ss - {r};
    while ss != {}
      invariant ss <= s
      invariant r in s
    {
      var i: O.T :| i in ss;
      ss := ss - {i};
      var lt := O.lt(i, r);
      if lt {
        r := i;
      }
    }
  }

  method Print(s: set<O.T>) {
    var ss := s;
    print "{";
    var sep := "";
    while ss != {} {
      var bottom: O.T := Minimum(ss);
      ss := ss - {bottom};
      print sep;
      PrintElem(bottom);
      sep := ", ";
    }
    print "}";
  }
}

module CharSetPrinter refines PrintOrderedSet {
  import O = CharOrder

  method PrintElem(e: O.T) {
    print e;
  }
}

module CharSetSetPrinter refines PrintOrderedSet {
  import O = CharSetSetOrder
  import P = CharSetPrinter

  method PrintElem(e: O.T) {
    P.Print(e);
  }
}

method SubSets() {
  var s: set<char> := {'a', 'b', 'c', 'd'};
  var b0 := forall r | r <= s :: |r| == 2;
  var b1 := exists r | r <= s :: |r| == 2;
  print b0, " ", b1, "\n";
  var S := set r | r <= s && P(r);
  print "|s|=", |s|, " |S|=", |S|, "\n";
  CharSetSetPrinter.Print(S);
  print "\n";
}

predicate P(r: set<char>) { true }

// -------------------------------------------------------------------------------------------

type IntMultiSet = multiset<int>

method MultiSets() {
  var a := multiset{};
  var b : IntMultiSet := multiset{17, 82, 17, 82};
  var c := multiset{12, 17};
  var d := multiset{12, 12, 17};
  print "Multisets: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  union: ", a + b, " ", b + c, "\n";
  print "  intersection: ", a * b, " ", b * c, "\n";
  print "  difference: ", a - b, " ", b - c, "\n";
  print "  disjoint: ", a !! b, " ", b !! c, "\n";
  print "  subset: ", a <= b, " ", b <= c, " ", c <= c, " ", c <= d, "\n";
  print "  proper subset: ", a < b, " ", b < c, " ", c < c, " ", c < d, "\n";
  print "  superset: ", a >= b, " ", b >= a, " ", c >= c, "\n";
  print "  proper superset: ", a > b, " ", b > a, " ", c > c, "\n";
  print "  membership: ", 17 in a, " ", 17 in b, " ", 17 in c, "\n";
  print "  update: ", a[17 := 2], " ", b[17 := 2], " ", c[17 := 2], "\n";
  print "  multiplicity: ", a[17], " ", b[17], " ", c[17], "\n";

  zeroMultiplicity();
}

method zeroMultiplicity() {
  var a := multiset{12}[12 := 0];
  var b := multiset{42};
  var c := multiset{1, 2}[1 := 0][2 := 0];
  var d := multiset{12};
  var e := multiset{null}[null := 0];
  var f := multiset{null};
  print "Test zero multiplicity:\n";
  print "  printing: ", multiset{a, multiset{42}}, " ", a + d, "\n";
  print "  union: ", |a + d|, " ", |d + a|, " ", |e + f|, " ", |f + e|, "\n";
  print "  membership: ", 12 in a, " ", null in e, "\n";
  print "  equality: ", a == b, " ", a == c, " ", e == f, "\n";
  print "  subset: ", a <= b, " ", a <= c, " ", c <= a, " ", e <= f, " ", f <= e, "\n";
  print "  strict subset: ", a < b, " ", a < c, " ", c < a, " ", e < f, " ", f < e, "\n";
  print "  disjoint: ", a !! d, " ", d !! a, " ", e !! f, " ", f !! e, "\n";
}

// -------------------------------------------------------------------------------------------

type IntSeq = seq<int>

method Sequences() {
  var a := [];
  var b : IntSeq := [17, 82, 17, 82];
  var c := [12, 17];
  print "Sequences: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  update: ", b[0 := 42], " ", c[0 := 42], "\n";
  print "  index: ", b[0], " ", c[0], "\n";
  print "  subsequence ([lo..hi]): ", b[1..3], " ", c[1..2], "\n";
  print "  subsequence ([lo..]): ", b[1..], " ", c[1..], "\n";
  print "  subsequence ([..hi]): ", b[..3], c[..1], "\n";
  print "  subsequence ([..]): ", a[..], " ", b[..], " ", c[..], "\n";
  print "  concatenation: ", a + b, " ", b + c, "\n";
  print "  prefix: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper prefix: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  membership: ", 17 in a, " ", 17 in b, " ", 17 in c, "\n";
  BoundedIntegerParameters.Test();
  SeqUpdate();
  SeqPrefix();

  var cl := new Class;
  var tr: Trait := cl;
  var xtrait: seq<Trait> := [cl, tr];
  var xclass: seq<Class> := [cl, cl];
  print "  eq covariance: ", xtrait == xclass, " ", xclass == xtrait, "\n";  // true true
}

method SeqUpdate() {
  // regression tests
  var s := "hello";
  print s, "\n"; // hello
  var ch: char := 69 as char;
  s := s[1 := ch];
  print s, "\n"; // hEllo

  var t := [2, 4, 6, 8, 10];
  print t, "\n"; // [2, 4, 6, 8, 10];
  t := t[1 := 0];
  print t, "\n"; // [2, 0, 6, 8, 10];
}

datatype Cell = Cell(data: int)

method SeqPrefix() {
  // regression tests
  var a, b, c := Cell(8), Cell(10), Cell(8);
  var sa := [a, a, a, b, a, b, b];
  var sc := [c, c, c, b, c, b, b];
  var t := [a, a, a, b, a, b, b, b];
  print sa == sc, " ", sa != sc, " ", sa == t, "\n"; // true false false
  print sa <= sc, " ", sc <= sa, " ", t <= sa, " ", sa <= t, "\n"; // true true false true
  print sa < sc, " ", sc < sa, " ", t < sa, " ", sa < t, "\n"; // false false false true
}

module BoundedIntegerParameters {
  newtype short = x | 0 <= x < 0x100
  newtype tall = x | 0 <= x < 0x1_0000
  newtype grande = x | 0 <= x < 0x1_0000_0000
  newtype venti = x | 0 <= x < 0x1_0000_0000_0000_0000
  newtype little = x | -12 <= x < 12
  newtype big = x | -12 <= x < 0x1_0000_0000_0000

  method Test() {
    Seq(5, 5, 5, 5, 5, 5);
  }

  method Seq(u0: short, u1: tall, u2: grande, u3: venti, s0: little, s1: big)
    requires u0 as int <= u1 as int <= u2 as int <= u3 as int < 7
    requires 0 <= s0 as int <= s1 as int < 7
  {
    var data := "Bounded";

    print data[..u0], " ";
    print data[..u1], " ";
    print data[..u2], " ";
    print data[..u3], " ";
    print data[..s0], " ";
    print data[..s1], "\n";

    print data[u0..], " ";
    print data[u1..], " ";
    print data[u2..], " ";
    print data[u3..], " ";
    print data[s0..], " ";
    print data[s1..], "\n";

    print data[u0], " ";
    print data[u1], " ";
    print data[u2], " ";
    print data[u3], " ";
    print data[s0], " ";
    print data[s1], "\n";
  }
}

// -------------------------------------------------------------------------------------------

method Strings() {
  var a := "";
  var b := "uRuR";
  var c := "gu";
  print "Strings: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  concatenation: ", a + b, " ", b + c, "\n";
  print "  prefix: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper prefix: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  membership: ", 'u' in a, " ", 'u' in b, " ", 'u' in c, "\n";

  var d := ['g', 'u', 'r', 'u'];
  print "  constructed as sequence: ", d, "\n";

  var x, y := InterplayBetweenSeqCharAndString('d');
  // TODO: JavaScript and Go currently differ from C# if the following line is
  // uncommented, as they don't carry enough type information around at run time
  // to notice that x and y are character sequences (i.e. strings).
  // print "  separate: ", x, " ", y, "\n";
  x := "hello-" + x;
  y := y + "-hello";
  print "  mix: ", x, " ", y, "\n";
}

method InterplayBetweenSeqCharAndString<G>(g: G) returns (a: seq<G>, b: seq<G>) {
  a := [g];
  b := a + a;
  b := b + [g];
}

// -------------------------------------------------------------------------------------------

type IntMap = map<int, int>

datatype Color = Blue | Yellow | Red

method Maps() {
  var a := map[];
  var b: IntMap := map[17 := 2, 82 := 2];
  var c := map[17 := 0, 12 := 26];
  print "Maps: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  keys: ", a.Keys, " ", b.Keys, " ", c.Keys, "\n";
  print "  values: ", a.Values, " ", b.Values, " ", c.Values, "\n";
  print "  items: ", a.Items, " ", b.Items, " ", c.Items, "\n";
  var a', b', c' := a[17 := 6], b[17 := 6], c[17 := 6];
  print "  update: ";
  print a'[17], " (", |a'|, " ", |a|, ") ";
  print b'[17], " (", |b'|, " ", |b|, " ", b[17], ") ";
  print c'[17], " (", |c'|, " ", |c|, " ", c[17], ")\n";
  print "  lookup: ", 17 in a, " ", b[17], " ", c[17], "\n";

  // regression tests: make sure the types of .Keys, .Values, and .Items are correct
  var m := map[Blue := 30, Yellow := 21];
  print "m: ", m, "\n";
  var keys := m.Keys;
  print "keys: ", keys, "\n";
  var values := m.Values;
  print "values: ", values, "\n";
  var items := m.Items;
  print "items: ", items, "\n";

  TestMapMergeSubtraction();
}

method TestMapMergeSubtraction() {
  TestMapMerge();
  TestMapSubtraction();
  TestNullsAmongKeys();
  TestNullsAmongValues();
}

method TestMapMerge() {
  var a := map["ronald" := 66, "jack" := 70, "bk" := 8];
  var b := map["wendy" := 52, "bk" := 67];
  var ages := a + b;
  assert ages["jack"] == 70;
  assert ages["bk"] == 67;
  assert "sanders" !in ages;
  print |a|, " ", |b|, " ", |ages|, "\n";  // 3 2 4
  print ages["jack"], " ", ages["wendy"], " ", ages["ronald"], "\n";  // 70 52 66
  print a["bk"], " ", b["bk"], " ", ages["bk"], "\n";  // 8 67 67
}

method TestMapSubtraction() {
  var ages := map["ronald" := 66, "jack" := 70, "bk" := 67, "wendy" := 52];
  var d := ages - {};
  var e := ages - {"jack", "sanders"};
  print |ages|, " ", |d|, " ", |e|, "\n";  // 4 4 3
  print "ronald" in d, " ", "sanders" in d, " ", "jack" in d, " ", "sibylla" in d, "\n";  // true false true false
  print "ronald" in e, " ", "sanders" in e, " ", "jack" in e, " ", "sibylla" in e, "\n";  // true false false false
}

class MyClass {
  const name: string
  constructor (name: string) {
    this.name := name;
  }
}

method TestNullsAmongKeys() {
  var a := new MyClass("ronald");
  var b := new MyClass("wendy");
  var c: MyClass? := null;
  var d := new MyClass("jack");
  var e := new MyClass("sibylla");

  var m := map[a := 0, b := 1, c := 2, d := 3];
  var n := map[a := 0, b := 10, c := 20, e := 4];
  var o := map[b := 199, a := 198];

  var o' := map[b := 199, c := 55, a := 198];
  var o'' := map[b := 199, c := 56, a := 198];
  var o3 := map[c := 3, d := 16];
  var x0, x1, x2 := o == o', o' == o'', o' == o';
  print x0, " " , x1, " ", x2, "\n";  //  false false true

  var p := m + n;
  var q := n + o;
  var r := o + m;
  var s := o3 + o;
  var y0, y1, y2, y3 := p == n + m, q == o + n, r == m + o, s == o + o3;
  print y0, " " , y1, " ", y2, " ", y3, "\n";  // false false false true

  print p[a], " ", p[c], " ", p[e], "\n";  // 0 20 4
  print q[a], " ", q[c], " ", q[e], "\n";  // 198 20 4
  print r[a], " ", r[c], " ", e in r, "\n";  // 0 2 false

  p, q, r := GenericMap(m, n, o, a, e);
  print p[a], " ", p[c], " ", p[e], "\n";  // 0 20 4
  print q[a], " ", q[c], " ", q[e], "\n";  // 198 20 4
  print r[a], " ", r[c], " ", e in r, "\n";  // 0 2 false
}

method GenericMap<K, V>(m: map<K, V>, n: map<K, V>, o: map<K, V>, a: K, b: K)
    returns (p: map<K, V>, q: map<K, V>, r: map<K, V>)
  requires a in m.Keys && a in n.Keys
  requires b !in m.Keys && b !in o.Keys
  ensures p == m + n && q == n + o && r == o + m
{
  p := m + n;
  q := n + o;
  r := o + m;
  print a in m.Keys, " ", a in n.Keys, " ", a in p, " ", b in r, "\n";  // true true true false

  assert p.Keys == m.Keys + n.Keys;
  assert q.Keys == o.Keys + n.Keys;
  assert r.Keys == m.Keys + o.Keys;
}

method TestNullsAmongValues() {
  var a := new MyClass("ronald");
  var b := new MyClass("wendy");
  var d := new MyClass("jack");
  var e := new MyClass("sibylla");

  var m: map<int, MyClass?> := map[0 := a, 1 := b, 2 := null, 3 := null];
  var n: map<int, MyClass?> := map[0 := d, 10 := b, 20 := null, 4 := e];
  var o: map<int, MyClass?> := map[199 := null, 198 := a];

  var o': map<int, MyClass?> := map[199 := b, 55 := null, 198 := a];
  var o'': map<int, MyClass?> := map[199 := b, 56 := null, 198 := a];
  var o3: map<int, MyClass?> := map[3 := null, 16 := d];
  var x0, x1, x2 := o == o', o' == o'', o' == o';
  print x0, " " , x1, " ", x2, "\n";  //  false false true

  var p := m + n;
  var q := n + o;
  var r := o + m;
  var s := o3 + o;
  var y0, y1, y2, y3 := p == n + m, q == o + n, r == m + o, s == o + o3;
  print y0, " " , y1, " ", y2, " ", y3, "\n";  // false true true true

  print p[0].name, " ", p[1].name, " ", p[20], "\n";  // jack wendy null
  print q[0].name, " ", q[199], " ", q[20], "\n";  // jack null null
  print r[0].name, " ", r[198].name, " ", 20 in r, "\n";  // ronald ronald false

  p, q, r := GenericMap(m, n, o, 0, 321);
  print p[0].name, " ", p[1].name, " ", p[20], "\n";  // jack wendy null
  print q[0].name, " ", q[199], " ", q[20], "\n";  // jack null null
  print r[0].name, " ", r[198].name, " ", 20 in r, "\n";  // ronald ronald false
}

// -------------------------------------------------------------------------------------------

method MultiSetForming() {
  var s := {24, 23, 24};
  var q := [24, 23, 24];
  var m := multiset(s);
  print |m|, ": ", m[2], " ", m[23], " ", m[24], "\n";
  m := multiset(q);
  print |m|, ": ", m[2], " ", m[23], " ", m[24], "\n";
}

// -------------------------------------------------------------------------------------------

method ExplosiveUnion<T(0)>(a: multiset<T>, N: nat) returns (b: multiset<T>)
  // ensures b == a^N
{
  if N == 0 {
    return multiset{};
  }
  var n := 1;
  b := a;
  while n < N
    // invariant b == a^n
  {
    b := b + b;  // double the multiplicities of every element in b
    n := n + 1;
  }
}

method TestExplosiveUnion1<T(0)>(a: multiset<T>, N: nat, t: T) {
  var b := ExplosiveUnion(a, N);
  print "There are ", b[t], " occurrences of ", t, " in the multiset\n";
}

method TestExplosiveUnion() {
  TestExplosiveUnion1(multiset{}, 100, 58);
  TestExplosiveUnion1(multiset{58}, 30, 58);
  TestExplosiveUnion1(multiset{58}, 100, 58);  // this requires BigInteger multiplicities in multisets
  var m: multiset<MyClass?> := multiset{null};
  TestExplosiveUnion1(m, 100, null);  // also test null, since the C# implementation does something different for null
}

// -------------------------------------------------------------------------------------------

module Regressions {
  newtype uint32 = i:int | 0 <= i < 0x1_0000_0000

  method Test() {
    TestMap();
    TestSeq();
    TestMultiset();
  }

  method TestMap() {
    print "Map===\n";
    var s: map<uint32, uint32> := map[1 := 123];
    var u := s[1 := 40];
    print "|s|=", |s|, " |u|=", |u|, "\n";  // 1 1
    print "s[1]=", s[1], " u[1]=", u[1], "\n";  // 123 40

    var S: map<int, uint32> := map[1 := 123];
    var U := S[1 := 41];
    print "|S|=", |S|, " |U|=", |U|, "\n";  // 1 1
    print "S[1]=", S[1], " U[1]=", U[1], "\n";  // 123 41
  }

  method TestSeq() {
    print "Seq===\n";
    var s: seq<uint32> := [14, 123];
    var u := s[1 := 42];
    print "|s|=", |s|, " |u|=", |u|, "\n";  // 2 2
    print s[1], " ", u[1], ", ";  // 123 42
    print s[1 as int], " ", u[1 as int], ", ";  // 123 42
    print s[1 as bv3], " ", u[1 as bv3], "\n";  // 123 42

    u := s[1 as uint32 := 43];
    print "|s|=", |s|, " |u|=", |u|, "\n";  // 2 2
    print s[1], " ", u[1], ", ";  // 123 43
    print s[1 as int], " ", u[1 as int], ", ";  // 123 43
    print s[1 as bv3], " ", u[1 as bv3], "\n";  // 123 43

    u := s[1 as bv3 := 44];
    print "|s|=", |s|, " |u|=", |u|, "\n";  // 2 2
    print s[1], " ", u[1], ", ";  // 123 44
    print s[1 as int], " ", u[1 as int], ", ";  // 123 44
    print s[1 as bv3], " ", u[1 as bv3], "\n";  // 123 44
  }

  method TestMultiset() {
    print "Multiset===\n";
    var s: multiset<uint32> := multiset{14, 123};
    var u := s[123 := 3];
    print "|s|=", |s|, " |u|=", |u|, "\n";  // 2 4
    print s[123], " ", u[123], "\n";  // 1 3

    u := s[123 := 3 /*as uint32*/];
    print "|s|=", |s|, " |u|=", |u|, "\n";  // 2 4
    print s[123], " ", u[123], "\n";  // 1 3
  }
}
