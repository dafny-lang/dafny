// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
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
}

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
  print "  membership: ", 17 in a, " ", 17 in b, " ", 17 in c, "\n";
}

method SubSets() {
  var s: set<char> := {'a', 'b', 'c', 'd'};
  var b0 := forall r | r <= s :: |r| == 2;
  var b1 := exists r | r <= s :: |r| == 2;
  print b0, " ", b1, "\n";
  var S := set r | r <= s && P(r);
  print "|s|=", |s|, " |S|=", |S|, "\n";
  print S, "\n";
}
predicate method P(r: set<char>) { true }

type IntMultiSet = multiset<int>

method MultiSets() {
  var a := multiset{};
  var b : IntMultiSet := multiset{17, 82, 17, 82};
  var c := multiset{12, 17};
  print "Multisets: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  union: ", a + b, " ", b + c, "\n";
  print "  intersection: ", a * b, " ", b * c, "\n";
  print "  difference: ", a - b, " ", b - c, "\n";
  print "  disjoint: ", a !! b, " ", b !! c, "\n";
  print "  subset: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper subset: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  membership: ", 17 in a, " ", 17 in b, " ", 17 in c, "\n";
  print "  update: ", a[17 := 2], " ", b[17 := 2], " ", c[17 := 2], "\n";
  print "  multiplicity: ", a[17], " ", b[17], " ", c[17], "\n";
}

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

    print data[..u0], " ";  // it is unfortunate how these get printed in Java
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

type IntMap = map<int, int>

method Maps() {
  var a := map[];
  var b : IntMap := map[17 := 2, 82 := 2];
  var c := map[17 := 0, 12 := 26];
  print "Maps: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  keys: ", a.Keys, " ", b.Keys, " ", c.Keys, "\n";
  print "  values: ", a.Values, " ", b.Values, " ", c.Values, "\n";
  print "  items: ", a.Items, " ", b.Items, " ", c.Items, "\n";
  print "  disjoint: ", a !! b, " ", b !! c, "\n";
  print "  update: ", a[17 := 6], " ", b[17 := 6], " ", c[17 := 6], "\n";
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
}

datatype Color = Blue | Yellow | Red

method MultiSetForming() {
  var s := {24, 23, 24};
  var q := [24, 23, 24];
  var m := multiset(s);
  print |m|, ": ", m[2], " ", m[23], " ", m[24], "\n";
  m := multiset(q);
  print |m|, ": ", m[2], " ", m[23], " ", m[24], "\n";
}

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

class MyClass { }

method TestExplosiveUnion() {
  TestExplosiveUnion1(multiset{}, 100, 58);
  TestExplosiveUnion1(multiset{58}, 30, 58);
  TestExplosiveUnion1(multiset{58}, 100, 58);  // this requires BigInteger multiplicities in multisets
  var m: multiset<MyClass?> := multiset{null};
  TestExplosiveUnion1(m, 100, null);  // also test null, since the C# implementation does something different for null
}
