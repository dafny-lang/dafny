// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Sets();
  SubSets();
  MultiSets();
  Sequences();
  Strings();
  Maps();
  MultiSetForming();
}

method Sets() {
  var a := {};
  var b := {17, 82, 17, 82};
  var c := {12, 17};
  print "Sets: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  union: ", a + b, " ", b + c, "\n";
  print "  intersection: ", a * b, " ", b * c, "\n";
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

method MultiSets() {
  var a := multiset{};
  var b := multiset{17, 82, 17, 82};
  var c := multiset{12, 17};
  print "Multisets: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  union: ", a + b, " ", b + c, "\n";
  print "  intersection: ", a * b, " ", b * c, "\n";
  print "  disjoint: ", a !! b, " ", b !! c, "\n";
  print "  subset: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper subset: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  membership: ", 17 in a, " ", 17 in b, " ", 17 in c, "\n";
  print "  multiplicity: ", a[17], " ", b[17], " ", c[17], "\n";
}

method Sequences() {
  var a := [];
  var b := [17, 82, 17, 82];
  var c := [12, 17];
  print "Sequences: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  concatenation: ", a + b, " ", b + c, "\n";
  print "  prefix: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper prefix: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  membership: ", 17 in a, " ", 17 in b, " ", 17 in c, "\n";
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

method Maps() {
  var a := map[];
  var b := map[17 := 2, 82 := 2];
  var c := map[17 := 0, 12 := 26];
  print "Maps: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  keys: ", a.Keys, " ", b.Keys, " ", c.Keys, "\n";
  print "  values: ", a.Values, " ", b.Values, " ", c.Values, "\n";
  print "  items: ", a.Items, " ", b.Items, " ", c.Items, "\n";
  print "  disjoint: ", a !! b, " ", b !! c, "\n";
  print "  lookup: ", 17 in a, " ", b[17], " ", c[17], "\n";
  print "  update: ", a[17 := 6], " ", b[17 := 6], " ", c[17 := 6], "\n";
}

method MultiSetForming() {
  var s := {24, 23, 24};
  var q := [24, 23, 24];
  var m := multiset(s);
  print |m|, ": ", m[2], " ", m[23], " ", m[24], "\n";
  m := multiset(q);
  print |m|, ": ", m[2], " ", m[23], " ", m[24], "\n";
}
