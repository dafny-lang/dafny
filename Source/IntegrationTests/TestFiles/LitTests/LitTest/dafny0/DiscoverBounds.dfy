// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --allow-warnings --relax-definite-assignment

newtype NT = x | 0 <= x < 100
newtype UT = NT

newtype Lower = x | -2 <= x
newtype Upper = x: Lower | x < 100

newtype Int = int

newtype NR = r | -2.0 <= r <= 5.4

method Main()
{
  var n: NT :| true;
  var t: UT :| true;

  var u: Upper :| true;
  var l: Lower :| l < 20;
  var o: Lower :| true;

  var j: Int :| true;

  print n, "\n";
  print t, "\n";
  print u, "\n";
  print l, "\n";
  print o, "\n";

  var b: bool;
  b := forall n': NT :: true ==> P(n' as int);
  b := forall t': UT :: true ==> P(t' as int);
  b := forall u': Upper :: true ==> P(u' as int);
  b := forall l': Lower :: l' < 20 ==> P(l' as int);
  b := forall j': Int :: -3 <= j' < 7 ==> P(j' as int);

  var x0, x1, x2, x3, x4, x5 := OtherEq(false, {}, [], map[198 := 200], multiset{}, iset{}, imap[]);
  print x0, " ", x1, " ", x2, " ", x3, " ", x4, " ", x5, "\n";
  x0, x1, x2, x3, x4, x5 := OtherEq(true, {}, [], map[198 := 200], multiset{}, iset{}, imap[]);
  print x0, " ", x1, " ", x2, " ", x3, " ", x4, " ", x5, "\n";

  EnumerateOverInfiniteCollections();
  Casts();
  MakeSureBoundsAreDiscoveredWithoutFirstSimplifyingTheExpression();
}

predicate P(x: int)
{
  x == 157
}

predicate Q(r: real)
{
  r / 2.0 <= r
}

method OtherEq<U,V(==)>(b: bool, s: set<int>, t: seq<real>, u: map<U,V>, v: multiset<char>, w: iset<bv12>, x: imap<bv28,int>)
  returns (s': set<int>, t': seq<real>, u': map<U,V>, v': multiset<char>, w': iset<bv12>, x': imap<bv28,int>)
{
  if b {
    s' :| s' == s;
    t' :| t' == t;
    u' :| u' == u;
    v' :| v' == v;
    w' :| w' == w;
    x' :| x' == x;
  } else {
    s' := var s'' :| s'' == s; s'';
    t' := var t'' :| t'' == t; t'';
    u' := var u'' :| u'' == u; u'';
    v' := var v'' :| v'' == v; v'';
    w' := var w'' :| w'' == w; w'';
    x' := var x'' :| x'' == x; x'';
  }
}

predicate LessThanFour(x: int) {
  x < 4
}

method EnumerateOverInfiniteCollections() {
  // ===== iset
  var s := {3, 3, 3, 5};

  // Once, the following RHS caused "u" to be auto-ghost. (Oddly enough, when using the same RHS as a
  // separate assignment, the RHS was not considered to be ghost. So, we test both here.)
  var u := iset x | x in s;
  u := iset x | x in s;
  assert 3 in u;

  // Once, the compilation of the following was rejected, because an iset was not considered enumerable. But it is.
  var y :| y in u && LessThanFour(y); // an iset is enumerable, so it's compilable
  print y, "\n"; // 3

  // ===== imap
  
  var m := map[3 := true, 5 := false];

  // Once, the following RHS caused "u" to be auto-ghost.  (Oddly enough, when using the same RHS as a
  // separate assignment, the RHS was not considered to be ghost. So, we test both here.)
  var w := imap x | x in m :: true;
  w := imap x | x in m :: true;

  // Once, the compilation of the following was rejected, because an imap was not considered enumerable. But it is.
  var z :| z in w && LessThanFour(z); // an imap is enumerable, so it's compilable
  print z, "\n"; // 3
}

method Casts() {
  // casts around just the variable is fine
  print forall x :: -12 <= x && (x as int - 2) as int < 0 ==> LessThanFour(x), " "; // true
  print forall x :: 12 <= x && (x as int - 20) as int < 0 ==> LessThanFour(x), "\n"; // false
  // casts among subset types are also fine
  print forall x: int :: 12 <= x && (x as int - 2) as nat < 24 ==> LessThanFour(x), " "; // false
  print forall x: nat :: 12 <= x && (x as int - 20) as int < 0 ==> LessThanFour(x), "\n"; // false
  // not a cast, but involving arithmetic expressions
  print forall x: int :: -100 <= x - 3 < -11 ==> LessThanFour(x as int), "\n"; // true
}

method MakeSureBoundsAreDiscoveredWithoutFirstSimplifyingTheExpression() {
  var b := forall n': NT :: true;
  print b, "\n"; // true
}
