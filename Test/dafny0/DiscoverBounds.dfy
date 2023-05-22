// RUN: %dafny /print:"%t.print" /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
