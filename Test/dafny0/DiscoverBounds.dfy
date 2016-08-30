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
}

predicate method P(x: int)
{
  x == 157
}

predicate method Q(r: real)
{
  r / 2.0 <= r
}

method OtherEq<U,V>(s: set<int>, t: seq<real>, u: map<U,V>, v: multiset<char>, w: iset<bv12>, x: imap<bv28,int>)
{
  if * {
    var s' :| s' == s;
//    var t' :| t' == t;  // TODO: use an ExactBoundedPool and compile this
//    var u' :| u' == u;  // TODO: use an ExactBoundedPool and compile this
//    var v' :| v' == v;  // TODO: use an ExactBoundedPool and compile this
    var w' :| w' == w;
//    var x' :| x' == x;  // TODO: use an ExactBoundedPool and compile this
  } else {
    var s'' := var s' :| s' == s; s';
    // TODO: var t'' := var t' :| t' == t; t';
    // TODO: var u'' := var u' :| u' == u; u';
    // TODO: var v'' := var v' :| v' == v; v';
    var w'' := var w' :| w' == w; w';
    // TODO: var x'' := var x' :| x' == x; x';
  }
}
