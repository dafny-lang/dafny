// RUN: %dafny /print:"%t.print" /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype NT = x | 0 <= x < 100
newtype UT = NT

newtype Lower = x | 10 <= x
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
  b := forall n': NT :: true ==> P(int(n'));
  b := forall t': UT :: true ==> P(int(t'));
  b := forall u': Upper :: true ==> P(int(u'));
  b := forall l': Lower :: l' < 20 ==> P(int(l'));
  b := forall o': Lower :: true ==> P(int(o'));  // error: cannot find finite range
  b := forall j': Int :: -3 <= j' < 7 ==> P(int(j'));

  b := forall r: real :: 0.0 <= r <= 100.0 ==> Q(r);  // error: cannot find finite range
  b := forall r': NR :: true ==> Q(real(r'));  // error: cannot find finite range
}

predicate method P(x: int)
{
  x == 157
}

predicate method Q(r: real)
{
  r / 2.0 <= r
}
