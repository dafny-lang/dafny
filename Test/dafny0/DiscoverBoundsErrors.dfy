// RUN: %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Lower = x | -2 <= x

newtype NR = r | -2.0 <= r <= 5.4

method Main()
{
  var b;
  b := forall o': Lower :: true ==> P(o' as int);  // error: cannot find finite range
  b := forall r: real :: 0.0 <= r <= 100.0 ==> Q(r);  // error: cannot find finite range
  b := forall r': NR :: true ==> Q(r' as real);  // error: cannot find finite range
}

predicate method P(x: int)
{
  x == 157
}

predicate method Q(r: real)
{
  r / 2.0 <= r
}
