// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class N
{
   var i: int;
   method newN(n: N)
      requires n != null;
      modifies this, n;
   {
      n.i := 1;
      i := 1;
   }
   method safe(n: N)
      requires n != null;
      modifies this;
   {
      i := n.i;
   }
}

method m(v: int, n: N) returns (r: int)
   modifies n;
   ensures r == v;
{
   r := v;
}
method testing1() returns (s: int)
   ensures s == 3;
{
   var n := new N;
   return m(3, n); // ERROR: methods disallowed.
}
method testing2() returns (s: int, b: int)
   ensures s == 3;
{
   var n := new N;
   return m(3, n), 2; // ERROR: methods disallowed.
}

method testing3() returns (n: N)
{
   return new N.newN(n); // ERROR: disallowed, as newN() modifies n
}
