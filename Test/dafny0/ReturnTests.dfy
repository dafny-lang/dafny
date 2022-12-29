// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class N
{
   var i: int;
   method newN(n: N)
      modifies this, n;
   {
      n.i := 1;
      i := 1;
   }
   method safe(n: N)
      modifies this;
   {
      i := n.i;
   }
}

method m(v: int, n: N) returns (r: int)
   modifies n;
   ensures r == v;
{
   r := v; // implict return still works.
}

method testing1() returns (a: int, b: set<int>)
{
   return 1, {1, 2, 3}; // type checking
}
method testing2() returns (a: int, b: int)
   ensures a == 1 && b == 2;
{
   a, b := 2, 1;
   return b, a; // test of parallel assignment.
}
method testing3() returns (a: int, b: int)
   ensures a == 1 && b == 2;
{
   a, b := 2, 1; // these are wrong
   if (true)
   {
      var a, b := 3, 4;
      return 1, 2;// return updates non-shadowed, formal parameters correctly
   }
}

method testing4(nnn: N) returns (n: N)
{
   return new N.safe(nnn); // only modifies 'this', which is the fresh N
}

method testing5() returns (r: int)
   ensures r == 2;
{
   r := 2;
   return; // sanity check.
}

iterator yieldTesting() yields (a: int, b: int)
   yield ensures a == 1 && b == 2;
{
   a, b := 2, 1; // these are wrong
   if (true)
   {
      var a, b := 3, 4;
      yield 1, 2;// return updates non-shadowed, formal parameters correctly
   }
}
