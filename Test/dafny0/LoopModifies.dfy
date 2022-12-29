// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// regular modifies sanity test:
method Testing1(a: array<int>)
   requires a.Length > 0;
{
   a[0] := 0; // ERROR
}

// array inside while loop, without explict modifies clause:
method Testing2(a: array<int>)
   requires a.Length > 0;
{
   var i := 0;
   while(i < 10)
      invariant 0 <= i <= 10;
   {
      a[0] := i; // ERROR
      i := i + 1;
   }
}

// array inside while loop, without explict modifies clause:
method Testing2A(a: array<int>)
   requires a.Length > 0;
   modifies a;
{
   var i := 0;
   while(i < 10)
      invariant 0 <= i <= 10;
   {
      // now there is no problem.
      a[0] := i;
      i := i + 1;
   }
}

// array inside while loop, with explict modifies clause:
method Testing3(a: array<int>)
   requires a.Length > 0;
{
   var i := 0;
   while(i < 10)
      invariant 0 <= i <= 10;
      modifies {};
   {
      a[0] := i; // ERROR
      i := i + 1;
   }
}

// modifies restricts:
method Testing4(a: array<int>)
   requires a.Length > 0;
   modifies a;
{
   var i := 0;
   while(i < 10)
      invariant 0 <= i <= 10;
      modifies {};
   {
      a[0] := i; // ERROR
      i := i + 1;
   }
   // should be ok.
   a[0] := 1;
}

// modifies not a subset:
method Testing5(a: array<int>)
   requires a.Length > 0;
   modifies {};
{
   var i := 0;
   while(i < 10) // ERROR
      invariant 0 <= i <= 10;
      modifies a;
   {
      a[0] := i;
      i := i + 1;
   }
}

// modifies is a subset, but modifications occur outside:
method Testing6(a: array<int>, b: array<int>)
   requires a.Length > 0;
   requires b.Length > 0;
   modifies a, b;
{
   var i := 0;
   while(i < 10)
      invariant 0 <= i <= 10;
      modifies a;
   {
      // cool.
      a[0] := i;

      // not cool.
      b[0] := i; // ERROR
      i := i + 1;
   }
}

// heap outside modifies is actually preserved:
method Testing7(a: array<int>, b: array<int>)
   requires a.Length > 0;
   requires b.Length > 0;
   requires a != b;
   modifies a, b;
{
   var i := 0;
   b[0] := 4;
   while(i < 10)
      invariant 0 <= i <= 10;
      modifies a;
   {
      // still good.
      a[0] := i;
      i := i + 1;
   }
   // this is new, and good:
   assert b[0] == 4;
}

// modifies actually restrict frame when nested:
method Testing8(a: array<int>, b: array<int>, c: array<int>)
   requires a.Length > 0;
   requires b.Length > 0;
   requires c.Length > 0;
   requires a != b && b != c && c != a;
   modifies a, b, c;
{
   var i := 0;
   b[0] := 4;
   while(i < 10)
      invariant 0 <= i <= 10;
      modifies a, b;
   {
      var j := 0;
      while(j < 10)
         invariant 0 <= j <= 10;
         modifies a;
      {
         // happy:
         a[0] := j;
         // not happy:
         b[0] := i; // ERROR
         j := j + 1;
      }
      i := i + 1;
   }
   c[0] := 1;
}

// heap outside modifies preserved when nested:
method Testing9(a: array<int>, b: array<int>, c: array<int>)
   requires a.Length > 0;
   requires b.Length > 0;
   requires c.Length > 0;
   requires a != b && b != c && c != a;
   modifies a, b, c;
{
   var i := 0;
   b[0] := 4;
   while(i < 10)
      invariant 0 <= i <= 10;
      modifies a, b;
   {
      var j := 0;
      b[0] := i;
      while(j < 10)
         invariant 0 <= j <= 10;
         modifies a;
      {
         a[0] := j;
         j := j + 1;
      }
      assert b[0] == i;
      i := i + 1;
   }
   c[0] := 1;
}

// allocation, fresh tests:

// allocated things not automatically in modifies of loops:
method Testing10(a: array<int>)
   requires a.Length > 0;
   modifies a;
{
   var i := 0;
   var arr := new int[1];
   arr[0] := 1; // good, even though not in method modifies.
   while(i < 10)
      invariant 0 <= i <= 10;
      modifies a;
   {
      arr[0] := 1; // ERROR
      i := i + 1;
   }
}

// unless no modifies given, in which case the context is used:
method Testing10a(a: array<int>)
   requires a.Length > 0;
   modifies a;
{
   var i := 0;
   var arr := new int[1];
   arr[0] := 1; // still good.
   while(i < 10)
      invariant 0 <= i <= 10;
   {
      arr[0] := 1; // no modifies, so allowed to touch arr.
      i := i + 1;
   }
}


// loop inherits modifies clause of enclosing loop, not method.
method Testing10b(a: array<int>, b: array<int>)
   requires a.Length > 0;
   requires b.Length > 0;
   requires a != b;
   modifies a,b;
{
   b[0] := 4;
   var j := 0;
   while (j < 10)
      modifies a;
   {
      var i := 1;
      while (i < 10)
      // note: no explicit modifies clause
      {
         a[0] := 1;
		 i := i + 1;
      }
      assert b[0] == 4; // should be fine.
	  j := j + 1;
   }
}

// arr still accessible after loop that can't touch it.
method Testing11()
{
   var i := 0;
   var arr := new int[1];
   while(i < 10)
      invariant 0 <= i <= 10;
      modifies {};
   {
      arr := new int[1];
      arr[0] := 1;
      var j := 0;
      while(j < 10)
         invariant 0 <= j <= 10;
         modifies {};
      {
         // can't touch arr in here.
         j := j + 1;
      }
      arr[0] := 2;
      i := i + 1;
   }
}

// allocation inside a loop is still ok:
method Testing11a(a: array<int>)
   requires a.Length > 0;
   modifies a;
{
   var i := 0;
   while(i < 10)
      invariant 0 <= i <= 10;
      modifies a;
   {
      var arr := new int[1];
      arr[0] := 1; // can modify arr, even though it
                   // is not in modifies because it is fresh.
      var j := 0;
      while(j < 10)
         invariant 0 <= j <= 10;
         modifies a;
      {
         arr[0] := 3; // ERROR: can't touch arr, as allocated before modifies captured.
         j := j + 1;
      }
      i := i + 1;
   }
}

class Elem
{
   var i: int;
}

// capture of modifies clause at beginning of loop:
method Testing12(a: Elem, b: Elem, c: Elem)
   requires a != b && b != c && c != a; // all different.
   modifies a, b, c;
{
   var i := 0;
   var S := {a, b, c};
   // S "captured" here for purposes of modifies clause.
   while(S != {})
      modifies S;
      decreases S;
   {
      var j :| j in S;
      // these still good, even though S shrinks to not include them.
      a.i := i;
      b.i := i;
      c.i := i;
      S := S - {j};
      i := i + 1;
   }
}
