// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:tailrecursion} A(q: int) returns (x: int, ghost y: bool, z: nat)
{
  if (q < 10) {
    x, y, z := 15, true, 20;
  } else {
    ghost var u;
    x, u, z := A(q-1);
    y := !u;
  }
}

method {:tailrecursion} B(q: int) returns (x: int, ghost y: bool, z: nat)
{
  if (q < 10) {
    x, y, z := 15, true, 20;
  } else {
    ghost var u;
    x, u, z := B(q-1);  // error: not a tail call, because it is followed by an increment to x
    y, x := !u, x + 1;
  }
}

method C(q: int) returns (x: int)
  decreases *;
{
  x := C(q-1);
}

method D(q: int) returns (x: int)
{
  x := D(q-1);
  x := x + 1;
}

method {:tailrecursion} E0(q: int) returns (x: int)  // error: not allowed, because the method is not
  // tail recursive (since mutually recursive methods are currently not recognized as being tail recursive)
{
  x := E1(q-1);
}
method {:tailrecursion} E1(q: int) returns (x: int)  // error: not allowed, because the method is not
  // tail recursive (since mutually recursive methods are currently not recognized as being tail recursive)
{
  x := E0(q);
}

method F0(q: int) returns (x: int)
  decreases *;  // fine
{
  x := D(q);
}
method F1(q: int) returns (x: int)
  decreases 5;  // since this is okay (that is, you can--for no particular reason--add a 'decreases' clause to a non-recursive method), the 'decreases *' above is also allowed
{
  x := D(q);
}

method {:tailrecursion} G0(q: int) returns (x: int)
  decreases *;
{
  x := D(q);
}
method {:tailrecursion false} G1(q: int) returns (x: int)  // the annotation tells the compiler not to tail-call optimize
  decreases *;
{
  x := G1(q);
}

method H0(q: int) returns (x: int)
  decreases *;  // fine
method {:tailrecursion} H1(q: int) returns (x: int)
  decreases *;  // fine
method H2(q: int) returns (x: int)
  decreases 5;  // fine

class {:autocontracts} MyAutoContractClass {
  var left: MyAutoContractClass?

  predicate Valid() { true }

  method {:tailrecursion} VisitLeft(val: int)
  {
    if left != null {
      left.VisitLeft(val);  // this is a tail call, because what :autocontracts appends is ghost
    }
  }
}

method {:tailrecursion} OtherTailCall(n: int) {
  ghost var x := 12;
  if n > 0 {
    OtherTailCall(n-1);  // tail call
  }
  x := 14;
  { x := 13; }
  ghost var h := 15;
  if n < h*30 { } // this is a ghost statement as well
  if n < 230 { } // and this can be (and is) considered ghost as well
  if (*) { x := x + 1; }  // this, too
}

class TailConstructorRegressionTest
{
  var next: TailConstructorRegressionTest
  constructor {:tailrecursion} (n: nat)
  {
    if n != 0 {
      next := new TailConstructorRegressionTest(n-1);  // error: not a tail call, because it is followed by an assignment
    }
  }
}

class TailConstructorRegressionTest'
{
  method {:tailrecursion} Compute<G(0)>(n: nat)
  {
    if n == 0 {
      print "\n";
    } else if n % 2 == 1 {
      var g: G;
      print g, " ";
      Compute<G>(n-1);
    } else {
      Compute<bool>(n-1);  // error: not a tail call, because the type parameters don't match
    }
  }

  method {:tailrecursion} Run<H,G(0)>(n: nat)
  {
    if n == 0 {
      print "\n";
    } else if n % 2 == 1 {
      var g: G;
      print g, " ";
      Run<H,G>(n-1);
    } else {
      Run<H,bool>(n-1);  // error: not a tail call, because the type parameters don't match
    }
  }
}
