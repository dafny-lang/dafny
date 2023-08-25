// RUN: %exits-with 4 %dafny /compile:0 /deprecation:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The first half of this file is a clone of Reads.dfy, 
// but modified to use methods instead of functions wherever possible,
// to provide more testing coverage of the newer feature
// of allowing and enforcing reads clauses on methods as well.

// Checking that the reads clause also is checked over requires

class C { var u : int; }

// Unlike functions, the default for methods is * instead of {}
ghost method yup1(c : C)
     requires c.u > 0
{}

ghost method nope1(c : C)
     requires c.u > 0
     reads {}
{}

ghost method ok1(c : C)
     requires c.u > 0
     reads c
{}

ghost method nope2(c : C?)
     requires c != null && c.u > 0
     reads if c != null then {} else {c}
{}

ghost method ok2(c : C?)
     requires c != null && c.u > 0
     reads if c != null then {c} else {}
{}

// Unlike functions, the default for methods is * instead of {}
ghost method yup3(xs : seq<C>)
     requires |xs| > 0 && xs[0].u > 0
{}

ghost method nope3(xs : seq<C>)
     requires |xs| > 0 && xs[0].u > 0
     reads {}
{}

ghost method ok3(xs : seq<C>)
     requires |xs| > 0 && xs[0].u > 0
     reads xs;
{}

ghost method nope4(c : C, xs : set<C>)
     requires c !in xs ==> c.u > 0
     reads xs
{}

ghost method ok4(c : C, xs : set<C>)
     requires c in xs ==> c.u > 0
     reads xs
{}

// reads over itself

class R {
  var r : R
  constructor () {
    r := this;
  }
}

ghost method nope5(r : R?)
  reads if r != null then {r.r} else {}
{}

ghost method ok5(r : R?)
  reads if r != null then {r, r.r} else {}
{}

// Reads checking where there are circularities among the expressions

class CircularChecking {
  ghost var Repr: set<object>

  ghost function F(): int
    reads this, Repr

  ghost method F'() returns (r: int)
    reads Repr, this  // this is also fine

  ghost method G0() returns (r: int)
    reads this
    requires Repr == {} && F() == 100

  ghost method G1() returns (r: int)
    reads this
    requires F() == 100  // fine, since the next line tells us that Repr is empty
    requires Repr == {}

  ghost method H0(cell: Cell) returns (r: int)
    reads Repr  // by itself, this reads is not self-framing
    requires this in Repr  // lo and behold!  So, reads clause is fine after all

  ghost method H1(cell: Cell) returns (r: int)
    reads this, Repr
    requires cell in Repr
    requires cell.data == 10

  ghost method H2(cell: Cell) returns (r: int)
    reads this, Repr
    requires cell.data == 10  // this is okay, too, since reads checks are postponed
    requires cell in Repr
}

class Cell { var data: int }

// Test the benefits of the new reads checking for function checking

ghost method ApplyToSet<X>(S: set<X>, f: X ~> X) returns (r: set<X>)
  requires forall x :: x in S ==> f.reads(x) == {} && f.requires(x)
  reads {}
{
  if S == {} {
    return {};
  } else {
    var x :| x in S;
    var r' := ApplyToSet(S - {x}, f);
    r := r + {f(x)};
  }
}

ghost method ApplyToSet_AltSignature0<X>(S: set<X>, f: X ~> X) returns (r: set<X>)
  requires forall x :: x in S ==> f.requires(x) && f.reads(x) == {}
  reads {}

ghost method ApplyToSet_AltSignature1<X>(S: set<X>, f: X ~> X) returns (r: set<X>)
  requires forall x :: x in S ==> f.reads(x) == {}
  requires forall x :: x in S ==> f.requires(x)
  reads {}

ghost method ApplyToSet_AltSignature2<X>(S: set<X>, f: X ~> X) returns (r: set<X>)
  requires (forall x :: x in S ==> f.reads(x) == {}) ==> forall x :: x in S ==> f.requires(x)
  // (this precondition would not be good enough to check the body above)
  reads {}

ghost method FunctionInQuantifier0() returns (r: int)
  requires exists f: int ~> int :: f(10) == 100  // error (x2): precondition violation and insufficient reads
  reads {}

ghost method FunctionInQuantifier1() returns (r: int)
  requires exists f: int ~> int :: f.requires(10) && f(10) == 100  // error: insufficient reads
  reads {}

ghost method FunctionInQuantifier2() returns (r: int)
  requires exists f: int ~> int :: f.reads(10) == {} && f.requires(10) && f(10) == 100
  reads {}
  ensures r == 100
{
  var f: int ~> int :| f.reads(10) == {} && f.requires(10) && f(10) == 100;  // fine :) :)
  return f(10);
}

class DynamicFramesIdiom {
  ghost var Repr: set<object>
  ghost predicate IllFormed_Valid()
    reads Repr  // error: reads is not self framing (notice the absence of "this")
  {
    this in Repr  // this says that the predicate returns true if "this in Repr", but the
                  // predicate can also be invoked in a state where its body will evaluate to false
  }
}

class ReadsTestsInsideLetSuchThat {
  var y: int

  ghost method F() returns (r: int) 
    reads {}
  {
    var yy :| yy == this.y;  // error: F does not have permission to read this.y
    return yy;
  }
}

// ConstInitializers: not applicable

// And now for brand new freshly-baked tests!

