// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Checking that the reads clause also is checked over requires

class C { var u : int; }

function nope1(c : C):()
     requires c.u > 0;
{()}

function ok1(c : C):()
     requires c.u > 0;
     reads c;
{()}

function nope2(c : C?):()
     requires c != null && c.u > 0;
     reads if c != null then {} else {c};
{()}

function ok2(c : C?):()
     requires c != null && c.u > 0;
     reads if c != null then {c} else {};
{()}

function nope3(xs : seq<C>):()
     requires |xs| > 0 && xs[0].u > 0;
{()}

function ok3(xs : seq<C>):()
     requires |xs| > 0 && xs[0].u > 0;
     reads xs;
{()}

function nope4(c : C, xs : set<C>):()
     requires c !in xs ==> c.u > 0;
     reads xs;
{()}

function ok4(c : C, xs : set<C>):()
     requires c in xs ==> c.u > 0;
     reads xs;
{()}

// reads over itself

class R {
  var r : R
  constructor () {
    r := this;
  }
}

function nope5(r : R?):()
  reads if r != null then {r.r} else {};
{()}

function ok5(r : R?):()
  reads if r != null then {r, r.r} else {};
{()}

// Reads checking where there are circularities among the expressions

class CircularChecking {
  ghost var Repr: set<object>

  function F(): int
    reads this, Repr

  function F'(): int
    reads Repr, this  // this is also fine

  function G0(): int
    reads this
    requires Repr == {} && F() == 100

  function G1(): int
    reads this
    requires F() == 100  // fine, since the next line tells us that Repr is empty
    requires Repr == {}

  function H0(cell: Cell): int
    reads Repr  // by itself, this reads is not self-framing
    requires this in Repr  // lo and behold!  So, reads clause is fine after all

  function H1(cell: Cell): int
    reads this, Repr
    requires cell in Repr
    requires cell.data == 10

  function H2(cell: Cell): int
    reads this, Repr
    requires cell.data == 10  // this is okay, too, since reads checks are postponed
    requires cell in Repr
}

class Cell { var data: int }

// Test the benefits of the new reads checking for function checking

function ApplyToSet<X>(S: set<X>, f: X ~> X): set<X>
  requires forall x :: x in S ==> f.reads(x) == {} && f.requires(x)
{
  if S == {} then {} else
    var x :| x in S;
    ApplyToSet(S - {x}, f) + {f(x)}
}

function ApplyToSet_AltSignature0<X>(S: set<X>, f: X ~> X): set<X>
  requires forall x :: x in S ==> f.requires(x) && f.reads(x) == {}

function ApplyToSet_AltSignature1<X>(S: set<X>, f: X ~> X): set<X>
  requires forall x :: x in S ==> f.reads(x) == {}
  requires forall x :: x in S ==> f.requires(x)

function ApplyToSet_AltSignature2<X>(S: set<X>, f: X ~> X): set<X>
  requires (forall x :: x in S ==> f.reads(x) == {}) ==> forall x :: x in S ==> f.requires(x)
  // (this precondition would not be good enough to check the body above)

function FunctionInQuantifier0(): int
  requires exists f: int ~> int :: f(10) == 100  // error (x2): precondition violation and insufficient reads

function FunctionInQuantifier1(): int
  requires exists f: int ~> int :: f.requires(10) && f(10) == 100  // error: insufficient reads

function FunctionInQuantifier2(): int
  requires exists f: int ~> int :: f.reads(10) == {} && f.requires(10) && f(10) == 100
  ensures FunctionInQuantifier2() == 100
{
  var f: int ~> int :| f.reads(10) == {} && f.requires(10) && f(10) == 100;  // fine :) :)
  f(10)
}

class DynamicFramesIdiom {
  ghost var Repr: set<object>
  predicate IllFormed_Valid()
    reads Repr  // error: reads is not self framing (notice the absence of "this")
  {
    this in Repr  // this says that the predicate returns true if "this in Repr", but the
                  // predicate can also be invoked in a state where its body will evaluate to false
  }
}

class ReadsTestsInsideLetSuchThat {
  var y: int

  function F(): int {
    var yy :| yy == this.y;  // error: F does not have permission to read this.y
    yy
  }
}

class ConstInitializers {
  var x: int

  const u: int := x // error: insufficient reads clause

  const v: int := F() // error: insufficient reads clause
  function method F(): int
    reads this
  {
    x + x
  }
}
