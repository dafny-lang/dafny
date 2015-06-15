// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Checking that the reads clause also is checked over requires

class C { var u : int; }

function nope1(c : C):()
     requires c != null && c.u > 0;
{()}

function ok1(c : C):()
     requires c != null && c.u > 0;
     reads c;
{()}

function nope2(c : C):()
     requires c != null && c.u > 0;
     reads if c != null then {} else {c};
{()}

function ok2(c : C):()
     requires c != null && c.u > 0;
     reads if c != null then {c} else {};
{()}

function nope3(xs : seq<C>):()
     requires |xs| > 0 && xs[0] != null && xs[0].u > 0;
{()}

function ok3(xs : seq<C>):()
     requires |xs| > 0 && xs[0] != null && xs[0].u > 0;
     reads xs;
{()}

function nope4(c : C, xs : set<C>):()
     requires c != null && c !in xs ==> c.u > 0;
     reads xs;
{()}

function ok4(c : C, xs : set<C>):()
     requires c != null && c in xs ==> c.u > 0;
     reads xs;
{()}

// reads over itself

class R { var r : R; }

function nope5(r : R):()
  reads if r != null then {r.r} else {};
{()}

function ok5(r : R):()
  reads if r != null then {r, r.r} else {};
{()}

// Reads checking where there are circularities among the expressions

class CircularChecking {
  var Repr: set<object>
    
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
    reads Repr  // error: reads is not self-framing (unless "this in Repr")
    requires this in Repr  // lo and behold!  So, reads clause is fine, if we can assume the precondition

  function H1(cell: Cell): int
    reads this, Repr
    requires cell in Repr
    requires cell != null && cell.data == 10

  function H2(cell: Cell): int
    reads this, Repr
    requires cell != null && cell.data == 10  // this is okay, too, since reads checks are postponed
    requires cell in Repr
}

class Cell { var data: int }
