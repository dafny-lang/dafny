// RUN: %exits-with 4 %dafny /compile:0 /readsClausesOnMethods:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The first half of this file is a clone of Reads.dfy, 
// but modified to use methods instead of functions wherever possible,
// to provide more testing coverage of the newer feature
// of allowing and enforcing reads clauses on methods as well.

// Checking that the reads clause also is checked over requires

class C { var u : int }

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
     reads xs
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
  // BUG: f.reads(10) is flagged for some reason. 
  // The wellformedness checks for LetSuchThat may be subtley different than AssignSuchThat...
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

class Box<T> {
  var x: T

  constructor(x: T)
    reads {}
  {
    this.x := x;
  }
}

method SetBox(b: Box<int>, i: int) 
  reads b
  modifies b
{
  b.x := i;
}

function GetBoxFn(b: Box<int>): int
  reads b
{
  b.x
}

method GetBoxCorrectReads(b: Box<int>) returns (i: int)
  reads b
{
  i := b.x;
}

method GetBoxReadsStar(b: Box<int>) returns (i: int)
  reads *
{
  i := b.x;
}

method GetBoxIncorrectReads(b: Box<int>) returns (i: int)
  reads {}
{
  i := b.x; // Error: insufficient reads clause to read field
}

method GetBoxDefaultReads(b: Box<int>) returns (i: int)
{
  i := b.x;
}

method ReadingAndWritingFreshStateAllowed()
  reads {}
{
  var myBox := new Box(42);
  var x := GetBoxFn(myBox);
  SetBox(myBox, 42);
}

method ApplyLambda<T(!new), R>(f: T ~> R, t: T) returns (r: R) 
  requires f.requires(t)
  reads f.reads
{
  r := f(t);
}

// method DependsOnAllocationState<T>(b: Box<T>) 
//   reads set t: T :: b // BUG? This isn't allowed on functions...
// {
// }

datatype Option<T> = Some(value: T) | None

class {:extern} ExternalSequentialMutableMap<K, V> {
  ghost var state: map<K, V>
  method {:extern} Put(k: K, v: V)
    requires k !in state
    modifies this
    ensures state == old(state)[k := v]
  function {:extern} Get(k: K): (v: Option<V>)
    reads this
    ensures k in state ==> v == Some(state[k])
    ensures k !in state ==> v == None
}

method {:concurrent} MemoizedSquare2(x: int, cache: ExternalSequentialMutableMap<int, int>) returns (xSquared: int)
  requires forall k | k in cache.state :: cache.state[k] == k * k   // Error: insufficient reads clause to read field
  reads {}
  ensures xSquared == x * x
{
  var cached := cache.Get(x);  // Error: insufficient reads clause to invoke function
  if cached.Some? {
    xSquared := cached.value;
  } else {
    xSquared := x * x;
    cache.Put(x, xSquared);    // Error: call might violate context's modifies clause
                               // Error: insufficient reads clause to call
  }
}

class {:extern} ExternalConcurrentMutableMap<K, V> {
  const inv: (K, V) -> bool
  method {:extern} Put(k: K, v: V)
    reads {}
    requires inv(k, v)
  method {:extern} Get(k: K) returns (v: Option<V>)
    reads {}
    ensures v.Some? ==> inv(k, v.value)
}

method {:concurrent} MemoizedSquare(x: int, cache: ExternalConcurrentMutableMap<int, int>) returns (xSquared: int)
  requires cache.inv == ((key, value) => value == key * key)
  reads {}
  ensures xSquared == x * x
{
  var cached := cache.Get(x);
  if cached.Some? {
    xSquared := cached.value;
  } else {
    xSquared := x * x;
    cache.Put(x, xSquared);
  }
}

function Always42(b: Box<int>): int {
  42
} by method {
  var result := 42;
  result := result + b.x; // Error: insufficient reads clause to read field
  result := result - b.x;
  return 42;
}

method BadMetaBox(b: Box<Box<int>>)
  reads {}
  modifies b.x  // Error: insufficient reads clause to read field
{
  b.x.x := 42;  // Error: insufficient reads clause to read field
}

method GoodMetaBox(b: Box<Box<int>>)
  modifies b.x
{
  b.x.x := 42;
}

function GoodMetaBox2(b: Box<Box<int>>): int
  reads b, b.x
{
  b.x.x
}

trait MyTrait {
  method M(b: Box<int>) returns (r: int)
    reads {}
}

class MyClass extends MyTrait {
  method M(b: Box<int>) returns (r: int) // Error: method might read an object not in the parent trait context's reads clause
    reads b
  {
    return 42;
  }
}

// Testing the reads checks on other clauses
method OnlySpecReads(b: Box<int>) returns (r: int)
  requires b.x == 42  // Error: insufficient reads clause to read field
  reads {}
  ensures r == b.x
{
  return 42;
}

method DefaultValueReads(b: Box<int>, x: int := b.x)  // Error: insufficient reads clause to read field
  returns (r: int)
  reads {}
{
  return 42;
}

// TODO:
// * Array reads!
// * Ensuring LHS' aren't checked as reads (LValueContext) - this.x working, array setting not working
//   * Lots of cases!
// * Invoking twostate things from methods
// * Example for the need to add fresh loop invariants in functions by methods?
// * Double check refinement
// * Missing check for reads clause not allowed to depend on set of allocated objects (?)
// * Double-check if it's correct that function default values don't assume preconditions (see example below)
// * Document explicit choice not to change autocontracts (?)
// * Figure out FunctionInQuantifier2 method
//   * Something to do with difference between AssignSuchThat and LetSuchThat?
//   * Possibly just leave and ask in PR review

// FUTURE:
// * Optimize checking for `reads {}`? Can be checked with a simple AST pass, much cheaper
//   * At least some cases might be handled by existing IsAlwaysTrue
// * Document explicit choice not to include method reads clause in decreases clause


function Partition(s: seq<int>, p: int -> bool, a: array<int>): (seq<int>, seq<int>) {
  ([], [])
} by method {
  var b := new int[10];
  var loop := true;
  while loop
    decreases loop
  {
    b[0] := 42;
    loop := false;
  }
  b[0] := 42;
  return ([], []);
}

// function DefaultValue(b: int, v: int := 1 / b): int 
//   requires b != 0
// {
//   42
// }