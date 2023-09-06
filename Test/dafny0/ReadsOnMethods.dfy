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
  requires forall x :: x in S ==> f.requires(x) && f.reads(x) == {}
  reads {}
{
  if S == {} {
    return {};
  } else {
    var x :| x in S;
    var r' := ApplyToSet(S - {x}, f);
    r := r' + {f(x)};
  }
}

ghost method ApplyToSet_AltSignature0<X>(S: set<X>, f: X ~> X) returns (r: set<X>)
  requires forall x :: x in S ==> f.requires(x) && f.reads(x) == {}
  reads {}

ghost method ApplyToSet_AltSignature1<X>(S: set<X>, f: X ~> X) returns (r: set<X>)
  requires forall x :: x in S ==> f.requires(x)
  requires forall x :: x in S ==> f.reads(x) == {}
  reads {}

ghost method ApplyToSet_AltSignature2<X>(S: set<X>, f: X ~> X) returns (r: set<X>)
  requires (forall x :: x in S ==> f.requires(x) && f.reads(x) == {}) ==> forall x :: x in S ==> f.requires(x)
  // (this precondition would not be good enough to check the body above)
  reads {}

ghost method FunctionInQuantifier0() returns (r: int)
  requires exists f: int ~> int :: f(10) == 100  // error (x2): precondition violation and insufficient reads
  reads {}

ghost method FunctionInQuantifier1() returns (r: int)
  requires exists f: int ~> int :: f.requires(10) && f(10) == 100  // error: insufficient reads
  reads {}

ghost method FunctionInQuantifier2() returns (r: int)
  requires exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100
  reads {}
  ensures r == 100
{
  // Unlike the ghost function version, f.reads(10) is flagged because we aren't delaying reads checks on method bodies.
  // It's still an open question whether we should be though: https://github.com/dafny-lang/dafny/issues/4489.
  // For now this is at least only a completeness issue.
  var f: int ~> int :| f.requires(10) && f.reads(10) == {} && f(10) == 100;  // error: insufficient reads
  return f(10);
}

class DynamicFramesIdiom {
  ghost var Repr: set<object>
  ghost method IllFormed_Valid() returns (r: bool)
    reads Repr  // error: reads is not self framing (notice the absence of "this")
    ensures r == (this in Repr)
  {
    return this in Repr;  // the post-condition says that the method returns true if "this in Repr", but the
                          // method can also be invoked in a state where its body will evaluate to false
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

// ---------- Basic use cases -----------

class Box<T> {
  var x: T

  constructor(x: T)
    reads {}
  {
    this.x := x;
  }
}

method SetBox(b: Box<int>, i: int) 
  modifies b
  reads {}
{
  b.x := i;
}

method SetBoxSpecific(b: Box<int>, i: int) 
  modifies b`x
  reads {}
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

method GetBoxCorrectReadsSpecific(b: Box<int>) returns (i: int)
  reads b`x
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

// ---------- More complicated reads clauses -----------

method ApplyLambda<T(!new), R>(f: T ~> R, t: T) returns (r: R) 
  requires f.requires(t)
  reads f.reads(t)
{
  r := f(t);
}

class GhostBox {
  ghost var x: int
  constructor(x: int) {
    this.x := x;
  }
}

// Unlike functions, method frames can refer to the set of allocated objects.
ghost method IncrementAllBoxes() 
  reads set b: GhostBox | true
  modifies set b: GhostBox | true
{
  forall b: GhostBox {
    b.x := b.x + 1;
  }
}

// ---------- Enforcing concurrency safe entry points (examples from the RFC) -----------

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

// ---------- Functions-by-method -----------

function GoodDirectFib(n: nat): nat {
  if n < 2 then n else GoodDirectFib(n - 2) + GoodDirectFib(n - 1)
} by method {
  var x, y := 0, 1;
  for i := 0 to n
    invariant x == GoodDirectFib(i) && y == GoodDirectFib(i + 1)
  {
    x, y := y, x + y;
  }
  return x;
}

function BadFib(n: nat): nat {
  if n < 2 then n else BadFib(n - 2) + BadFib(n - 1)
} by method {
  // Rejected because the default for methods is reads *
  var r := FibMethod(n); // Error: insufficient reads clause to call
  return r;
}

method FibMethod(n: nat) returns (r: nat) 
  ensures r == BadFib(n)
{
  var x, y := 0, 1;
  for i := 0 to n
    invariant x == BadFib(i) && y == BadFib(i + 1)
  {
    x, y := y, x + y;
  }
  return x;
}

function GoodFib(n: nat): nat {
  if n < 2 then n else GoodFib(n - 2) + GoodFib(n - 1)
} by method {
  var r := FibMethodWithReads(n);
  return r;
}

method FibMethodWithReads(n: nat) returns (r: nat) 
  reads {}
  ensures r == GoodFib(n)
{
  var x, y := 0, 1;
  for i := 0 to n
    invariant x == GoodFib(i) && y == GoodFib(i + 1)
  {
    x, y := y, x + y;
  }
  return x;
}

// Example of where applying the function reads clause to the by method body
// catches what would be a concurrency issue.
function WeirdAlways42(b: Box<int>): int {
  42
} by method {
  var result := 42;
  result := result + b.x; // Error: insufficient reads clause to read field
  result := result - b.x;
  return 42;
}

// ---------- Correctly excluding lvalues from reads checks -----------

method BadMetaBox(b: Box<Box<int>>)
  reads {}
  modifies b.x  // Error: insufficient reads clause to read field
{
  b.x.x := 42;  // Error: insufficient reads clause to read field
}

method GoodMetaBox(b: Box<Box<int>>)
  reads b
  modifies b.x
{
  b.x.x := 42;
}

method BadArrayRead(a: array<int>) returns (r: int)
  requires a.Length > 0
  reads {}
{
  return a[0];  // Error: insufficient reads clause to read array element
}

method BadArrayRead2(a: array<int>) returns (r: int)
  requires a.Length > 0
  reads {}
  // Showing that modifies does not imply reads - they are independent clauses
  modifies a
{
  return a[0];  // Error: insufficient reads clause to read array element
}

method GoodArrayRead(a: array<int>) returns (r: int)
  requires a.Length > 0
  reads a
{
  return a[0];
}

method GoodArrayWrite(a: array<int>)
  requires a.Length > 0
  modifies a
{
  a[0] := 42;
}

method GoodArrayWrite2(a: array<int>)
  requires a.Length > 0
  reads {}
  modifies a
{
  a[0] := 42;
}

// ---------- Correct verification between reads clauses (inheritance, calls, etc.) -----------

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

method PretendingNotToRead(b: Box<int>, ghost g: Box<int>) 
  reads {}
{
  var x := VoraciousReader(b);  // Error: insufficient reads clause to call
}
method PretendingNotToRead2(b: Box<int>, ghost g: Box<int>) 
  reads {}
{
  var x := WhatsInTheBox(b);  // Error: insufficient reads clause to call
}
method ActuallyNotReading(b: Box<int>, ghost g: Box<int>) 
  reads {}
{
  var x := NotAReader(b);
}
method PretendingNotToReadButSpooky(b: Box<int>, ghost g: Box<int>) 
  reads {}
{
  var x := TheGhostCanTotallySeeYou(g);  // Error: insufficient reads clause to call
}
method InTwoPlacesAtOnce(b: Box<int>) 
  reads {}
{
  assert Unchanged(b);  // Error: insufficient reads clause to call
}
method StuckInThePast(b: Box<int>) 
  reads {}
{
  // Doesn't verify, but allowed by reads clause
  assert Was42(b);   // Error: assertion might not hold
}

method VoraciousReader(b: Box<int>) returns (r: int) { r := b.x; }
method WhatsInTheBox(b: Box<int>) returns (r: int) reads b { r := b.x; }
method NotAReader(b: Box<int>) returns (r: int) reads {} { r := 42; }
ghost method TheGhostCanTotallySeeYou(b: Box<int>) returns (r: int) reads b { r := b.x; }
twostate predicate Unchanged(b: Box<int>) reads b {
  old(b.x) == b.x
}
twostate predicate Was42(b: Box<int>) {
  old(b.x) == 42
}

// ---------- Restricting other clauses on methods by reads clauses as well -----------

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
  return x;
}
