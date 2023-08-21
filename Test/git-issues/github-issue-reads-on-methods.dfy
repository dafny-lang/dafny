// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Box<T> {
  constructor(x: T) {
    this.x := x;
  }
  var x: T
}

method SetBox(b: Box<int>, i: int) 
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
  reads f.reads  // BUG: Insufficient reads clause to read function
{
  r := f(t);
}

method DependsOnAllocationState<T>(b: Box<T>) 
  reads set t: T :: b // BUG? Not allowed for function...
{
}

datatype Option<T> = Some(value: T) | None

class {:extern} ExternalSequentialMutableMap<K, V> {
  ghost var state: map<K, V>
  method {:extern} Put(k: K, v: V)
    requires k !in state
    modifies this
    ensures state == old(state)[k := v]
  method {:extern} Get(k: K) returns (v: Option<V>)
    ensures k in state ==> v == Some(state[k])
    ensures k !in state ==> v == None
}

method {:concurrent} MemoizedSquare2(x: int, cache: ExternalSequentialMutableMap<int, int>) returns (xSquared: int)
  requires forall k | k in cache.state :: cache.state[k] == k * k
  reads {}
  ensures xSquared == x * x
{
  var cached := cache.Get(x); // Bug: Not catching invalid read here
  if cached.Some? {
    xSquared := cached.value;
  } else {
    xSquared := x * x;
    cache.Put(x, xSquared);
  }
}

class {:extern} ExternalConcurrentMutableMap<K, V> {
  const inv: (K, V) -> bool
  method {:extern} Put(k: K, v: V)
    requires inv(k, v)
  method {:extern} Get(k: K) returns (v: Option<V>)
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
  modifies b.x
{
  b.x.x := 42;
}

method GoodMetaBox(b: Box<Box<int>>)
  modifies b.x
{
  b.x.x := 42;
}

function Foo(b: Box<Box<int>>): int
  reads b, b.x
{
  b.x.x
}

trait T {
  method M(b: Box<int>) returns (r: int)
}

class C extends T {
  method M(b: Box<int>) returns (r: int) 
    reads b // BUG
  {
    return 42;
  }
}

class Concurrent {

  function {:concurrent} GoodFn(b: Box<int>): int {
    42
  }

  function {:concurrent} BadFn(b: Box<int>): int 
    reads b
  {
    b.x
  }

  function {:concurrent} WeirdButOkayFn(b: Box<int>): int 
    reads if false then {b} else {}
  {
    42
  }

  method {:concurrent} GoodM(b: Box<int>) {
  }

  method {:concurrent} BadM(b: Box<int>) 
    reads b
  {
    var x := b.x;
  }

  method {:concurrent} WeirdButOkayM(b: Box<int>) 
    reads if false then {b} else {}
  {
  }

  method {:concurrent} AlsoBadM(b: Box<int>) 
    modifies b
  {
    b.x := 42;
  }

  method {:concurrent} AlsoWeirdButOkayM(b: Box<int>) 
    modifies if false then {b} else {}
  {
  }
}

// Testing the reads checks on other clauses
method OnlySpecReads(b: Box<int>) returns (r: int)
  requires b.x == 42
  reads {}
  ensures r == b.x
{
  return 42;
}

method DefaultValueReads(b: Box<int>, x: int := b.x)
  returns (r: int)
  reads {}
{
  return 42;
}

// TODO:
// * stress test well-formedness of reads clauses (e.g. when depending on method preconditions)
//   * Also need to apply reads clauses to all other clauses, and default values
// * Double check refinement
// * Extending traits subframe check
// * Method call subframe check
// * Explicitly test against ghost state too
//   * ghost methods/lemmas as well
// * {:concurrent} (probably separate test file)
// * Optimize checking for `reads {}`? Can be checked with a simple AST pass, much cheaper
//   * At least some cases might be handled by existing IsAlwaysTrue
// * Double-check if it's correct that function default values don't assume preconditions
// * Missing check for reads clause not allowed to depend on set of allocated objects
// * Document explicit choice not to include method reads clause in decreases clause (backwards compatibility)
// * Document explicit choice not to change autocontracts (?)
