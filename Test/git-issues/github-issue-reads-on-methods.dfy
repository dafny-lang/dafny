// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

method DependsOnAllocationState<T>(b: Box<T>) 
  reads set t: T :: b // BUG? This isn't allowed on functions...
{
}

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

trait T {
  method M(b: Box<int>) returns (r: int)
    reads {}
}

class C extends T {
  method M(b: Box<int>) returns (r: int) // Error: method might read an object not in the parent trait context's reads clause
    reads b
  {
    return 42;
  }
}

class Concurrent {

  function {:concurrent} GoodFn(b: Box<int>): int {
    42
  }

  function {:concurrent} BadFn(b: Box<int>): int  // Error: reads clause might not be empty ({:concurrent} restriction)
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

  method {:concurrent} BadM(b: Box<int>)  // Error: reads clause might not be empty ({:concurrent} restriction)
    reads b
  {
    var x := b.x;
  }

  method {:concurrent} WeirdButOkayM(b: Box<int>) 
    reads if false then {b} else {}
  {
  }

  method {:concurrent} AlsoBadM(b: Box<int>)  // Error: modifies clause might not be empty ({:concurrent} restriction)
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
// * Add CLI option!
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

const f := (b: Box<T>) reads b => b.x


lemma Dorp(b: Box<T>) {
  assert b.x == b.x;
}

// function DefaultValue(b: int, v: int := 1 / b): int 
//   requires b != 0
// {
//   42
// }