// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Box<T> {
  constructor() {}
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
  var myBox := new Box();
  var x := GetBoxFn(myBox);
  SetBox(myBox, 42);
}

// TODO: verification times out. Did this already work for functions?
method ApplyLambda<T, R>(f: T ~> R, t: T) returns (r: R) 
  requires f.requires(t)
  reads f.reads
{
  r := f(t);
}

datatype Option<T> = Some(value: T) | None

class {:extern} ExternalMutableMap<K, V> {
  method {:extern} Put(k: K, v: V) 
  method {:extern} Get(k: V) returns (v: Option<V>)
}

method MemoizedSquare(x: int, cache: ExternalMutableMap<int, int>) returns (xSquared: int)
  reads {}
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

method MetaBox(b: Box<Box<int>>)
  reads {}
  modifies b.x  // BUG: should be error because b.x reads b
{
  b.x.x := 42; // BUG: should be error because b.x.x reads b, but reads checks must not look at LHS's
}

function Foo(b: Box<Box<int>>): int
  reads b, b.x
{
  b.x.x
}

trait T {
  method M(b: Box<int>)
}

class C extends T {
  method M(b: Box<int>) 
    modifies b
  {
    b.x := 42;
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

method DefaultValueReads(b: Box<int>, x: int := b.x) returns (r: int)
  reads {}
{
  return 42;
}

// TODO:
// * stress test well-formedness of reads clauses (e.g. when depending on method preconditions)
//   * Also need to apply reads clauses to all other clauses, and default values
// * Double check refinement
// * Double check extending traits
// * {:concurrent} (probably separate test file)
// * Review reads checks for AST elements missed because they don't occur in expressions
// * Optimize checking for `reads {}`? Can be checked with a simple AST pass, much cheaper
//   * At least some cases might be handled by existing IsAlwaysTrue
// * Double-check if it's correct that function default values don't assume preconditions
