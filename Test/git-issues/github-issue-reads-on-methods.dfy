// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Box {
  constructor() {}
  var x: int
}

method SetBox(b: Box, i: int) 
  modifies b
{
  b.x := i;
}

function GetBoxFn(b: Box): int
  reads b
{
  b.x
}

method GetBoxCorrectReads(b: Box) returns (i: int)
  reads b
{
  i := b.x;
}

method GetBoxReadsStar(b: Box) returns (i: int)
  reads *
{
  i := b.x;
}

method GetBoxIncorrectReads(b: Box) returns (i: int)
  reads {}
{
  i := b.x; // Error: insufficient reads clause to read field
}

method GetBoxDefaultReads(b: Box) returns (i: int)
{
  i := b.x; // Bug: getting an error here too, likely because we're not correctly defaulting to reads *
}

method ReadingAndWritingFreshStateAllowed()
  reads {}
{
  var myBox := new Box();
  var x := GetBoxFn(myBox);
  SetBox(myBox, 42);
}

// 

datatype Option<T> = Some(value: T) | None

class {:extern} ExternalMutableMap<K, V> {
  // TODO: having ghost state should cause frame violations
  ghost var state: map<K, V>
  method {:extern} Put(k: K, v: V) ensures state == old(state)[k := v]
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

function Always42(b: Box): int {
  42
} by method {
  var result := 42;
  result := result + b.x; // Error: insufficient reads clause to read field
  result := result - b.x;
  return 42;
}

// TODO:
// * stress test well-formedness of reads clauses (e.g. when depending on method preconditions)
// * Double check refinement
