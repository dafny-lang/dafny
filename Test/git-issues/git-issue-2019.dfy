// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method f(x: seq<int>) returns (res: seq<int>)
  ensures x == res
{
  var y := [];
  for i := 0 to |x|
    invariant |y| == i
    invariant x[..i] == y[..i]
  {
    y := y + [x[i]];
  }
  return y;
}

function f(x: seq<int>): seq<int> {
  x
} by method {
  var y := [];
  for i := 0 to |x|
    invariant |y| == i
    invariant x[..i] == y[..i]
  {
    y := y + [x[i]];
  }
  return y;
}
