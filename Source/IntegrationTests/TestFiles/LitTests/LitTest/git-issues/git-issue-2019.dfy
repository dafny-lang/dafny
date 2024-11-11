// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


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
