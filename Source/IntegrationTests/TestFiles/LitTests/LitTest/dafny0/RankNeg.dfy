// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


// Negative tests

// Not well-founded mutual recursions.

ghost function seq_loop_i(xs: seq<int>): int
{
  if (xs == [1, 2]) then seq_loop_s([[1,2]])
  else 0
}
ghost function seq_loop_s(xs: seq<seq<int>>): int
{
  if (xs == [[1, 2]]) then seq_loop_i([1,2])
  else 0
}

datatype wrap = X | WS(ds: seq<wrap>)
ghost function wrap_loop_1(xs: seq<wrap>): int
{
  if (xs == [WS([X,X])]) then wrap_loop_2(WS([X,X]))
  else 0
}
ghost function wrap_loop_2(xs: wrap): int
{
  if (xs == WS([X,X])) then wrap_loop_3([X,X])
  else 0
}
ghost function wrap_loop_3(xs: seq<wrap>): int
{
  if (xs == [X,X]) then wrap_loop_1([WS([X,X])])
  else 0
}
