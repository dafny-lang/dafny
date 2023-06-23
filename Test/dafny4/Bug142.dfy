// RUN: %dafny /warnShadowing  /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function P(x:int):int
ghost function Q(x:int):int
ghost function R(x:int):int

ghost function Example0(y:int) : int
{
  var state0 := y;
  var state0 := P(state0);
  var state0 := Q(state0);
  var state0 := R(state0);
  state0
}


ghost function {:warnShadowing false} Example(y:int) : int
{
  var state := y;
  var state := P(state);
  var state := Q(state);
  var state := R(state);
  state
}

ghost function Example2(y:int) : int
{
  var state1 := y;
  var state1 := P(state1);
  var state1 := Q(state1);
  var state1 := R(state1);
  state1
}
