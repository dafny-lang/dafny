// RUN: %baredafny verify %args --warn-shadowing "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function P(x:int):int
function Q(x:int):int
function R(x:int):int

function Example0(y:int) : int
{
  var state0 := y;
  var state0 := P(state0);
  var state0 := Q(state0);
  var state0 := R(state0);
  state0
}


function {:warnShadowing false} Example(y:int) : int
{
  var state := y;
  var state := P(state);
  var state := Q(state);
  var state := R(state);
  state
}

function Example2(y:int) : int
{
  var state1 := y;
  var state1 := P(state1);
  var state1 := Q(state1);
  var state1 := R(state1);
  state1
}
