// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Max(s: set<int>): (m: int)
  requires s != {}
{
  var x :| x in s;
  if s == {x} then
    x
  else
    var s' := s - {x};
    var y := Max(s');
    y
}

method IncorrectLoop0(m: int)
{
  var r := {m};
  while r != {}
    // Incorrectly generated CanCall assumptions for multiple invariant declarations
    // once caused the error on the next line to be omitted.
    invariant r != {} // error: loop invariant not maintained
    invariant m == Max(r)
  {
    r := r - {m};
  }
}

method IncorrectLoop1(m: int)
{
  var r := {m};
  while r != {}
    invariant r != {} && m == Max(r) // error: loop invariant not maintained
  {
    r := r - {m};
  }
}
