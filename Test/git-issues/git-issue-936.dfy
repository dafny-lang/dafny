// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Status = Failure(msg: string) | Success
{
  function method IsFailure(): bool { Failure? }
  function method PropagateFailure(): Status { this }
}

method q(i: int) returns (r: Status)
  ensures i == 1 ==> !r.Failure?
  ensures i == 2 ==> r.Failure?
{
  if i == 2 {
    return Failure("Z");
  }
  return Success;
}

method m() returns (z: int)
  ensures z == 42
{
  z := 0;
  :- assert q(1);
  return 42;
}

method mbad() {
  :- assert q(0); // error: assert does not necessarily hold
}

method n() {
  :- assume q(2);
  assert false;  // does not fail
}

method n2() returns (z: int)
  ensures z == 42
{
  z := 0;
  :- assume q(0);
  z := 42;
}

method p() {
  :- expect q(2);
  assert false;  // does not fail
}

method p2() returns (z: int)
  ensures z == 42
{
  z := 0;
  :- expect q(0);
  z := 42;
}

method t() returns (r: Status, z: int)
  ensures r.Failure? ==> z == 0
  ensures !r.Failure? ==> z == 42
{
  r := Success;
  z := 0;
  :- q(0);
  z := 42;
}

method t2() returns (r: Status, z: int)
  ensures !r.Failure?
  ensures z == 42
{
  r := Success;
  z := 0;
  :- q(1);
  z := 42;
}

method t3() returns (r: Status, z: int)
  ensures r.Failure?
  ensures z == 0;
{
  r := Success;
  z := 0;
  :- q(2);
  z := 42;
}

