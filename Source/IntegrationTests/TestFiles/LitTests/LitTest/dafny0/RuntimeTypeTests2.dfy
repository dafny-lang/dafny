// RUN: %exits-with 3 %run "%s" --target cs > "%t"
// RUN: %diff "%s.expect" "%t"

// The errors in this file are produced by the compiler

predicate ItWasReal(r: real)
{
  r == 44.1985
}

method AssignSuchThat() returns (a: int, b: real)
{
  a :| a % 5 == 0 && a % 7 == 0;
  assert ItWasReal(44.1985);
  b :| ItWasReal(b);  // error: compile doesn't know how to compile this, even though the verifier can check there's a value
}

method LetSuchThat() returns (x: int, y: real)
{
  x := var a :| a % 5 == 0 && a % 7 == 0 && 0 <= a && a < 30; a;
  assert ItWasReal(44.1985);
  y := var b :| ItWasReal(b); b;  // error: compile doesn't know how to compile this, even though the verifier can check there's a value
}
