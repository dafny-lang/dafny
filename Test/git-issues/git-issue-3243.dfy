// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method LoopWithBody(x: int)
  decreases *
{
  var i := 0;
  while i < x
    // The following loop-invariant-on-entry check was once omitted when it was the only proof obligation.
    invariant i <= x // error: loop invariant does not hold on entry
    decreases *
  {
  }
}

method BodylessLoop(x: int)
{
  var i := 0;
  while i < x
    // The following loop-invariant-on-entry check was once omitted when it was the only proof obligation.
    invariant i <= x // error: loop invariant does not hold on entry
}
