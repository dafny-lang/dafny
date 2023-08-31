// RUN: %exits-with 4 %dafny /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Once upon a time, the type parameter in the following line had caused
// malformed Boogie to be generated.
type EvenSet<A> = s: set<A> | |s| == 0 || |s| % 2 == 0

method Main()
{
  var s: EvenSet := {36,24,36};  // this set only has 2 numbers, so it's okay
  var t: EvenSet := {12};  // error: value does not satisfy subset-type constraint
}
