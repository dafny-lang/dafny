// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Check that using the reveal_ lemma to prove the well-definedness of a function
// in a lower SCC does not cause a soundness problem

function A(): int
  ensures A() == 5; // error: this result value is not what the postcondition specification says
{
  reveal_B();  // This isn't a decreases failure, since reveal just adjusts fuel values; it doesn't mention B
  6
}

function {:opaque} B(): int
  ensures B() == 5;
{
  A()
}

