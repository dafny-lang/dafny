// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A forall statement's call permissions used to be granted even when its bound variable
// ranges over a type that may be empty. Here that let Candidate call Never, whose
// precondition is false, and so prove false.

type Empty = x: int | false witness *

function Never(): bool
  requires false
  ensures false
{ false }

lemma Candidate()
  ensures false
{
  forall x: Empty
    ensures Never()
  { }
  assert Never(); // error: (but this was once provable, due to a bug)
}

// The same over a type that is not empty was, and still is, refused.
type NonEmpty = x: int | x == 0 witness 0

lemma Control()
  ensures false
{
  forall x: NonEmpty
    ensures Never() // error: function precondition
  { }
  assert Never();
}
