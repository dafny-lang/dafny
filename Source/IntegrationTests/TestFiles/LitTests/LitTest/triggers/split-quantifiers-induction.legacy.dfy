// RUN: %exits-with 4 %dafny /compile:0 /induction:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List = Nil | Cons(head: int, tail: List)

function Len(l: List): nat {
  match l
  case Nil => 0
  case Cons(_, t) => 1 + Len(t)
}

function F(l: List): int

// The verifier inducts on l for the first part, which calls Len on it, but not for the second
lemma L() {
  assert forall l: List :: Len(l) >= 0 && F(l) <= F(Cons(0, l)); // error: the second part does not hold
}
