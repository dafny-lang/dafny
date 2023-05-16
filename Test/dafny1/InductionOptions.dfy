// RUN: %exits-with 4 %dafny /compile:0 /induction:0 "%s" > "%t"
// RUN: %exits-with 4 %baredafny verify %args --manual-lemma-induction "%s" >> "%t"
// RUN: %exits-with 4 %dafny /compile:0 /induction:2 "%s" >> "%t"
// RUN: %dafny /compile:0 /induction:3 "%s" >> "%t"
// RUN: %exits-with 4 %dafny /compile:0 /induction:4 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// This file tests the various /induction options

datatype List = Nil | Cons(int, List)

ghost function Append(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, Append(tail, ys))
}

lemma LemmaOnly(xs: List)
  ensures Append(xs, Nil) == xs
{  // error with /induction:0,1,2
}

method QuantifierOnly() {
  assert forall xs :: Append(xs, Nil) == xs;  // error with /induction:0,1,4
}

lemma LemmaPostcondition()
  ensures forall xs :: Append(xs, Nil) == xs
{  // error with /induction:0,1,4
}

lemma AssertInLemma()
{
  assert forall xs :: Append(xs, Nil) == xs;  // error with /induction:0,1,4
}

lemma {:induction} AttributeOnLemma(xs: List)
  ensures Append(xs, Nil) == xs
{  // error with /induction:0
}

method AttributeOnQuantifier() {
  assert forall xs {:induction} :: Append(xs, Nil) == xs;  // error with /induction:0
}
