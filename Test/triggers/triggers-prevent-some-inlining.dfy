// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This  file looks  at the  interactions  between inlining  and triggers.   The
// sum_is_sum predicate gets a {sum(a,  b)} trigger, which explicitly depends on
// one of the  variables being passed in. Since triggers  are generated prior to
// inlining  (inlining  happens  during  translation),  inlining  the  last  two
// instances of that call below would cause  b+1 (a trigger killer) to pop up in
// a trigger.   This would create  an invalid trigger,  so Dafny doesn't  let it
// happen.

ghost function sum(a: int, b: int): int {
  a + b
}

ghost predicate sum_is_sum(b: int, c: int) {
  forall a: int :: sum(a, b) + c == a + b + c
}

method can_we_inline(b: int, c: int)
  ensures sum_is_sum(0, 0)     // OK  to inline
  ensures sum_is_sum(b, c)     // OK  to inline
  ensures sum_is_sum(b, c+1)   // OK  to inline
  ensures sum_is_sum(b+1, c)   // NOK to inline
  ensures sum_is_sum(b+1, c+1) // NOK to inline
{ }
