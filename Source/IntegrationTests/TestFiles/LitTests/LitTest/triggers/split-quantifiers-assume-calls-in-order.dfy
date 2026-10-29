// RUN: %exits-with 4 %verify --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The trigger generator joins the first and the last conjunct of each quantifier, which get the same triggers, into a
// part before the middle one, which guards the call Bad(n) in the last one

ghost predicate P(x: int) { x == 5 }
ghost predicate Q(x: int) { true }
ghost predicate R(x: int, y: int) { true }

// Without its precondition, the definition gives false
ghost function Bad(n: int): int
  requires n > 0
{
  if n <= 0 then Bad(n) + 1 else 0
}

ghost predicate G(n: int) {
  forall x :: P(x) ==> (n > 0 ==> R(x, Bad(n))) && (if Q(x) && Q(x + 1) then n > 0 else n > 0) && R(x, Bad(n))
}

lemma Forall()
  ensures false // error: postcondition might not hold
{
  assert P(5);
  var g := G(0);
}

lemma Exists()
  ensures false // error: postcondition might not hold
{
  var n := 0;
  assert P(5);
  if exists x :: (if P(x) then n > 0 && !R(x, Bad(n)) else true) || (if Q(x) && Q(x + 1) then n <= 0 else n <= 0) || (P(x) && R(x, Bad(n))) {
  }
}
