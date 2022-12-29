// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// It would be great if Dafny would use a/b as a possible witness when trying to
// establish the existential in M.

method M(a: int, b: int) {
  var s :| b != 0 ==> s == a / b;  // WISH
  assert P(a, b, s);
}

method M_assert_exists(a: int, b: int) {
  assert exists s :: (b != 0 ==> s == a / b && Q(s));  // WISH
}

method N(a: int, b: int)
  requires b != 0
{
  var s :| s == a / b;  // see, this already works
  assert P(a, b, s);
}

predicate P(a: int, b: int, s: int)
{
  b != 0 ==> s == a / b
}

predicate Q(s: int)
{
  true
}
