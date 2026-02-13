// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


// It would be great if Dafny would use a/b as a possible witness when trying to
// establish the existential in M.

method M(a: int, b: int) {
  var s :| b != 0 ==> s == a / b;  // PREVIOUS WISH: wish granted in PR 6023, which distributes the "b != 0 ==>" to outside the existential
  assert P(a, b, s);
}

method M_assert_exists(a: int, b: int) {
  assert exists s :: (b != 0 ==> s == a / b && Q(s));  // WISH (the same distribution is not applied to existentials in general)
}

method N(a: int, b: int)
  requires b != 0
{
  var s :| s == a / b;  // see, this already works
  assert P(a, b, s);
}

ghost predicate P(a: int, b: int, s: int)
{
  b != 0 ==> s == a / b
}

ghost predicate Q(s: int)
{
  true
}
