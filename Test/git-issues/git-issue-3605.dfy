// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


class C { }

method M()
  ensures false
{
  ghost var s, r;
  s := set c: C | True(c);
  label L:
  r := Id(s);

  var c := new C;
  assert c in s; // error: the elements of s were all allocated before label L, and in particular before "c := new C"
  assert c !in r;
}

predicate True(s: C) {
  true
}

ghost method Id(s: set<C>) returns (r: set<C>)
  ensures r == s
{
  r := s;
}
