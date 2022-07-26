lemma Foo<T>(s: seq<T>, p: seq<T> -> bool)
  requires p(s[..|s|])
  ensures p(s)
{
//  assert s[..|s|] == s;
}
