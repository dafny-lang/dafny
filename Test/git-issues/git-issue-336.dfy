// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma TestMap(a: map<int, (int,int)>) {
  // The following assertion used to not prove automatically
  assert (map k | k in a :: k := a[k].0)
         // the following map comprehension implicitly uses k as the key
      == (map k | k in a :: a[k].0);
}

lemma TestSet0(a: set<int>) {
  assert (set k | k in a && k < 7 :: k)
         // the following set comprehension implicitly uses k as the term
      == (set k | k in a && k < 7);
}

lemma TestSet1(a: set<int>, m: int) {
  assert (set k | k in a && k < 7 :: k)
      == (set k | k in a && k < 7 :: m + (k - m));
}

lemma TestSet2(a: set<int>, m: int)
  requires m in a && m < 7
{
  assert (set k | k < 7 && k in a)
      == (set k | k in a :: if k < 7 then k else m);
}
