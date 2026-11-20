// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The elements of a map built by a map comprehension used to be specified outside the
// map's domain too. Two comprehensions over the same empty domain are equal maps, which
// made their value expressions, 1 and 2, equal everywhere, and so proved false.

lemma Bad(k: int, s: set<int>)
  requires s == {}
  ensures false // error: (but this was once provable, due to a bug)
{
  var m1 := map x: int | x in s :: 1;
  var m2 := map x: int | x in s :: 2;
  assert m1 == m2;
  var e := if k in m1 then m1[k] else 1;
}

lemma Contradiction()
  ensures false
{
  Bad(0, {});
}
