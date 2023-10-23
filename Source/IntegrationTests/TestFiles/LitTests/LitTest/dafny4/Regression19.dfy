// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate ContainsNothingBut5(s: set<int>)
{
  forall q :: q in s ==> q == 5
}

ghost predicate YeahContains5(s: set<int>)
{
  exists q :: q in s && q == 5
}

ghost predicate ViaSetComprehension(s: set<int>) {
  |set q | q in s && q == 5| != 0
}

ghost predicate LambdaTest(s: set<int>) {
  (q => q in s)(5)
}

ghost predicate ViaMapComprehension(s: set<int>) {
  |(map q | q in s && q == 5 :: true).Keys| != 0
}

ghost predicate Contains5(s: set<int>)
{
  var q := 5; q in s
}

datatype R = MakeR(int) | Other

ghost predicate RIs5(r: R) {
  match r case MakeR(q) => q == 5 case Other => false
}

lemma NonemptySet(x: int, s: set<int>)
  requires x in s
  ensures |s| != 0
{
}
lemma NonemptyMap(x: int, s: map<int,bool>)
  requires x in s.Keys
  ensures |s| != 0
{
}

method M(s: set<int>, r: R, q: int)
  requires s == {5} && r == MakeR(5)
{
  assert ContainsNothingBut5(s);  // forall
  assert YeahContains5(s);  // exists

  NonemptySet(5, set q | q in s && q == 5);
  assert ViaSetComprehension(s);  // set comprehension

  NonemptyMap(5, map q | q in s && q == 5 :: true);
  assert ViaMapComprehension(s);  // map comprehension

  assert LambdaTest(s);  // lambda expression
  assert Contains5(s);  // let expression (once had generated malformed Boogie)

  assert RIs5(r);  // match expression
}
