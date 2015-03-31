// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M()
  modifies set o: object | true  // allowed, since comprehension is in ghost context
{
}

method N()
  requires null in set o: object | true  // (X) allowed, since comprehension is in ghost context
  ensures null in set o: object | true  // (X) allowed, since comprehension is in ghost context
  decreases set o: object | true  // (X) allowed, since comprehension is in ghost context
{
  N();
}

method O() returns (ghost p: set<object>)
{
  assert null in set o: object | true;  // (X) allowed -- in a ghost context
  p := set o: object | true;  // (X) allowed -- in a ghost context
}

method P() returns (p: set<object>)
{
  p := set o: object | true;  // not allowed -- not in a ghost context
}

ghost method Q() returns (p: set<object>)
{
  p := set o: object | true;  // allowed, since the whole method is ghost
}

function F(): int
  requires null in set o: object | true  // allowed
  ensures null in set o: object | true  // allowed
  reads set o: object | true  // allowed
  decreases set o: object | true  // allowed
{
  if null in set o: object | true then  // allowed -- in a ghost context
    F()
  else
    0
}

function method G(): int
  requires null in set o: object | true  // (X) allowed
  ensures null in set o: object | true  // (X) allowed
  reads set o: object | true  // allowed
  decreases set o: object | true  // (X) allowed
{
  if null in set o: object | true then  // not allowed, since this is not a ghost context
    G()
  else
    0
}
