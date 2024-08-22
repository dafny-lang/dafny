// RUN: %verify --allow-axioms "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node { }

ghost predicate Q(x: Node)
ghost predicate P(x: Node)

method AuxMethod(y: Node)
  modifies y

method MainMethod(y: Node)
  modifies y
{
  AuxMethod(y);  // remove this call and the assertion below goes through (as it should)

  forall x: Node | Q(x)
    ensures P(x)
  {
    assume false;
  }
  // The following assertion should be a direct consequence of the forall statement above
  assert forall x: Node :: Q(x) ==> P(x);
}
