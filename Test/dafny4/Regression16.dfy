// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Tree = Leaf | Node(x: int, left: Tree, right: Tree)

function Insert(t: Tree, y: int): Tree
{
  match t
  case Leaf => Node(y, Leaf, Leaf)
  case Node(x, left, right) =>
    if y < x then
      Node(y, Insert(right, x), left)
    else
      Node(x, Insert(right, y), left)
}

ghost function Elements(t: Tree): multiset<int>
{
  match t
  case Leaf =>  multiset {}
  case Node(x, left, right) => multiset {x} + Elements(left) + Elements(right)
}

ghost predicate IsBalanced(t: Tree)
{
  match t
  case Leaf => true
  case Node(_, left, right) =>
    IsBalanced(left) && IsBalanced(right) &&
    var L, R := |Elements(left)|, |Elements(right)|;
    L == R || L == R+1
}

lemma InsertBalanced_A(t: Tree, y: int)
  requires IsBalanced(t)
  ensures var t' := Insert(t, y);
    Elements(
      Insert(t, y)  // Use Insert(t, y) here instead of t'.  This verifies (and did before).
    ) == Elements(t) + multiset {y} &&
    IsBalanced(t')
{
}

lemma InsertBalanced_B(t: Tree, y: int)
  requires IsBalanced(t)
  ensures var t' := Insert(t, y);
    Elements(
      t'  // Use t' here, which stands for Insert(t, y).  This used to not verify (because the
          // fuel of this call to Insert was previously not increments).
    ) == Elements(t) + multiset {y} &&
    IsBalanced(t')  // An effect of the "fixed" implementation is that the fuel of Insert gets
                    // incremented here, too, whereas it did not used to.
{
}
