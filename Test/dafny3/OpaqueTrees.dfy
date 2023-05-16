// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Tree<T> = Leaf(T) | Node(Tree, Tree)

ghost function {:opaque} size(t: Tree): nat
{
  match t
  case Leaf(_) => 1
  case Node(left, right) => 1 + size(left) + size(right)
}

ghost function {:opaque} mirror<T>(t: Tree<T>): Tree<T>
{
  match t
  case Leaf(_) => t
  case Node(left, right) => Node(mirror(right), mirror(left))
}

lemma {:induction false} MirrorSize(t: Tree)
  ensures size(mirror(t)) == size(t);
{
  match t {
    case Leaf(x) =>
      calc {
        size(mirror(Leaf(x)));
      ==  { reveal mirror(); }
        size(Leaf(x));
      }
    case Node(left, right) =>
      calc {
        size(mirror(Node(left, right)));
      ==  { reveal mirror(); }
        size(Node(mirror(right), mirror(left)));
      ==  { reveal size(); }
        1 + size(mirror(right)) + size(mirror(left));
      ==  { MirrorSize(right); MirrorSize(left); }  // induction hypothesis
        1 + size(right) + size(left);
      ==  { reveal size(); }
        size(Node(left, right));
      }
  }
}
