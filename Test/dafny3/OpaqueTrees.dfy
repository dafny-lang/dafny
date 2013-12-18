datatype Tree<T> = Leaf(T) | Node(Tree, Tree)

function {:opaque} size(t: Tree): nat
{
  match t
  case Leaf(_) => 1
  case Node(left, right) => 1 + size(left) + size(right)
}

function {:opaque} mirror(t: Tree): Tree
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
      ==  { reveal_mirror(); }
        size(Leaf(x));
      }
    case Node(left, right) =>
      calc {
        size(mirror(Node(left, right)));
      ==  { reveal_mirror(); }
        size(Node(mirror(right), mirror(left)));
      ==  { reveal_size(); }
        1 + size(mirror(right)) + size(mirror(left));
      ==  { MirrorSize(right); MirrorSize(left); }  // induction hypothesis
        1 + size(right) + size(left);
      ==  { reveal_size(); }
        size(Node(left, right));
      }
  }
}
