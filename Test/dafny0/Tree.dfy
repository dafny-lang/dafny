// ------------------ generic list, non-generic tree

datatype List<T> {
  Nil;
  Cons(T, List<T>);
}

datatype Tree {
  Node(int, List<Tree>);
}

static function Inc(t: Tree): Tree
  decreases t;
{
  match t
  case Node(n, children) => #Tree.Node(n+1, ForestInc(children))
}

static function ForestInc(forest: List<Tree>): List<Tree>
  decreases forest;
{
  match forest
  case Nil => forest
  case Cons(tree, tail) => #List.Cons(Inc(tree), ForestInc(tail))
}

// ------------------ generic list, generic tree (but GInc defined only for GTree<int>

datatype GTree<T> {
  Node(T, List<GTree<T>>);
}

static function GInc(t: GTree<int>): GTree<int>
  decreases t;
{
  match t
  case Node(n, children) => #GTree.Node(n+1, GForestInc(children))
}

static function GForestInc(forest: List<GTree<int>>): List<GTree<int>>
  decreases forest;
{
  match forest
  case Nil => forest
  case Cons(tree, tail) => #List.Cons(GInc(tree), GForestInc(tail))
}

// ------------------ non-generic structures

datatype TreeList {
  Nil;
  Cons(OneTree, TreeList);
}

datatype OneTree {
  Node(int, TreeList);
}

static function XInc(t: OneTree): OneTree
  decreases t;
{
  match t
  case Node(n, children) => #OneTree.Node(n+1, XForestInc(children))
}

static function XForestInc(forest: TreeList): TreeList
  decreases forest;
{
  match forest
  case Nil => forest
  case Cons(tree, tail) => #TreeList.Cons(XInc(tree), XForestInc(tail))
}
