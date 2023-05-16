// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ------------------ generic list, non-generic tree

datatype List<T> = Nil | Cons(T, List<T>)

datatype Tree = Node(int, List<Tree>)

ghost function Inc(t: Tree): Tree
{
  match t
  case Node(n, children) => Tree.Node(n+1, ForestInc(children))
}

ghost function ForestInc(forest: List<Tree>): List<Tree>
{
  match forest
  case Nil => forest
  case Cons(tree, tail) => List.Cons(Inc(tree), ForestInc(tail))
}

// ------------------ generic list, generic tree (but GInc defined only for GTree<int>

datatype GTree<T> = Node(T, List<GTree<T>>)

ghost function GInc(t: GTree<int>): GTree<int>
{
  match t
  case Node(n, children) => GTree.Node(n+1, GForestInc(children))
}

ghost function GForestInc(forest: List<GTree<int>>): List<GTree<int>>
{
  match forest
  case Nil => forest
  case Cons(tree, tail) => List.Cons(GInc(tree), GForestInc(tail))
}

// ------------------ non-generic structures

datatype TreeList = Nil | Cons(OneTree, TreeList)

datatype OneTree = Node(int, TreeList)

ghost function XInc(t: OneTree): OneTree
{
  match t
  case Node(n, children) => OneTree.Node(n+1, XForestInc(children))
}

ghost function XForestInc(forest: TreeList): TreeList
{
  match forest
  case Nil => forest
  case Cons(tree, tail) => TreeList.Cons(XInc(tree), XForestInc(tail))
}

// ------------------ fun with recursive functions

ghost function len<T>(l: List<T>): int
{
  match l
  case Nil => 0
  case Cons(h,t) => 1 + len(t)
}

ghost function SingletonList<T>(h: T): List<T>
  ensures len(SingletonList(h)) == 1;
{
  List.Cons(h, List.Nil)
}

ghost function Append<T>(a: List<T>, b: List<T>): List<T>
  ensures len(Append(a,b)) == len(a) + len(b);
{
  match a
  case Nil => b
  case Cons(h,t) => List.Cons(h, Append(t, b))
}

ghost function Rotate<T>(n: int, l: List<T>): List<T>
  requires 0 <= n;
  ensures len(Rotate(n, l)) == len(l);
{
  match l
  case Nil => l
  case Cons(h, t) =>
    if n == 0 then l else
      Rotate(n-1, Append(t, SingletonList(h)))
}


