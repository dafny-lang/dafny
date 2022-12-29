// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ------------------ generic list, non-generic tree

datatype List<T> = Nil | Cons(T, List<T>)

datatype Tree = Node(int, List<Tree>)

function Inc(t: Tree): Tree
{
  match t
  case Node(n, children) => Tree.Node(n+1, ForestInc(children))
}

function ForestInc(forest: List<Tree>): List<Tree>
{
  match forest
  case Nil => forest
  case Cons(tree, tail) => List.Cons(Inc(tree), ForestInc(tail))
}

// ------------------ generic list, generic tree (but GInc defined only for GTree<int>

datatype GTree<T> = Node(T, List<GTree<T>>)

function GInc(t: GTree<int>): GTree<int>
{
  match t
  case Node(n, children) => GTree.Node(n+1, GForestInc(children))
}

function GForestInc(forest: List<GTree<int>>): List<GTree<int>>
{
  match forest
  case Nil => forest
  case Cons(tree, tail) => List.Cons(GInc(tree), GForestInc(tail))
}

// ------------------ non-generic structures

datatype TreeList = Nil | Cons(OneTree, TreeList)

datatype OneTree = Node(int, TreeList)

function XInc(t: OneTree): OneTree
{
  match t
  case Node(n, children) => OneTree.Node(n+1, XForestInc(children))
}

function XForestInc(forest: TreeList): TreeList
{
  match forest
  case Nil => forest
  case Cons(tree, tail) => TreeList.Cons(XInc(tree), XForestInc(tail))
}

// ------------------ fun with recursive functions

function len<T>(l: List<T>): int
{
  match l
  case Nil => 0
  case Cons(h,t) => 1 + len(t)
}

function SingletonList<T>(h: T): List<T>
  ensures len(SingletonList(h)) == 1;
{
  List.Cons(h, List.Nil)
}

function Append<T>(a: List<T>, b: List<T>): List<T>
  ensures len(Append(a,b)) == len(a) + len(b);
{
  match a
  case Nil => b
  case Cons(h,t) => List.Cons(h, Append(t, b))
}

function Rotate<T>(n: int, l: List<T>): List<T>
  requires 0 <= n;
  ensures len(Rotate(n, l)) == len(l);
{
  match l
  case Nil => l
  case Cons(h, t) =>
    if n == 0 then l else
      Rotate(n-1, Append(t, SingletonList(h)))
}


