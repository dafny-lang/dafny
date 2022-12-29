// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

codatatype Stream<T> = SNil | SCons(head: T, tail: Stream)
datatype Tree = Node(children: Stream<Tree>)

// return an infinite stream of trees
function BigTree(): Tree
{
  Node(BigTrees())
}
function BigTrees(): Stream<Tree>
  decreases 0;
{
  SCons(BigTree(), BigTrees())
}

// say whether a tree has finite height
predicate HasBoundedHeight(t: Tree)
{
  exists n :: 0 <= n && LowerThan(t.children, n)
}
greatest predicate LowerThan(s: Stream<Tree>, n: nat)
{
  match s
  case SNil => true
  case SCons(t, tail) =>
    1 <= n && LowerThan(t.children, n-1) && LowerThan(tail, n)
}

// return a finite tree
function SmallTree(n: nat): Tree
{
  Node(SmallTrees(n))
}
function SmallTrees(n: nat): Stream<Tree>
  decreases -1;
{
  if n == 0 then SNil else SCons(SmallTree(n-1), SmallTrees(n))
}
// prove that the tree returned by SmallTree is finite
lemma Theorem(n: nat)
  ensures HasBoundedHeight(SmallTree(n));
{
  Lemma(n);
}
greatest lemma Lemma(n: nat)
  ensures LowerThan(SmallTrees(n), n);
{
  if 0 < n {
    Lemma(n-1);
  }
}
