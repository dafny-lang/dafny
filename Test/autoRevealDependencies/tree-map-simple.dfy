// RUN: %baredafny verify %args --default-function-opacity autoRevealDependencies "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  TestY();
}

datatype List<A> = Nil | Cons(head: A, tail: List<A>)

datatype Tree<A> = Branch(val: A, trees: List<Tree<A>>)

ghost function ListData(xs: List): set
  ensures forall x :: x in ListData(xs) ==> x < xs
{
  match xs
  case Nil => {}
  case Cons(x,xs) => {x} + ListData(xs)
}

ghost function {:transparent} TreeData(t0: Tree): set
  ensures forall t :: t in TreeData(t0) ==> t < t0
{
  var Branch(x, ts) := t0;
  {x} + set t, y | t in ListData(ts) && y in TreeData(t) :: y
}

// ---------- Partial functions ----------

ghost predicate {:transparent} PreY<A,B>(f: A --> B, s: set<A>) {
  forall x :: x in s ==> f.requires(x)
}

function MapY<A,B>(xs: List<A>, f: A --> B): List<B>
  requires PreY(f, ListData(xs))
  decreases xs
{
  match xs
  case Nil => Nil
  case Cons(x, xs) => Cons(f(x), MapY(xs, f))
}

function TreeMapY<A,B>(t0: Tree<A>, f: A --> B): Tree<B>
  requires PreY(f, TreeData(t0))
  decreases t0
{
  var Branch(x, ts) := t0;
  Branch(f(x), MapY(ts, t requires t in ListData(ts) && PreY(f, TreeData(t)) => TreeMapY(t, f)))
}

method TestY() {
  var f := x requires x != 0 => 100 / x;
  var t := TreeMapY(Branch(1, Cons(Branch(2, Nil), Nil)), f);
  assert t == Branch(100, Cons(Branch(50, Nil), Nil));  // proved via Lit axioms
  print t, "\n";
}
