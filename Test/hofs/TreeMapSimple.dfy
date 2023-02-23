// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  TestY();
  TestZ();
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

ghost function TreeData(t0: Tree): set
  ensures forall t :: t in TreeData(t0) ==> t < t0
{
  var Branch(x, ts) := t0;
  {x} + set t, y | t in ListData(ts) && y in TreeData(t) :: y
}

// ---------- Partial functions ----------

ghost predicate PreY<A,B>(f: A --> B, s: set<A>) {
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

// ---------- Read-effect functions ----------

ghost predicate PreZ<A,B>(f: A ~> B, s: set<A>)
  reads set x, y | x in s && y in f.reads(x) :: y
{
  forall x :: x in s ==> f.requires(x)
}

function MapZ<A,B>(xs: List<A>, f: A ~> B): List<B>
  requires PreZ(f, ListData(xs))
  reads PreZ.reads(f, ListData(xs))
  decreases xs
{
  match xs
  case Nil => Nil
  case Cons(x, xs) => Cons(f(x), MapZ(xs, f))
}

function TreeMapZ<A,B>(t0: Tree<A>, f: A ~> B): Tree<B>
  requires PreZ(f, TreeData(t0))
  reads PreZ.reads(f, TreeData(t0))
  decreases t0
{
  var Branch(x, ts) := t0;
  var g := t requires t in ListData(ts) && PreZ(f, TreeData(t))
            reads set x, y | x in TreeData(t) && y in f.reads(x) :: y
           => TreeMapZ(t, f);
  Branch(f(x), MapZ(ts, g))
}

method TestZ() {
  var f := x requires x != 0 => 100 / x;
  var t := TreeMapZ(Branch(1, Cons(Branch(2, Nil), Nil)), f);
  // Functions with reads clauses don't get Lit axioms, so we can't prove the same
  // assertion as we did in TestY.
  print t, "\n";
}
