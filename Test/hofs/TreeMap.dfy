
datatype List<A> = Nil | Cons(head: A,tail: List<A>);

datatype Tree<A> = Branch(val: A,trees: List<Tree<A>>);

function Set(xs : List) : set
  ensures forall x :: x in Set(xs) ==> x < xs;
{
  match xs
    case Nil => {}
    case Cons(x,xs) => {x} + Set(xs)
}

function TSet(t0 : Tree) : set
  ensures forall t :: t in TSet(t0) ==> t < t0;
{
  match t0 case Branch(x,ts) => {x} + set t, y | t in Set(ts) && y in TSet(t) :: y
}

// reads {}

function ReadNothingMap(f : A -> B, xs: List<A>): List<B>
  requires forall x :: x in Set(xs) ==> f.requires(x);
  requires forall x :: f.reads(x) == {};
  decreases xs;
{
  match xs
    case Nil => Nil
    case Cons(x,xs) => Cons(f(x),ReadNothingMap(f,xs))
}

function TReadNothingMap(f: A -> B, t0: Tree<A>): Tree<B>
  requires forall x {:heapQuantifier} :: f.requires(x);
  requires forall x {:heapQuantifier} :: f.reads(x) == {};
  decreases t0;
{
  var Branch(x,ts) := t0;
  Branch(f(x), ReadNothingMap(t requires t in Set(ts) => TReadNothingMap(f,t), ts))
}

function TReadNothingMap2(f: A -> B, t0: Tree<A>): Tree<B>
  requires forall x :: f.requires(x);
  requires forall x :: f.reads(x) == {};
  decreases t0;
{
  var Branch(x,ts) := t0;
  Branch(f(x), ReadNothingMap(t requires t in Set(ts) -> TReadNothingMap2(f,t), ts))
}

function TReadNothingMap3(f: A -> B, t0: Tree<A>): Tree<B>
  requires forall x :: f.requires(x);
  requires forall x :: f.reads(x) == {};
  decreases t0;
{
  var Branch(x,ts) := t0;
  Branch(f(x), ReadNothingMap(
    t requires t in Set(ts)
      requires (forall x :: x in TSet(t) ==> f.requires(x))
    => TReadNothingMap(f,t), ts))
}

method TestReadNothingStar() {
  assert TReadNothingMap(x => x + 1, Branch(1,Nil)).Branch?;

  assert TReadNothingMap(x => x + 1, Branch(0,Nil)) == Branch(1,Nil);

  assert TReadNothingMap(x => x + 1, Branch(1,Cons(Branch(0,Nil),Nil)))
      == Branch(2,Cons(Branch(1,Nil),Nil));

  assert TReadNothingMap2(x -> x + 1, Branch(1,Nil)).Branch?;

  assert TReadNothingMap2(x -> x + 1, Branch(0,Nil)) == Branch(1,Nil);

  assert TReadNothingMap2(x -> x + 1, Branch(1,Cons(Branch(0,Nil),Nil)))
      == Branch(2,Cons(Branch(1,Nil),Nil));
}

/// reads *

function ReadStarMap(f : A -> B, xs: List<A>): List<B>
  requires forall x :: x in Set(xs) ==> f.requires(x);
  reads *;
  decreases xs;
{
  match xs
    case Nil => Nil
    case Cons(x,xs) => Cons(f(x),ReadStarMap(f,xs))
}

function TReadStarMap(f: A -> B, t0: Tree<A>): Tree<B>
  requires forall x {:heapQuantifier} :: f.requires(x);
  reads *;
  decreases t0;
{
  var Branch(x,ts) := t0;
  Branch(f(x), ReadStarMap(t reads * requires t in Set(ts) => TReadStarMap(f,t), ts))
}

function TReadStarMap2(f: A -> B, t0: Tree<A>): Tree<B>
  requires forall x :: f.requires(x);
  reads *;
  decreases t0;
{
  var Branch(x,ts) := t0;
  Branch(f(x), ReadStarMap(t reads * requires t in Set(ts) -> TReadStarMap2(f,t), ts))
}

lemma LitTReadStarMap2(f : A -> B, x : A, ts: List<Tree<A>>)
  requires forall u :: f.requires(u);
  ensures TReadStarMap2(f, Branch(x,ts)) ==
    Branch(f(x), ReadStarMap(t reads * requires t in Set(ts) -> TReadStarMap2(f,t), ts));
{
  assert TReadStarMap2(f, Branch(x,ts)).val == f(x);
  if (ts.Nil?) {
    assert TReadStarMap2(f, Branch(x,ts)).trees ==
      ReadStarMap(t reads * requires t in Set(ts) -> TReadStarMap2(f,t),ts);
  } else {
    assert TReadStarMap2(f, Branch(x,ts)).trees ==
      ReadStarMap(t reads * requires t in Set(ts) -> TReadStarMap2(f,t),ts);
  }
}

method TestReadStar() {
  assert TReadStarMap(x => x + 1, Branch(1,Nil)).Branch?;

  assert TReadStarMap(x => x + 1, Branch(0,Nil)) == Branch(1,Nil);

  assert ReadStarMap(t reads * requires t in Set(Cons(Branch(0,Nil),Nil)) -> TReadStarMap(x => x + 1,t)
                    , Cons(Branch(0,Nil),Nil))
      == Cons(Branch(1,Nil),Nil);

  assert TReadStarMap(x => x + 1, Branch(1,Cons(Branch(0,Nil),Nil))).Branch?;

  assert TReadStarMap(x => x + 1, Branch(1,Cons(Branch(0,Nil),Nil))).val == 2;

  assert TReadStarMap(x => x + 1, Branch(1,Cons(Branch(0,Nil),Nil))).trees == Cons(Branch(1,Nil),Nil);

  assert TReadStarMap(x => x + 1, Branch(1,Cons(Branch(0,Nil),Nil)))
      == Branch(2,Cons(Branch(1,Nil),Nil));

  assert TReadStarMap2(x -> x + 1, Branch(1,Nil)).Branch?;

  assert TReadStarMap2(x -> x + 1, Branch(0,Nil)) == Branch(1,Nil);

  assert TReadStarMap2(x -> x + 1, Branch(1,Cons(Branch(0,Nil),Nil)))
      == Branch(2,Cons(Branch(1,Nil),Nil));
}

/// reads exact

function Map(f : A -> B, xs: List<A>): List<B>
  requires forall x :: x in Set(xs) ==> f.requires(x);
  reads set x, y | x in Set(xs) && y in f.reads(x) :: y;
  decreases xs;
{
  match xs
    case Nil => Nil
    case Cons(x,xs) => Cons(f(x),Map(f,xs))
}

function TMap(f : A -> B, t0: Tree<A>): Tree<B>
  requires forall t :: t in TSet(t0) ==> f.requires(t);
  reads set x, y | x in TSet(t0) && y in f.reads(x) :: y;
  decreases t0;
{
  var Branch(x,ts) := t0;
  Branch(
    f(x),
    Map( t requires t in Set(ts)
           reads set x, y | x in TSet(t) && y in f.reads(x) :: y
           -> TMap(f,t)
       , ts)
  )
}

lemma LitTMap(f : A -> B,x : A, ts: List<Tree<A>>)
  requires f.requires(x);
  requires forall t, u :: t in Set(ts) && u in TSet(t) ==> f.requires(u);
  ensures TMap(f, Branch(x,ts)) ==
    Branch(f(x),
      Map( t requires t in Set(ts)
             reads set x, y | x in TSet(t) && y in f.reads(x) :: y
             -> TMap(f,t),ts));
{
  assert TMap(f, Branch(x,ts)).val == f(x);
  assert TMap(f, Branch(x,ts)).trees ==
      Map(t requires t in Set(ts)
            reads set x, y | x in TSet(t) && y in f.reads(x) :: y
            -> TMap(f,t),ts);
}

method Test() {
  assert TMap(x -> x + 1, Branch(1,Nil)).Branch?;

  assert TMap(x -> x + 1, Branch(0,Nil)) == Branch(1,Nil);

  calc {
       TMap(x -> x + 1, Branch(1,Cons(Branch(0,Nil),Nil)));
    == { LitTMap(x -> x + 1,1, Cons(Branch(0,Nil),Nil)); }
       Branch((x -> x + 1)(1),Map(t -> TMap(x -> x + 1,t),Cons(Branch(0,Nil),Nil)));
    ==
       Branch(2,Map(t -> TMap(x -> x + 1,t),Cons(Branch(0,Nil),Nil)));
    ==
       Branch(2,Map(t -> TMap(x -> x + 1,t),Cons(Branch(0,Nil),Nil)));
    ==
       Branch(2,Cons(TMap(x -> x + 1,Branch(0,Nil)),Nil));
    ==
       Branch(2,Cons(Branch((x -> x + 1)(0),Nil),Nil));
    ==
       Branch(2,Cons(Branch(1,Nil),Nil));
  }

  assert TMap(x -> x + 1, Branch(1,Cons(Branch(0,Nil),Nil)))
      == Branch(2,Cons(Branch(1,Nil),Nil));
}
