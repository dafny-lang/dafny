// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<A> = Nil | Cons(head: A,tail: List<A>);

datatype Tree<A> = Branch(val: A,trees: List<Tree<A>>);

function ListData(xs : List) : set
  ensures forall x :: x in ListData(xs) ==> x < xs;
{
  match xs
    case Nil => {}
    case Cons(x,xs) => {x} + ListData(xs)
}

function TreeData(t0 : Tree) : set
  ensures forall t :: t in TreeData(t0) ==> t < t0;
{
  var Branch(x,ts) := t0;
  {x} + set t, y | t in ListData(ts) && y in TreeData(t) :: y
}

function Pre(f : A -> B, s : set<A>) : bool
  reads (set x, y | x in s && y in f.reads(x) :: y);
{
  forall x :: x in s ==> f.reads(x) == {} && f.requires(x)
}

function method Map(xs : List<A>, f : A -> B): List<B>
  reads (set x, y | x in ListData(xs) && y in f.reads(x) :: y);
  requires Pre(f, ListData(xs));
  decreases xs;
{
  match xs
    case Nil => Nil
    case Cons(x,xs) => Cons(f(x),Map(xs,f))
}

function method TMap(t0 : Tree<A>, f : A -> B) : Tree<B>
  reads (set x, y | x in TreeData(t0) && y in f.reads(x) :: y);
  requires Pre(f, TreeData(t0));
  decreases t0;
{
  var Branch(x,ts) := t0;
  Branch(f(x),Map(ts, t  requires t in ListData(ts)
                         requires Pre(f, TreeData(t))
                      => TMap(t,f)))
}

