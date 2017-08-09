// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<A> = Nil | Cons(head: A,tail: List<A>)

datatype Tree<A> = Branch(val: A,trees: List<Tree<A>>)

function ListData(xs : List) : set
  ensures forall x :: x in ListData(xs) ==> x < xs
{
  match xs
    case Nil => {}
    case Cons(x,xs) => {x} + ListData(xs)
}

function TreeData(t0 : Tree) : set
  ensures forall t :: t in TreeData(t0) ==> t < t0
{
  var Branch(x,ts) := t0;
  {x} + set t, y | t in ListData(ts) && y in TreeData(t) :: y
}

function Pre<A,B>(f : A ~> B, s : set<A>) : bool
  reads (set x, y | x in s && y in f.reads(x) :: y)
{
  forall x :: x in s ==> f.reads(x) == {} && f.requires(x)
}

function method Map<A,B>(xs : List<A>, f : A ~> B): List<B>
  reads Pre.reads(f, ListData(xs))
  requires Pre(f, ListData(xs))
  decreases xs
{
  match xs
    case Nil => Nil
    case Cons(x,xs) => Cons(f(x),Map(xs,f))
}

function method TMap<A,B>(t0 : Tree<A>, f : A ~> B) : Tree<B>
  reads Pre.reads(f, TreeData(t0))
  requires Pre(f, TreeData(t0))
  decreases t0
{
  var Branch(x,ts) := t0;
  Branch(f(x),Map(ts, t  requires t in ListData(ts)
                         requires Pre(f, TreeData(t))
                      => TMap(t,f)))
}

method Main()
{
  var t := TMap(Branch(1,Cons(Branch(2,Nil),Nil)), x requires x != 0 => 100 / x);
  assert t   == Branch(100,Cons(Branch(50,Nil),Nil));
  print t, "\n";
}
