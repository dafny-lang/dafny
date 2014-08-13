
datatype List<A> = Nil | Cons(A, List<A>)

datatype Tree<A> = Branch(A, trees: List<Tree<A>>)

function ListData(xs: List<A>): set<A>
  // ensures forall x :: x in ListData(xs) ==> x < xs;
{
  match xs
    case Nil => {}
	case Cons(x,xs) => {x} + ListData(xs)
}

function TreeData(t0: Tree<A>): set<A>
{
  var Branch(x, ts) := t0;
  {x} + set t, y | t in ListData(ts) && y in TreeData(t) :: y
}

function Map(xs : List<A>, f : A -> B): List<B>
{
  match xs
    case Nil => Nil
	case Cons(x,xs) => Cons(f(x),Map(xs,f))
}

function TMap(t0 : Tree<A>, f : A -> B): Tree<B>
{
  var Branch(x, ts) := t0;
  Branch(f(x), Map(ts, t => TMap(t,f)))
}
