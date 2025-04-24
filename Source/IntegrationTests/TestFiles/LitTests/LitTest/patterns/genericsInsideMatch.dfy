// RUN: %verify --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<X> = Nil | Cons(head: X, tail: List<X>)

method Split<X>(ws: List<X>) returns (ans: int)
{
  match ws
  case Cons(a, Cons(b, tail)) => {
    forall rx: List<X>
    {}
    return 0;
  }
  case _ => {
    return 0;
  }
}