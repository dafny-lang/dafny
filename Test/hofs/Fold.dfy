// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<A> = Nil | Cons(A,List<A>)

datatype Expr = Add(List<Expr>) | Mul(List<Expr>) | Lit(int)

function Eval(e : Expr): int
{
  match e
    case Add(es) => Fold(es, 0, (e,v) requires e < es => Eval(e) + v)
    case Mul(es) => Fold(es, 1, (e,v) requires e < es => Eval(e) * v)
    case Lit(i)  => i
}

function Fold<A,B(!new)>(xs : List<A>, unit : B, f : (A,B) --> B): B  // (is this (!new) really necessary?)
  requires forall x, y :: x < xs ==> f.requires(x,y)
{
  match xs
    case Nil => unit
    case Cons(x,xs) => f(x, Fold(xs, unit, f))
}

method Main() {
  var two := Lit(2);
  var add := (x,y) => Add(Cons(x,Cons(y,Nil)));
  assert Eval(add(two,two)) == 4;
  print "3 = ", Eval(add(Lit(1),two)), "\n";
}
