// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Nat = Zero | Suc(Nat)

predicate Even(n: Nat)
{
  match n
  case Zero => true
  case Suc(Zero) => false
  case Suc(Suc(p)) => Even(p)
}


method checkEven(n: Nat) {
  assert Even(Zero) == true;
  assert Even(Suc(Zero)) == false;
  assert Even(Suc(Suc(n))) == Even(n);
}

datatype List<T> = Nil | Cons(T, List<T>)

function last<T>(xs: List<T>): T
  requires xs != Nil
{
  match xs
  case Cons(y, Nil) => y
  case Cons(y, Cons(z, zs)) => last(Cons(z, zs))
}

method checkLast<T>(y: T) {
  assert last(Cons(y, Nil)) == y;
  assert last(Cons(y, Cons(y, Nil))) == last(Cons(y, Nil));
}


function minus(x: Nat, y: Nat): Nat
{
  match (x, y)
  case (Zero, _) => Zero
  case (Suc(_), Zero) => x
  case (Suc(a), Suc(b)) => minus(a, b)
}

method checkMinus(x:Nat, y: Nat) {
  assert minus(Suc(x), Suc(y)) == minus(x,y);
}


// nested match statement
method Last<T>(xs: List<T>) returns (x: T)
  requires xs != Nil
{
 
  match xs {
  	case Cons(y, Nil) => x:= y;
  	case Cons(y, Cons(z, zs)) => x:=Last(Cons(z, zs));
  }
}
