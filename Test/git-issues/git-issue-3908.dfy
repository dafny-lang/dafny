// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(T, List<T>)

method UnexpectedError<G>(l: List<G>)
{
  var x0: real;
  match l
  case Cons(x: G, y) =>
    x0 := 31.4; // this once generated a bogus error that real cannot be assigned to G
  case Nil =>
}

method UnexpectedDuplicateName<G>(l: List<G>)
{
  match l
  case Cons(x: G, y) =>
    var x0: real; // this once generated a bogus error that name of local variable x0 is a duplicate
  case Nil =>
}

function UnexpectedErrorInFunction<G>(l: List<G>): int
{
  var x0: real := 3.14;
  match l
  case Cons(x: G, y) =>
    var a: real := x0; // this once generated a bogus error that G cannot be assigned to real
    10
  case Nil =>
    11
}
