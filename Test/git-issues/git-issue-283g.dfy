// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> =
  | Success(value: T)
  | Failure(error: string)

datatype Bar = C1() | C2(bl: string)

const X: int := 42
const SS: string := "asd"

trait Foo
{
  static const S: string := "asd"

  method FooMethod1() returns (r: Result<string>)
    ensures
      match Result<string>.Failure(S) {
        case Failure(X) => true  // ERROR: X is a constant, but wrong type
        case Success(C1) => true // C1 is a variable
      }

}

datatype Cell<T> = Cell(value: T)

const Y := 1  // type of Y must be inferred
method q() {
  var c: Cell;  // note, type argument omitted; it will eventually be inferred
  match c {
    case Cell(Y) =>     // Y is int, so C is Cell<int>
    case Cell(_) =>     // if Y is a const, then this case is not redundant
  }
  c := Cell(1.2); // ERROR: type mismatch
}

method qq() {
  var c: Cell<real>;
  match c {
    case Cell(Y) =>     // ERROR: Y is a const int, so a type mismatch is reported
    case Cell(_) =>     // if Y is a const, then this case is not redundant
  }
}

method qqq() {
  var c: Cell;
  match c {
    case Cell(XX) =>     // XX is a variable
    case Cell(_) =>     // WARNING so then this case is not redundant
  }
}

