// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
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

  method FooMethod2() returns (r: Result<Bar>)
    ensures
      match r { // missing case
        case Success(C2("")) => r == Result<Bar>.Success(Bar.C1)
        case Success(C1()) => true
        case Failure(e) => true
      }

  method FooMethod3() returns (r: Result<string>)
    ensures
      match r { // SS is a const, so missing case
        case Success(_) => true
        case Failure(SS) => true
      }

}
