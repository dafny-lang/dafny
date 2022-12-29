// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> =
  | Success(value: T)
  | Failure(error: string)

datatype C = C1 | C2(x: int)

trait Foo
{
  method FooMethod4()  returns (r: Result<C>)
    ensures
      match r { // ERROR - missing case
        case Success(C1()) => true
        case Failure(e) => true
        // ERROR - missing cases
      }

  method FooMethod4a()  returns (r: Result<C>)
    ensures
      match r { // ERROR - missing case, C1 is a constructor
        case Success(C1) => true
        case Failure(e) => true
      }

}

