// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> =
  | Success(value: T)
  | Failure(error: string)

datatype C = C1 | C2(x: int)

trait Foo
{
  method FooMethod()  returns (r: Result<string>)
    ensures
      match r {
        case Success(()) => true // ERROR () does not match string
        case Failure(e) => true
      }

  method FooMethod2()  returns (r: Result<C>)
    ensures
      match r {
        case Success(D()) => true // ERROR - not a constructor
        case Failure(e) => true
      }

  method FooMethod3()  returns (r: Result<C>)
    ensures
      match r {
        case Success(C2()) => true // ERROR - wrong number of arguments
        case Failure(e) => true
      }

  method FooMethod5()  returns (r: Result<C>)
    ensures
      match r {
        case Success(C1()) => true
        case Success(C1) => true // ERROR - duplicate constructor
        case Failure(e) => true
      }
}

