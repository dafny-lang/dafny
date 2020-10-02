datatype Result<T> =
  | Success(value: T)
  | Failure(error: string)

datatype Bar = C1() | C2(bla: string)

trait Foo
{
  method FooMethod1() returns (r: Result<string>)
    ensures
      match r {
        case Success(C1()) => true
        case Failure(e) => true
      }

  method FooMethod2()  returns (r: Result<string>)
    ensures
      match r {
        case Success(C2(x)) => true
        case Failure(e) => true
      }
}

