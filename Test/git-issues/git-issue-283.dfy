datatype Result<T> =
    | Success(value: T)
    | Failure(error: string)

trait Foo 
{ 
    method FooMethod()  returns (r: Result<string>)
        ensures
            match r {
                case Success(()) => true 
                case Failure(e) => true 
            }
}
