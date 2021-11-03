datatype Outcome<T> =
| Success(value: T)
| Failure(error: string)
{
  compiled predicate IsFailure() {
    this.Failure?
  }
  compiled function PropagateFailure<U>(): Outcome<U>
    requires IsFailure()
  {
    Failure(this.error) // this is Outcome<U>.Failure(...)
  }
  compiled function Extract(): T
    requires !IsFailure()
  {
    this.value
  }
}

