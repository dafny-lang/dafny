module Result {
  datatype Result<T> = Success(x: T) | Failure(e: string)
}
module Test {
  import opened Result
  function method f(): Result<int>
  {
    Success(0)
  }
}
