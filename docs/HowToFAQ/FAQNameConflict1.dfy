module Result {
  datatype Result<T> = Success(x: T) | Failure(e: string)
}
module Test {
  import opened Result
  function method f(): Result.Result<int>
  {
    Success(0)
  }
}
module Test1 {
  import opened R = Result
  function method f(): Result<int>
  {
    Success(0)
  }
}
