datatype Status =
| Success
| Failure(error: string)
{
  predicate method IsFailure() { this.Failure?  }
  function method PropagateFailure(): Status
    requires IsFailure()
  {
    Failure(this.error) 
  }
}

