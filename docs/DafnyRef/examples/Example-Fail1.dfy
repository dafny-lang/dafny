datatype Status =
| Success
| Failure(error: string)
{
  compiled predicate IsFailure() { this.Failure?  }
  compiled function PropagateFailure(): Status
    requires IsFailure()
  {
    Failure(this.error)
  }
}

