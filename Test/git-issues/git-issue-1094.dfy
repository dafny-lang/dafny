// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ----- Type error -----

method FP() returns (r: FStatus)
{
  {
    var r: int;  // this variable shadows the out-parameter r
    :- FTry();  // regression: this once gave an error saying RHS (of type FStatus) not assignable to LHS (of type int)
  }
}

method MP() returns (r: MStatus)
{
  {
    var r: int;  // this variable shadows the out-parameter r
    :- MTry();  // regression: this once gave an error saying RHS (of type MStatus) not assignable to LHS (of type int)
  }
}

method FQ() returns (r: FResult<int>)
  ensures r == FResult.Failure(5)
{
  {
    var r: int;  // this variable shadows the out-parameter r
    var x :- FCompute();  // regression: this once gave an error saying RHS (of type FResult<?>) not assignable to LHS (of type int)
  }
}

method MQ() returns (r: MResult<int>)
  ensures r == MResult.Failure(5)
{
  {
    var r: int;  // this variable shadows the out-parameter r
    var x :- MCompute();  // regression: this once gave an error saying RHS (of type MResult<?>) not assignable to LHS (of type int)
  }
}

// ----- Verification error -----

method FS() returns (r: FStatus)
  ensures r == FStatus.Error(5)
{
  {
    var r: FStatus;  // this variable shadows the out-parameter r
    :- FTry();  // regression: this once resulted in a reported postcondition violation
  }
}

method MS() returns (r: MStatus)
  ensures r == MStatus.Error(5)
{
  {
    var r: MStatus;  // this variable shadows the out-parameter r
    :- MTry();  // regression: this once resulted in a reported postcondition violation
  }
}

method FR() returns (r: FResult<int>)
  ensures r == FResult.Failure(5)
{
  {
    var r: FResult<int>;  // this variable shadows the out-parameter r
    var x :- FCompute();  // regression: this once resulted in a reported postcondition violation
  }
}

method MR() returns (r: MResult<int>)
  ensures r == MResult.Failure(5)
{
  {
    var r: MResult<int>;  // this variable shadows the out-parameter r
    var x :- MCompute();  // regression: this once resulted in a reported postcondition violation
  }
}

// ----- Aux definitions -----

method FTry() returns (status: FStatus)
  ensures status == FStatus.Error(5)

method MTry() returns (status: MStatus)
  ensures status == MStatus.Error(5)

datatype FStatus = Okay | Error(code: int) {
  predicate method IsFailure() {
    Error?
  }
  function method PropagateFailure(): FStatus
    requires Error?
  {
    this
  }
}

datatype MStatus = Okay | Error(code: int) {
  predicate method IsFailure() {
    Error?
  }
  method PropagateFailure() returns (m: MStatus)
    requires Error?
    ensures m == this
  {
    return this;
  }
}

method FCompute() returns (result: FResult<int>)
  ensures result == FResult.Failure(5)

method MCompute() returns (result: MResult<int>)
  ensures result == MResult.Failure(5)

datatype FResult<X> = Success(x: X) | Failure(code: int) {
  predicate method IsFailure() {
    Failure?
  }
  function method PropagateFailure<U>(): FResult<U>
    requires Failure?
  {
    FResult.Failure(code)
  }
  function method Extract(): X
    requires Success?
  {
    x
  }
}

datatype MResult<X> = Success(x: X) | Failure(code: int) {
  predicate method IsFailure() {
    Failure?
  }
  method PropagateFailure<U>() returns (result: MResult<U>)
    requires Failure?
    ensures result.Failure? && result.code == code
  {
    return MResult.Failure(code);
  }
  method Extract() returns (result: X)
    requires Success?
  {
    return x;
  }
}
