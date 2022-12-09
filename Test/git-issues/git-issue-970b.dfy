// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method UnresolvedRhs(x: int) returns (r: Status)
{
  var i;
  i :- Pind(x);  // error: 'Pind' not found
}

method BadFunctionRhs(x: int) returns (r: Status)
{
  var i;
  i :- Find(x);  // error: wrong number of out-parameters ('Find' is a function) had caused crash
}

method BadMethodRhs(x: int) returns (r: Status)
{
  var i;
  i :- Mind(x);  // error: wrong number of out-parameters
}

method GoodFunctionRhs(x: int) returns (r: Result)
{
  var i;
  i :- Hind(x);  // ('Hind' is a function) had caused crash
}

method GoodMethodRhs(x: int) returns (r: Result)
{
  var i;
  i :- Tind(x);
}

datatype Status = Okay | Error(description: string) {
  predicate method IsFailure() {
    Error?
  }
  function method PropagateFailure(): Status
    requires Error?
  {
    this
  }
}

datatype Result = Success(value: int) | Exception(description: string) {
  predicate method IsFailure() {
    Exception?
  }
  function method PropagateFailure(): Result
    requires Exception?
  {
    this
  }
  function method Extract(): int
    requires Success?
  {
    value
  }
}

function method Find(x: int): Status
method Mind(x: int) returns (s: Status)

function method Hind(x: int): Result
method Tind(x: int) returns (s: Result)
