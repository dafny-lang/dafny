// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype NatOutcome =
| Success(value: nat)
| Failure(error: string)
{
  predicate IsFailure() {
    this.Failure?
  }
  // translation of "this" in well-formedness check here previously crashed
  function PropagateFailure(): NatOutcome
    requires IsFailure()
  {
    this
  }
  function Extract(): nat
    requires !IsFailure()
  {
    this.value
  }
  function P(): nat
    ensures this.P() < 20  // translation of "this" here previously crashed
  {
    if Success? then 12 else 14
  }
  function R(): nat
  {
    var x :| 0 <= x < this.P() + 1 && x < 1;  // translation of "this" here previously crashed
    x
  }
}

method Main() {
  var n := Success(55);
  assert !n.IsFailure();
  var v := n.Extract();
  print n, " ", n.IsFailure(), " ", v, "\n";  // Success(55) false 55
  print n.P(), " ", n.R(), "\n";  // 12 0

  n := Failure("it could be worse");
  assert n.IsFailure();
  var p := n.PropagateFailure();
  print n, " ", n.IsFailure(), " ", p, "\n";  // Failure(...) true Failure(...)
  print n.P(), " ", n.R(), "\n";  // 14 0
}
