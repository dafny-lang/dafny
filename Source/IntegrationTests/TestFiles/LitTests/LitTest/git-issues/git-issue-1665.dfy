// Check that Rprinted program is generated as expected:
// RUN: %dafny /env:0 /compile:0 /dafnyVerify:0 /rprint:"%t".raw.dfy "%s"
// RUN: %diff "%s.expect" "%t".raw.dfy

// Check that original program successfully verifies (exit code 0):
// RUN: %dafny /env:0 /compile:0 "%s" > "%t".1

// Check that produced rprinted program also successfuly verifies:
// RUN: %dafny /env:0 /compile:0 "%t".raw.dfy > "%t".2

// Check that verification results are the same:
// RUN: %diff "%t".1 "%t".2

module ConcreteModule
{
  datatype Status =
    | Success
    | Failure(error: nat)
  {
    predicate IsFailure() { this.Failure? }
    function PropagateFailure(): Status
      requires IsFailure()
    {
      Failure(this.error)
    }
  }
    
  method execute_external_method(n:nat, m:nat) returns (r:Status)
  {
    match n { // match statement is essential to reproduce the bug
      case 0 =>            
        :- Func1(); // elephant operator is essential to reproduce the bug
        match m {
          case 1 =>
            :- Func1();
          case _ =>
            return Success;
        }
      case _ =>
        return Success;
    }
  }

  method Func1() returns (r:Status)
  {
    return Success;
  }

  method AdditionalWildcardTests(n: nat) {
    match n {
      case _ =>
    }
    match n {
      case _: int =>
    }
    match n {
      case _: nat =>
    }
    match n {
      case 3 =>
      case _: int =>
    }
    match n {
      case x =>
    }
    match n {
      case n => // bound variable shadows parameter n
    }
    match n {
      case x: int =>
    }
    match n {
      case n: int => // bound variable shadows parameter n
    }
  }
}
