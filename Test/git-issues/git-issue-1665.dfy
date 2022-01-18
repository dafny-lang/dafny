// RUN: %dafny /env:0 /dafnyVerify:0 /compile:0 /rprint:- "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module ConcreteModule
{
	datatype Status =
		| Success
		| Failure(error: nat)
	{
		predicate method IsFailure() { this.Failure? }
		function method PropagateFailure(): Status
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
}
