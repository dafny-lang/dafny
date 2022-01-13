// RUN: %dafny /env:0 /compile:0 /dafnyVerify:0 /rprint:- "%s" > "%t"
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
		
	method execute_external_method(n:nat) returns (r:Status)
	{
		match n {
			case 0 => 
				:- Func1(); // this call is essential to reproduce the bug		
			case _ =>
				return Success;
		}
	}

	method Func1() returns (r:Status)
	{
		return Success;
	}
}
