// RUN: %dafny /compile:3 /optimize "%s" > "%t"

/*
method foo() returns (i: int) {

}

method Main() {
    var x: int := foo();
    print x;
}
*/

datatype Option<T> = None | Some(get: T)

function method Unreachable<R>(): R
    requires false 
{
    var o: Option<R> := None;
    assert o.Some?;
    o.get
}

trait NatOutcome {
    predicate method IsFailure()
	function method PropagateFailure(): NatOutcome requires IsFailure()
	function method Extract(): nat requires !IsFailure()
}

class NatSuccess extends NatOutcome {
    const value: nat
    constructor(value: nat) {
        this.value := value;
    }
    predicate method IsFailure() { 
        false 
    }
	function method PropagateFailure(): NatOutcome requires IsFailure() {
        Unreachable<NatOutcome>() 
    }
	function method Extract(): nat requires !IsFailure() { 
        value
    }
}

class NatFailure extends NatOutcome {
    const error: string;
    constructor(error: string) {
        this.error := error;
    }
    predicate method IsFailure() { 
        true
    }
	function method PropagateFailure(): NatOutcome requires IsFailure() {
        this
    }
	function method Extract(): nat requires !IsFailure() { 
        Unreachable<nat>()
    }
}

method MakeNatSuccess(n: nat) returns (res: NatOutcome) {
    res := new NatSuccess(n);
}

method MakeNatFailure(msg: string) returns (res: NatOutcome) {
    res := new NatFailure(msg);
}


method TestParsing(b: bool, n: nat, o1: NatOutcome, o2: NatOutcome) {
    // 2x2 matrix of (expr, stmt) x (explicit type, no explicit type), where stmt also tests reassignment

    var stmt1: /*nat*/ NatOutcome :- MakeNatSuccess(n);
    stmt1 :- MakeNatFailure("sorry, bad luck");
    var use_stmt1: /*nat*/ NatOutcome := stmt1;

    var stmt2 :- MakeNatSuccess(n);
    stmt2 :- MakeNatFailure("sorry, bad luck");
    var use_stmt2: /*nat*/ NatOutcome := stmt2;

}

/*
method TestParsing(b: bool, n: nat, o1: NatOutcome, o2: NatOutcome) {
    // 2x2 matrix of (expr, stmt) x (explicit type, no explicit type), where stmt also tests reassignment

    var expr1: nat :- (var x := if b then o1 else o2; x);
    var use_expr1: nat := expr1;

    var stmt1: nat :- MakeNatSuccess(n);
    stmt1 :- MakeNatFailure("sorry, bad luck");
    var use_stmt1: nat := stmt1;

    var expr2 :- (var x := if b then o1 else o2; x);
    var use_expr2: nat := expr2;

    var stmt2 :- MakeNatSuccess(n);
    stmt2 :- MakeNatFailure("sorry, bad luck");
    var use_stmt2: nat := stmt2;
}
*/