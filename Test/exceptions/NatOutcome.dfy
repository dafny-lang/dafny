// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Does not test anything Exceptions-related, but is included by other tests

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
    const error: string
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
