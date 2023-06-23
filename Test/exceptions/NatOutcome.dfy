// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Does not test anything Exceptions-related, but is included by other tests

datatype Option<T> = None | Some(get: T)

function Unreachable<R>(): R
    requires false
{
    var o: Option<R> := None;
    assert o.Some?;
    o.get
}

trait NatOutcome {
    predicate IsFailure()
    function PropagateFailure(): NatOutcome requires IsFailure()
    function Extract(): nat requires !IsFailure()
}

class NatSuccess extends NatOutcome {
    const value: nat
    constructor(value: nat) {
        this.value := value;
    }
    predicate IsFailure() {
        false
    }
    function PropagateFailure(): NatOutcome requires IsFailure() {
        Unreachable<NatOutcome>()
    }
    function Extract(): nat requires !IsFailure() {
        value
    }
}

class NatFailure extends NatOutcome {
    const error: string
    constructor(error: string) {
        this.error := error;
    }
    predicate IsFailure() {
        true
    }
    function PropagateFailure(): NatOutcome requires IsFailure() {
        this
    }
    function Extract(): nat requires !IsFailure() {
        Unreachable<nat>()
    }
}

method MakeNatSuccess(n: nat) returns (res: NatOutcome) {
    res := new NatSuccess(n);
}

method MakeNatFailure(msg: string) returns (res: NatOutcome) {
    res := new NatFailure(msg);
}
