// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Does not test anything Exceptions-related, but is included by other tests

trait VoidOutcome {
    predicate method IsFailure()
    function method PropagateFailure(): VoidOutcome requires IsFailure()
}

class VoidSuccess extends VoidOutcome {
    constructor() {}
    predicate method IsFailure() {
        false
    }
    function method PropagateFailure(): VoidOutcome requires IsFailure() {
        this
    }
}

class VoidFailure extends VoidOutcome {
    const error: string
    constructor(error: string) {
        this.error := error;
    }
    predicate method IsFailure() {
        true
    }
    function method PropagateFailure(): VoidOutcome requires IsFailure() {
        this
    }
}

method MakeVoidSuccess() returns (res: VoidOutcome) {
    res := new VoidSuccess();
}

method MakeVoidFailure(msg: string) returns (res: VoidOutcome) {
    res := new VoidFailure(msg);
}
