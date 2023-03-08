// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Does not test anything Exceptions-related, but is included by other tests

trait VoidOutcome {
    predicate IsFailure()
    function PropagateFailure(): VoidOutcome requires IsFailure()
}

class VoidSuccess extends VoidOutcome {
    constructor() {}
    predicate IsFailure() {
        false
    }
    function PropagateFailure(): VoidOutcome requires IsFailure() {
        this
    }
}

class VoidFailure extends VoidOutcome {
    const error: string
    constructor(error: string) {
        this.error := error;
    }
    predicate IsFailure() {
        true
    }
    function PropagateFailure(): VoidOutcome requires IsFailure() {
        this
    }
}

method MakeVoidSuccess() returns (res: VoidOutcome) {
    res := new VoidSuccess();
}

method MakeVoidFailure(msg: string) returns (res: VoidOutcome) {
    res := new VoidFailure(msg);
}
