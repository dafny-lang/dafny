// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Does not test anything Exceptions-related, but is included by other tests

trait VoidOutcome {
    compiled predicate IsFailure()
    compiled function PropagateFailure(): VoidOutcome requires IsFailure()
}

class VoidSuccess extends VoidOutcome {
    constructor() {}
    compiled predicate IsFailure() {
        false
    }
    compiled function PropagateFailure(): VoidOutcome requires IsFailure() {
        this
    }
}

class VoidFailure extends VoidOutcome {
    const error: string
    constructor(error: string) {
        this.error := error;
    }
    compiled predicate IsFailure() {
        true
    }
    compiled function PropagateFailure(): VoidOutcome requires IsFailure() {
        this
    }
}

method MakeVoidSuccess() returns (res: VoidOutcome) {
    res := new VoidSuccess();
}

method MakeVoidFailure(msg: string) returns (res: VoidOutcome) {
    res := new VoidFailure(msg);
}
