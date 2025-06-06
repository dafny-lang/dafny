// RUN: %testDafnyForEachResolver "%s"

module Issue1461 {
    class Bug1461 {
        twostate predicate p() reads this
        method test() {
            var q := p;
            assume {:axiom} p();  // no problem
            assume {:axiom} q();  // added {:axiom} to suppress the warning
        }
    }
}