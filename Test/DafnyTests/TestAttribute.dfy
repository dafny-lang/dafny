// RUN: msbuild -t:restore ../DafnyTests.sln
// RUN: msbuild -t:Test -v:q -noLogo > "%t".raw || true
// Remove the absolute file path before the expected error
// RUN: sed 's/[^:]*://' "%t".raw > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern} Tests {

    datatype VoidOutcome =
    | VoidSuccess
    | VoidFailure(error: string)
    {
        predicate method IsFailure() {
            this.VoidFailure?
        }
        function method PropagateFailure(): VoidOutcome requires IsFailure() {
            this
        }
    }
    
    function method {:test} PassingTest(): VoidOutcome {
        VoidSuccess
    }

    function method {:test} FailingTest(): VoidOutcome {
        VoidFailure("Whoopsie")
    }
}
