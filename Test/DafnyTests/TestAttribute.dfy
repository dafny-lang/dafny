// RUN: msbuild -t:restore ../DafnyTests.sln
// RUN: msbuild -t:Test -v:q -noLogo > "%t".raw || true
// Remove the absolute file path before the expected error
// RUN: sed 's/[^:]*://' "%t".raw > "%t"
// RUN: %diff "%s.expect" "%t"

include "../exceptions/VoidOutcomeDt.dfy"

function method {:test} PassingTest(): VoidOutcome {
    VoidSuccess()
}

function method {:test} FailingTest(): VoidOutcome {
    VoidFailure("Whoopsie")
}
