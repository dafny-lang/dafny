// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny test --no-verify --target=cs %args   "%s" >> "%t"
// RUN: %baredafny test --no-verify --target=java %args "%s" >> "%t"
// RUN: %baredafny test --no-verify --target=go %args   "%s" >> "%t"

module SequenceConcatOptimization {

    // A basic performance sanity check for the sequence concatenation
    // that is now implemented for C#, Java, and Go (with the latter
    // using a common implementation in Dafny).
    // In these languages this test completes in a second or so,
    // but the others take much longer than I was willing to wait.
    method {:test} SirConcatsALot() {
        var s: seq<int> := [];
        for i := 0 to 1_000_000 {
            s := s + [i];
        }
        expect |s| == 1_000_000;
    }
}