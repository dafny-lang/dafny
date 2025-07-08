// RUN: %verify "%s" > "%t"
// RUN: %baredafny test --no-verify --target=cs %args   "%s" >> "%t"
// RUN: %baredafny test --no-verify --target=java %args "%s" >> "%t"
// RUN: %baredafny test --no-verify --target=go %args   "%s" >> "%t"
// RUN: %baredafny test --no-verify --target=py %args   "%s" >> "%t"

module SequenceConcatOptimization {

  // A basic performance sanity check for the sequence concatenation
  // that is now implemented for C#, Java, and Go (with the latter
  // using a common implementation in Dafny).
  // In these languages this test completes in a second or so,
  // but the others take much longer than I was willing to wait.
  method {:test} SirConcatsALot() {
    var s: seq<int> := [];
    var n := 1_000_000;

    for i := 0 to n 
      invariant |s| == i
    {
      s := s + [i];
    }

    for i := 0 to n
    {
      expect s[i] == i;
    }

    expect |s| == n;
  }
}
