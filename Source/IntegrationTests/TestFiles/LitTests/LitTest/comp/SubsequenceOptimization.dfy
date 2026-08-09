// RUN: %verify "%s" > "%t"
// RUN: %baredafny test --no-verify --target=java %args "%s" >> "%t"

module SubsequenceOptimization {

  // A basic performance sanity check for the subsequence optimization
  // that is now implemented for Java.
  // In these languages this test completes in a second or so,
  // but the others take much longer than I was willing to wait.
  method {:test} ItSlicesItDices() {
    var n := 1_000_000;
    var s: seq<int> := seq(n, i => 1);
    
    var sum := RecursiveSum(s);
    expect n == sum;
  }

  // Hold on to a ton of small subsequences of huge sequences,
  // to ensure that if s[..] is used to make an explicit copy,
  // the huge sequences can be garbage collected.
  // Otherwise this test will run out of memory.
  //
  // (Note: in practice with the parameters as below
  // the process doesn't seem to run out of memory when I tested it.
  // With large values and without the support being tested, it does,
  // but then takes way too long to complete successfully with the support enabled.
  // I've settled for a mild stress test here for now.)
  method {:test} IntentionalCopying() {
    var n := 1_000;
    var m := 1_000_000;
    var a := new seq<int>[n];
    for i := 0 to n {
      var s: seq<int> := seq(m, i => 1);
      a[i] := TakeWithIntentionalCopy(s, 1);
    }
  }

  function TakeWithIntentionalCopy(s: seq<int>, n: nat): seq<int>
    requires n <= |s|
  {
    s[..n][..]
  }

  @TailRecursion
  function RecursiveSum(s: seq<int>): int {
    if |s| == 0 then
      0
    else
      s[0] + RecursiveSum(s[1..])
  }
}
