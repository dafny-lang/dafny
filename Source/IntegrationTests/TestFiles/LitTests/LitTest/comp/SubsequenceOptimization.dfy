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

  @TailRecursion
  function RecursiveSum(s: seq<int>): int {
    if |s| == 0 then
      0
    else
      s[0] + RecursiveSum(s[1..])
  }
}
