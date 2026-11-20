// NONUNIFORM: Regression test for GitHub issue #6620 in the Rust runtime:
// indexing a sequence built by ~100000 singleton concatenations must not
// overflow the call stack while materializing it. The fix lives in the Rust
// runtime, so the test targets the Rust backend only, and it uses --no-verify
// to focus on the compiled program's behavior (the program was verified in the
// original issue report).
// RUN: %baredafny run --no-verify --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var numbers: seq<int> := [];
  var i := 0;
  while i < 100000
    invariant 0 <= i <= 100000
    invariant |numbers| == i
    invariant forall k :: 0 <= k < i ==> numbers[k] == k
  {
    numbers := numbers + [i];
    i := i + 1;
  }
  print numbers[99999] == 99999, "\n";
}
