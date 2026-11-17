// NONUNIFORM: Regression test for GitHub issue #6620 in the Rust runtime:
// releasing a sequence built by ~100000 singleton concatenations that was
// never indexed or materialized must not overflow the call stack during its
// destruction. The fix lives in the Rust runtime, so the test targets the Rust
// backend only, and it uses --no-verify to focus on the compiled program's
// behavior (the shape of this program was validated in the issue report).
// RUN: %baredafny run --no-verify --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var numbers: seq<int> := [];
  var i := 0;
  while i < 100000
    invariant 0 <= i <= 100000
    invariant |numbers| == i
  {
    numbers := numbers + [i];
    i := i + 1;
  }
  // Reading only the cardinality leaves the concatenation tree unmaterialized.
  print |numbers|, "\n";
  // Releasing the sequence must dismantle the deep tree without overflowing
  // the stack; reaching the print below proves the process survived it.
  numbers := [];
  print "released", "\n";
}
