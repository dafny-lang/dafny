// RUN: ! %testDafnyForEachCompiler --refresh-exit-code=0 "%s" > "%t"
// RUN: %diff "%s.testdafny.expect" "%t"

method Main() {
  ghost var n := 15;
  assert n < 12; // error: the verifier complains about this
  print "hello\n";
}
