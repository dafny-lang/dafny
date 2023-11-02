// RUN: ! %testDafnyForEachCompiler --refresh-exit-code=0 "%s" > "%t"
// RUN: %diff "%s.testdafny.expect" "%t"

method Main() {
  ghost var n := 15;
  if j :| 0 <= j < n { // this gives a no-trigger warning
  }
  print "hello\n";
}
