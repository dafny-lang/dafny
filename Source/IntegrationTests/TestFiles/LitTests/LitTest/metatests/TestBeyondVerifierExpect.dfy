// Note we specify the set of compilers to test explicitly since we're looking at the actual output,
// and otherwise using DAFNY_INTEGRATION_TESTS_ONLY_COMPILERS breaks this test.

// RUN: ! %testDafnyForEachCompiler --refresh-exit-code=0 --compilers cs,java,go,js,cpp,dfy,py,rs "%s" -- --allow-warnings > "%t"
// RUN: %diff "%s.testdafny.expect" "%t"

method Main() {
  ghost var n := 15;
  if j :| 0 <= j < n { // this gives a no-trigger warning
  }
  print "hello\n";
}
