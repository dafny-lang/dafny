// Note we specify the set of compilers to test explicitly since we're looking at the actual output,
// and otherwise using DAFNY_INTEGRATION_TESTS_ONLY_COMPILERS breaks this test.

// RUN: ! %testDafnyForEachCompiler --refresh-exit-code=0 --compilers cs,java,go,js,cpp,dfy,py,rs "%s" > "%t"
// RUN: %diff "%s.testdafny.expect" "%t"

// A %testdafny test case expected to fail, since the given
// output is different than any actual output

method Main() {
  var i := 0;
  print i, "\n";
}
