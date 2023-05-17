// RUN: ! %testDafnyForEachCompiler "%s" > "%t"
// RUN: %diff "%s.testdafny.expect" "%t"

// A %testdafny test case expected to fail, since the given
// output is different than any actual output

method Main() {
  var i := 0;
  print i, "\n";
}
