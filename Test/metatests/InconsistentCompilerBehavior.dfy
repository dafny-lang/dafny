// RUN: ! %testDafnyForEachCompiler "%s" > "%t"
// RUN: %diff "%s.testdafny.expect" "%t"

// A %testdafny test case expected to fail, since at the time of
// writing this every runtime prints function values differently. :)

method Main() {
  var fn := (x: int) => x;
  print fn, "\n";
}
