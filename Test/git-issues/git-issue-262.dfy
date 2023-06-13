// NONUNIFORM:
// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

function tst(x: nat): nat {
    x + 1
}

method Main() {
  var f := tst;
  print f, "\n";
  print tst, "\n";
}
