// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --spill-translation /Users/salkeldr/Documents/GitHub/dafny/Test/git-issues/git-issue-633A.dfy

method m() {
  print "OK\n";
}
