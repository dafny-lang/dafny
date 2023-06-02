// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment /spillTargetCode:3 /Users/salkeldr/Documents/GitHub/dafny/Test/git-issues/git-issue-633A.dfy

method m() {
  print "OK\n";
}
