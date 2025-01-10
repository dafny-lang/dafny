// NONUNIFORM: need to add support for --input when running to %testDafnyForEachCompiler
// RUN: %verify "%s" %S/git-issue-633A.dfy > "%t"
// RUN: %run --no-verify --target cs "%s" --input %S/git-issue-633A.dfy >> "%t"
// RUN: %run --no-verify --target js "%s" --input %S/git-issue-633A.dfy >> "%t"
// RUN: %run --no-verify --target go "%s" --input %S/git-issue-633A.dfy >> "%t"
// RUN: %run --no-verify --target java "%s" --input %S/git-issue-633A.dfy  >> "%t"
// RUN: %run --no-verify --target py "%s" --input %S/git-issue-633A.dfy  >> "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  print "OK\n";
}
