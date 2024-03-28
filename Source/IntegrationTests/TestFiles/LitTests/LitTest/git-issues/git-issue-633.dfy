// NONUNIFORM: need to add support for --input when running to %testDafnyForEachCompiler
// RUN: %verify "%s" %S/git-issue-633A.dfy > "%t"
// RUN: %run --no-verify --target cs /spillTargetCode:3 "%s" %S/git-issue-633A.dfy >> "%t"
// RUN: %dafny /noVerify /compile:4 --target js /spillTargetCode:3 "%s" %S/git-issue-633A.dfy >> "%t"
// RUN: %dafny /noVerify /compile:4 --target go /spillTargetCode:3 "%s" %S/git-issue-633A.dfy >> "%t"
// RUN: %dafny /noVerify /compile:4 --target java /spillTargetCode:3 "%s" %S/git-issue-633A.dfy  >> "%t"
// RUN: %dafny /noVerify /compile:4 --target py /spillTargetCode:3 "%s" %S/git-issue-633A.dfy  >> "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  print "OK\n";
}
