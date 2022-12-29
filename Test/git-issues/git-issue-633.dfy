// RUN: %baredafny verify %args "%s" %S/git-issue-633A.dfy > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /spillTargetCode:3 "%s" %S/git-issue-633A.dfy >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /spillTargetCode:3 "%s" %S/git-issue-633A.dfy >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /spillTargetCode:3 "%s" %S/git-issue-633A.dfy >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /spillTargetCode:3 "%s" %S/git-issue-633A.dfy  >> "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  print "OK\n";
}
