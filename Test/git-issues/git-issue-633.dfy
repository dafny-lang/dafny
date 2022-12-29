// RUN: %baredafny verify %args "%s" %S/git-issue-633A.dfy > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" %S/git-issue-633A.dfy >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" %S/git-issue-633A.dfy >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" %S/git-issue-633A.dfy >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" %S/git-issue-633A.dfy  >> "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  print "OK\n";
}
