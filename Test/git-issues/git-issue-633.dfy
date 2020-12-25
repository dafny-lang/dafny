// RUN: %dafny /compile:0 "%s" git-issue-633A.dfy > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /spillTargetCode:3 "%s" git-issue-633A.dfy >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /spillTargetCode:3 "%s" git-issue-633A.dfy >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /spillTargetCode:3 "%s" git-issue-633A.dfy >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /spillTargetCode:3 "%s" git-issue-633A.dfy  >> "%t"
// RUN: sed -e 'sx\\x/x' < "%t" > "%t"2
// RUN: %diff "%s.expect" "%t"2

method m() {
  print "OK\n";
}
