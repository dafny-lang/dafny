// RUN: %baredafny build %args -t:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue-4139-helper.dfy"

method Main() {
  var undertest := new TestLogic''TopLevel();
  print "COMPLETED OK\n";
}