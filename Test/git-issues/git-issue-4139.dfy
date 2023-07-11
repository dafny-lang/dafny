// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue-4139-main.dfy"

method Main() {
  var undertest := new TestLogic''TopLevel();
}