// RUN: %baredafny build %args -t:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

test.dfy:
include "main.dfy"

method Main() {
  var undertest := new TestLogic''TopLevel();
  print "COMPLETED OK\n";
}

main.dfy:
class TestLogic''TopLevel {
  constructor () 
  {
  }
}