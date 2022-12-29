// RUN: %baredafny verify %args --print="%t.dprint.dfy" "%s" "%s"
// RUN: %baredafny verify %args "%t.dprint.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"

method M() {
  ghost var h := var ta := F(); 5;
  var j := ghost var tb := F(); 5;
  assert h == j;
}

function F(): int { 5 }

