//RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 /dprint:"%t.dfy" "%s"
//RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 "%t.dfy" > "%t.output"
//RUN: %diff "%s.expect" "%t.output"

method M() {
  ghost var h := var ta := F(); 5;
  var j := ghost var tb := F(); 5;
  assert h == j;
}

function F(): int { 5 }

