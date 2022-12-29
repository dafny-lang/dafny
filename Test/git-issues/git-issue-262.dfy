// RUN: %baredafny run %args --target=cs "%s" > "%t"
// RUN: %baredafny run %args --target=js "%s" >> "%t"
// RUN: %baredafny run %args --target=go "%s" >> "%t"
// RUN: %baredafny run %args --target=java "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function method tst(x: nat): nat {
    x + 1
}

method Main() {
  var f := tst;
  print f, "\n";
  print tst, "\n";
}
