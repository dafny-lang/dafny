// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Y<+U> = Y(y: U)

trait Tr {}
class Cl extends Tr {
  constructor () {}
}

method Main() {
  // Because Y is an erasable type wrapper, it gets compiled as its argument,
  // so even Java supports this one.
  var cl := new Cl();
  var e: Y<Tr> := Y(cl);
  match e
  case Y(tr) => return;
}
