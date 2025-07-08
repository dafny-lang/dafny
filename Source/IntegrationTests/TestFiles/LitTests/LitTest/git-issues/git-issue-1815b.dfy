// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

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
