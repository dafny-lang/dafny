// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Dt<+U> = Dt(x: U, i: int)

trait Tr {}
class Cl extends Tr {
  constructor () {}
}

method Main() {
  var cl: Cl := new Cl();
  var e: Dt<Tr> := Dt(cl, 1815);
  match e {
    case Dt(tr, _) =>
  }
  print "done\n";
}
