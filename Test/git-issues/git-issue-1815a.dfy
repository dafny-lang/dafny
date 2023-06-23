// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

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
