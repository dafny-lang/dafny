// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Dt<+U> = Dt(x: U)

trait Tr {}
class Cl extends Tr {
  constructor () {}
}

method Main() {
  var cl: Cl := new Cl();
  var e: Dt<Tr> := Dt(cl);
  match e {
    case Dt(tr) =>
  }
  print "done\n";
}
