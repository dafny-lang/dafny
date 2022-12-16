// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
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
