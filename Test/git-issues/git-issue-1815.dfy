// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype X<+U> = X(x: U)

trait Tr {}
class Cl extends Tr {
    constructor () {}
}

method Main() {
    var cl := new Cl();
    var e: X<Tr> := X(cl);
    match e
    case X(tr) => return;
}
