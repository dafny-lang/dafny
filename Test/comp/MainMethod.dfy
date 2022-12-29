// RUN: %baredafny verify %args "%s" > "%t"

// RUN: %dafny /noVerify /compile:4 /Main:Cl.Static   /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Cl.Instance /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Tr.Static   /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Dt.Static   /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Dt.Instance /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Co.Static   /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Co.Instance /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Nt.Static   /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Nt.Instance /compileTarget:cs "%s" >> "%t"

// RUN: %dafny /noVerify /compile:4 /Main:Cl.Static   /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Cl.Instance /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Tr.Static   /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Dt.Static   /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Dt.Instance /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Co.Static   /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Co.Instance /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Nt.Static   /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Nt.Instance /compileTarget:js "%s" >> "%t"

// RUN: %dafny /noVerify /compile:4 /Main:Cl.Static   /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Cl.Instance /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Tr.Static   /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Dt.Static   /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Dt.Instance /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Co.Static   /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Co.Instance /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Nt.Static   /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Nt.Instance /compileTarget:go "%s" >> "%t"

// RUN: %dafny /noVerify /compile:4 /Main:Cl.Static   /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Cl.Instance /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Tr.Static   /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Dt.Static   /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Dt.Instance /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Co.Static   /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Co.Instance /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Nt.Static   /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Nt.Instance /compileTarget:java "%s" >> "%t"

// RUN: %dafny /noVerify /compile:4 /Main:Cl.Static   /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Cl.Instance /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Tr.Static   /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Dt.Static   /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Dt.Instance /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Co.Static   /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Co.Instance /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Nt.Static   /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:Nt.Instance /compileTarget:py "%s" >> "%t"

// RUN: %diff "%s.expect" "%t"

type plural = x | 2 <= x witness 2

class Cl<X(0)> {
  var p: plural
  var c: real
  var x: X
  static method Static() { print "Cl: static\n"; }
  method Instance() { print "Cl: ", p, " ", c, " ", x, "\n"; }
}

trait Tr<X> {
  static method Static() { print "Tr: static\n"; }
}

datatype Dt<X> = Dt0(plural, X) | Dt1(real, X) {
  static method Static() { print "Dt: static\n"; }
  method Instance() { print "Dt: ", this, "\n"; }
}

codatatype Co<X> = CoMore(plural, X, Co) {
  static method Static() { print "Co: static\n"; }
  method Instance() { print "Co: ", this, "\n"; }
}

newtype Nt = x | -0x8000_0000 <= x <= 0x8000_0000 {
  const c: plural
  static method Static() { print "Nt: static\n"; }
  method Instance() { print "Nt: ", this, " ", c, "\n"; }
}
