// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /Main:A.Test "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /Main:B.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:C.Test "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /Main:D.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:E.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:G.Test "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /Main:H.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:I.Test "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /Main:J.Test "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /Main:K.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:       "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:-      "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /Main:Tr.Instance "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /Main:Opaque.Static   "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /Main:Opaque.Instance "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  method Test(i: int) { print "Bad\n"; }
}
class B {
  method Test<T>() { print "Bad\n"; }
}
class C<T> {
  method Test() { print "OK-C\n"; }
}
class D {
  constructor() {}
  method Test() { print "Bad\n"; }
}
class E {
  constructor() {}
  static method Test() { print "OK-E\n"; }
}
class G {
  method Test(ghost i: int) { print "OK-G\n"; }
}
class H {
  method Test() returns (i: int) { print "Bad\n"; }
}
class I {
  method Test() returns (ghost i: int) { print "OK-I\n"; }
}
class J {
  method Test() requires true { print "Bad\n"; }
}
class K {
  method Test() modifies {} { print "Bad\n"; }
}
class Z {
  method Main() { print "Main\n"; }
}

// Of the remaining methods, this file tests only the error cases.
// The cases that compile are tested in Test/comp/MainMethod.dfy.

trait Tr {
  static method Static() { print "OK-Tr\n"; }
  method Instance() { print "Bad\n"; }
}

datatype Dt = Dt0(int) | Dt1(real) {
  static method Static() { print "OK-Dt: static\n"; }
  method Instance() { print "OK-Dt: ", this, "\n"; }
}

codatatype Co = CoMore(Co) {
  static method Static() { print "OK-Co: static\n"; }
  method Instance() { print "OK-Co: ", this, "\n"; }
}

newtype Nt = x | -0x8000_0000 <= x <= 0x8000_0000 {
  static method Static() { print "OK-Nt: static\n"; }
  method Instance() { print "OK-Nt: ", this, "\n"; }
}

type {:extern "OpaqueX"} Opaque {
  static method Static() { print "Bad\n"; }
  method Instance() { print "Bad\n"; }
}
