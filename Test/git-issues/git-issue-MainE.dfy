// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /Main:A.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:B.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:C.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:D.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:E.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:G.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:H.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:I.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:J.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:K.Test "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /Main:       "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:-      "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:Tr.Static   "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:Tr.Instance "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:Dt.Static   "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:Dt.Instance "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:Co.Static   "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:Co.Instance "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:Nt.Static   "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:Nt.Instance "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:Opaque.Static   "%s" >> "%t"
// %dafny /noVerify /compile:4 /Main:Opaque.Instance "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  method Test(i: int) { print "Bad\n"; }
}
class B {
  method Test<T>() { print "Bad\n"; }
}
class C<T> {
  method Test() { print "Bad\n"; }
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

trait Tr {
  static method Static() { print "Main\n"; }
  method Instance() { print "Bad\n"; }
}

datatype Dt = DtValue {
  static method Static() { print "Main\n"; }
  method Instance() { print "Bad\n"; }
}

codatatype Co = CoValue {
  static method Static() { print "Main\n"; }
  method Instance() { print "Bad\n"; }
}

newtype Nt = x | -0x8000_0000 <= x <= 0x8000_0000 {
  static method Static() { print "Main\n"; }
  method Instance() { print "Bad\n"; }
}
/*
type {:extern "ClassForOpaque"} Opaque {
  static method Static() { print "Main\n"; }
  method Instance() { print "Bad\n"; }
}
*/
