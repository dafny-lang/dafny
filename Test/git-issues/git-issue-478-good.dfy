// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// By first defining import LibA and then defining a module LibA,
// the latter used to generate:
//     duplicate module name: LibA
// This now works, and the effect is to imported LibA opened and
// not introduce another local name for it.
import opened LibA
module LibA {
  method Hello() {
    print "hello\n";
  }
}

// By first defining module LibB and then defining import LibB,
// the latter used to generate:
//     can't import module LibB when not inside of a module
// This now works, and the effect is to imported LibB opened and
// not introduce another local name for it.
module LibB {
  method Hi() {
    print "hi\n";
  }
}
import opened LibB

module LibC {
  method Hey() {
    print "hey\n";
  }
}
import opened C = LibC

module LibD {
  method Tjena() {
    print "tjena\n";
  }
}
import opened LibD = LibD  // name LibD explicitly

method Main() {
  Hello();  // via opened import
  LibA.Hello();  // via module name

  Hi();  // via opened import
  LibB.Hi();  // via module name

  Hey();  // via opened import
  C.Hey();  // via local name of import
  LibC.Hey();  // via module name

  Tjena();  // via opened import
  LibD.Tjena();  // via module name

  var w := Outer.B.P(2, 4);
  print w, "\n";  // 6
}

module Outer {
  module A {
    type T = int
  }
  module B {
    import opened A
    method P(u: A.T, v: T) returns (w: int) {
      w := u + v;
    }
  }
}
