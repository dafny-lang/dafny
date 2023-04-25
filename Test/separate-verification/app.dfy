
// Use case #1: only verifying separately, but compiling into a single unit

// RUN: %baredafny build %args -t:lib %S/Inputs/wrappers.dfy > %t
// RUN: %baredafny build %args -t:lib %S/Inputs/seq.dfy --library %S/Inputs/wrappers.doo >> %t
// RUN: %baredafny run   %args %s --library %S/Inputs/seq.doo --library %S/Inputs/wrappers.doo >> %t
// RUN: %diff "%s.expect" %t

// include "wrappers.dfy"
// include "seq.dfy"

module App {

  import opened Seq

  method Main() {
    var a := [1, 2, 3];
    var b := [4, 5, 6];
    var c := [7, 8, 9];

    LemmaConcatIsAssociative(a, b, c);
    assert (a + b) + c == a + (b + c);

    print a + b + c, "\n";
  }

}