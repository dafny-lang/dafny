// Reference-type equality must compare identity even when an extern class
// overrides __eq__ (https://github.com/dafny-lang/dafny/issues/6491).
// RUN: %run --target py "%s" --input %S/Inputs/BoxPkg.py > "%t"
// RUN: %diff "%s.expect" "%t"
module {:extern "BoxPkg"} BoxPkg {
  class {:extern} Box {
    constructor {:extern} ()
  }
}

module Repro {
  import opened BoxPkg

  datatype D = D(b: Box, tag: int)

  type NBox = b: Box? | b != null witness *

  method Main() {
    var a := new Box();
    var b := new Box(); // distinct object; extern __eq__ calls any two boxes equal

    assert a != b;
    print a != b, "\n";

    var d1 := D(a, 0);
    var d2 := D(b, 0);
    assert d1 != d2;
    print d1 != d2, "\n";

    // Subset types over reference types compare by identity too.
    var na: NBox := a;
    var nb: NBox := b;
    assert na != nb;
    print na != nb, "\n";

    // Comparisons against null still work.
    var c: Box? := null;
    var d: Box? := a;
    print c == null, " ", d != null, "\n";

    // A tuple holding a reference compares that component by identity too. A Dafny tuple compiles
    // to a native Python tuple, which cannot be given a custom __eq__, so this goes through the
    // runtime's tuple_eq with a mask saying which components are references.
    var ta := (a, 1);
    var tb := (b, 1);
    assert ta != tb;
    print ta != tb, " ", ta == ta, "\n";

    // Nested tuples, and a tuple in a datatype field, take the same route.
    var na2 := ((a, 1), 2);
    var nb2 := ((b, 1), 2);
    assert na2 != nb2;
    print na2 != nb2, "\n";
    print Pair((a, 1), 0) != Pair((b, 1), 0), "\n";

    // A tuple of values is unaffected: no mask is emitted for it at all.
    print (1, 2) == (1, 2), "\n";
  }

  datatype Pair = Pair(t: (Box, int), tag: int)
}
