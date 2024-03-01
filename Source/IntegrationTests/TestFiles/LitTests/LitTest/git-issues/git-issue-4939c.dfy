// RUN: %testDafnyForEachCompiler "%s" -- --general-traits=datatype

module NoAutoInit {
  trait GeneralTrait { }
  trait ReferenceTrait extends object { }

  datatype A = A(g: GeneralTrait)
  datatype B = B(h: ReferenceTrait)

  method Main() {
    // Test that code generation succeeds, even thought "a" and "b" are never defined or used
    var a: A := *;
    var b: B := *;
    print "done\n";
  }
}
