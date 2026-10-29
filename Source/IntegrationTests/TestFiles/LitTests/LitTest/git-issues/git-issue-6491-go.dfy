// An extern Go class is compared correctly by the built-in collections only if it
// implements the runtime's EqualsGeneric interface as identity; Dafny cannot
// generate that method for a type declared in another Go package. See "Equality of
// extern types" in the reference manual, and Inputs/BoxPkg.go for the
// implementation this test relies on (https://github.com/dafny-lang/dafny/issues/6491).
// RUN: %run --target go "%s" --input %S/Inputs/BoxPkg.go > "%t"
// RUN: %diff "%s.expect" "%t"
module {:extern "BoxPkg"} BoxPkg {
  class {:extern} Box {
    constructor {:extern} ()
  }
}

module Repro {
  import opened BoxPkg

  method Main() {
    var a := new Box();
    var b := new Box(); // distinct object; structurally identical

    assert a != b;
    print a != b, "\n";

    var s := {a, b};
    assert |s| == 2;
    print |s|, "\n";
  }
}
