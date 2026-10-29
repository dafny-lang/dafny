// Generic comparison of extern references without an equals method used to
// crash with "a.equals is not a function"; they now compare by identity
// (https://github.com/dafny-lang/dafny/issues/6491).
// RUN: %run --target js "%s" --input %S/Inputs/BoxPkg.js > "%t"
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

    var s := {a, b};    // used to crash building the set
    assert |s| == 2;
    print |s|, "\n";

    assert a in s && b in s;
    print a in s, " ", b in s, "\n";
  }
}
