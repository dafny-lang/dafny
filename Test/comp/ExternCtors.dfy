/*
---
!dafnyTestSpec
compileTargetOverrides:
    java:
        otherFiles:
            - Class.java
    cs:
        otherFiles:
            - ExternCtors-externs/Library.cs
    js:
        otherFiles:
            - ExternCtors-externs/Library.js
        expected:
            # The expected exit code should be 3, but /countVerificationErrors:0 is overriding that
            # https://github.com/dafny-lang/dafny/issues/887
            outputFile: ~
            specialCaseReason: Extern constructors are currently broken in JavaScript
    go:
        otherFiles:
            - ExternCtors-externs/Library.go
        expected:
            # The expected exit code should be 3, but /countVerificationErrors:0 is overriding that
            # https://github.com/dafny-lang/dafny/issues/887
            outputFile: ~
            specialCaseReason: Extern constructors are currently broken in Go
*/
method Main() {
  Library.Class.SayHi();
  var obj := new Library.Class(42);
  obj.Print();
}

module {:extern "Library"} Library {
  class {:extern} Class {
    constructor {:extern} (n: int)
    static method {:extern} SayHi()
    function method {:extern} Get() : int
    method Print() {
      print "My value is ", Get(), "\n";
    }
  }
}
