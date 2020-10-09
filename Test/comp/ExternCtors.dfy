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
            outputFile: ~
            specialCaseReason: Extern constructors are currently broken in JavaScript
    go:
        otherFiles:
            - ExternCtors-externs/Library.go
        expected:
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
