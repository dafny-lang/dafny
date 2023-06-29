// RUN: %dafny /compile:3 /compileTarget:cs "%s" %S/ExternCtors-externs/Library.cs > "%t"
// RUN: %dafny /compile:3 /compileTarget:java "%s" %S/ExternCtors-externs/Class.java >> "%t"
// RUN: %dafny /compile:3 /compileTarget:py "%s" %S/ExternCtors-externs/Library.py >> "%t"
// RUN: %diff "%s.expect" "%t"

// FIXME: Extern constructors are currently broken in Go and JavaScript,
// so they are omitted

method Main() {
  Library.Class.SayHi();
  var obj := new Library.Class(42);
  obj.Print();
}

module {:extern "Library"} Library {
  class {:extern} Class {
    constructor {:extern} (n: int)
    static method {:extern} SayHi()
    function {:extern} Get() : int
    method Print() {
      print "My value is ", Get(), "\n";
    }
  }
}
