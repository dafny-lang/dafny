// RUN: %baredafny run %args --target=cs "%s" %S/ExternCtors-externs/Library.cs > "%t"
// RUN: %baredafny run %args --target=java "%s" %S/ExternCtors-externs/Class.java >> "%t"
// RUN: %baredafny run %args --target=py "%s" %S/ExternCtors-externs/Library.py >> "%t"
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
    function method {:extern} Get() : int
    method Print() {
      print "My value is ", Get(), "\n";
    }
  }
}
