// RUN: %run --target cs "%s" --input %S/ExternCtors-externs/Library.cs > "%t"
// RUN: %run --target java "%s" --input %S/ExternCtors-externs/Class.java >> "%t"
// RUN: %run --target py "%s" --input %S/ExternCtors-externs/Library.py >> "%t"
// RUN: %run --target go "%s" --input %S/ExternCtors-externs/Library.go >> "%t"
// RUN: %diff "%s.expect" "%t"

// FIXME: Extern constructors are currently broken in JavaScript,
// so that is omitted

method Main() {
  Library.Class.SayHi();
  var obj := new Library.Class(42);
  print "My value is ", obj.Get(), "\n";
}

module {:extern "Library"} Library {
  class {:extern} Class {
    constructor {:extern} (n: int)
    static method {:extern} SayHi()
    function {:extern} Get() : int
  }
}

