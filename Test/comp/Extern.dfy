// RUN: %dafny /compile:3 /compileTarget:cs "%s" Extern2.cs > "%t"
// RUN: %dafny /compile:3 /compileTarget:js "%s" Extern3.js >> "%t"
// RUN: %dafny /compile:3 /compileTarget:go "%s" Extern4.go >> "%t"
// RUN: %dafny /compile:3 /compileTarget:java "%s" LibClass.java Mixed.java AllExtern.java >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Hello\n";
  var x, y := Library.LibClass.CallMeInt(30);
  var z := Library.LibClass.CallMeNative(44, true);
  print x, " ", y, " ", z, "\n";
  
  Library.AllDafny.M();
  Library.Mixed.M();
  Library.Mixed.P();
  Library.AllExtern.P();
  assert Library.AllDafny.Seven() == Library.Mixed.Seven() == Library.AllExtern.Seven();
}

module {:extern "Library"} Library {
  newtype MyInt = x | -100 <= x < 0x8000_0000
  class {:extern "LibClass"} LibClass {
    static method {:extern} CallMeInt(x: int) returns (y: int, z: int)
    static method {:extern} CallMeNative(x: MyInt, b: bool) returns (y: MyInt)
  }
  
  class AllDafny {
    static function Seven(): int { 7 }
    static method M() { print "AllDafny.M\n"; }
  }
  class {:extern} Mixed {
    static function Seven(): int { 7 }
    static method M() { print "Mixed.M\n"; }
    static method {:extern} P()
  }
  class {:extern} AllExtern {
    static function Seven(): int { 7 }
    static method {:extern} P()
  }
}
