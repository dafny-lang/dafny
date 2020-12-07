// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module P {
  datatype T_ = T()  // the underscore in this name once caused a problem in Java compilation
  type T = t:T_ | true ghost witness T()
}

module C refines P {
  datatype C = C(t: T)  // this had once caused a bogus error about cyclic dependencies
}

module OtherNamesWithSpecialCharacters?_ {
  datatype A?_ = A?_
  codatatype B?_ = B?_
  trait Tr?_ { var data: int }
  class Cl?_ extends Tr?_ { }
  type Threes?_ = x: int | x % 3 == 0
  newtype Fives?_ = x: int | x % 5 == 0

  method Test() {
    var a: A?_;
    var b: B?_ := B?_;
    print a, " ", b, "\n";

    var c: Cl?_ := new Cl?_;
    var t: Tr?_ := c;
    c.data := 17;
    var x3: Threes?_;
    var x5: Fives?_;
    print c.data, " ", t.data, " ", x3, " ", x5, "\n";
  }
}

method Main() {
  var t: C.T := C.T;  // this had once caused malformed Java, because of a missing qualified name
  var c := C.C(t);
  print c, "\n";

  var pt: P.T := P.T;
  print pt, "\n";

  OtherNamesWithSpecialCharacters?_.Test();
}
