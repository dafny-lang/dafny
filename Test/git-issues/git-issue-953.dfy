// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
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
    print a, " ", b, "\n"; // A?_.A?_ B?_.B?_

    var c: Cl?_ := new Cl?_;
    var t: Tr?_ := c;
    c.data := 17;
    var x3: Threes?_;
    var x5: Fives?_;
    print c.data, " ", t.data, " ", x3, " ", x5, "\n"; // 17 17 0 0
  }
}

method Main() {
  var t: C.T := C.T;  // this had once caused malformed Java, because of a missing qualified name
  var c := C.C(t);
  print c, "\n"; // C_Compile.T_.T

  var pt: P.T := P.T;
  print pt, "\n"; // P_Compile.T_.T

  OtherNamesWithSpecialCharacters?_.Test();

  var t2: C2.T := C2.T(10);
  var c2 := C2.C(t2, 11);
  print c2, "\n"; // C2_Compile.C.C(10, 11)

  var pt2: P2.T := P2.T(9);
  print pt2, "\n"; // 9
}

module P2 {
  datatype T_ = T(y: int)
  type T = t:T_ | true ghost witness T(5)
}

module C2 refines P2 {
  datatype C = C(t: T, x: int)
}
