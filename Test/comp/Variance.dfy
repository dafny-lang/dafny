// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Co<+T> = Co(z: T) {
    const x: int;
    const y: seq<T>

    function A(x: T): int { 0 }
    static function sA(x: T): int { 0 }
    function gA(ghost x: T): int { 0 }
    function B(x: seq<T>): int { 0 }
    function C(x: int): seq<T> { y }
    function D(x: T): T { x }

    method mA(x: T) returns (r: int) { r := 0; }
    method mD(x: T) returns (r: T) { r := x; }
}

datatype Non<T> = Non(T) {
    const x: int;
    const y: seq<T>

    function A(x: T): int { 0 }
    static function sA(x: T): int { 0 }
    function gA(ghost x: T): int { 0 }
    function B(x: seq<T>): int { 0 }
    function C(x: int): seq<T> { y }
    function D(x: T): T { x }

    method mA(x: T) returns (r: int) { r := 0; }
    method mD(x: T) returns (r: T) { r := x; }
}

datatype Cont<-T> = Cont(z: T -> int) {
    const x: int;
    const y: seq<T>

    function A(x: T): int { 0 }
    static function sA(x: T): int { 0 }
    function gA(ghost x: T): int { 0 }
    function B(x: seq<T>): int { 0 }
    function C(x: int): seq<T> { y }
    function D(x: T): T { x }

    method mA(x: T) returns (r: int) { r := 0; }
    method mD(x: T) returns (r: T) { r := x; }
}

codatatype CCo<+T> = CCo(T) {
    const x: int;
    const y: seq<T>

    function A(x: T): int { 0 }
    static function sA(x: T): int { 0 }
    function gA(ghost x: T): int { 0 }
    function B(x: seq<T>): int { 0 }
    function C(x: int): seq<T> { y }
    function D(x: T): T { x }

    method mA(x: T) returns (r: int) { r := 0; }
    method mD(x: T) returns (r: T) { r := x; }
}

codatatype CNon<T> = CNon(z: T) {
    const x: int;
    const y: seq<T>

    function A(x: T): int { 0 }
    static function sA(x: T): int { 0 }
    function gA(ghost x: T): int { 0 }
    function B(x: seq<T>): int { 0 }
    function C(x: int): seq<T> { y }
    function D(x: T): T { x }

    method mA(x: T) returns (r: int) { r := 0; }
    method mD(x: T) returns (r: T) { r := x; }
}

codatatype CCon<-T> = CCon(T -> int) {
    const x: int;
    const y: seq<T>

    function A(x: T): int { 0 }
    static function sA(x: T): int { 0 }
    function gA(ghost x: T): int { 0 }
    function B(x: seq<T>): int { 0 }
    function C(x: int): seq<T> { y }
    function D(x: T): T { x }

    method mA(x: T) returns (r: int) { r := 0; }
    method mD(x: T) returns (r: T) { r := x; }
}

trait X {}

class Int extends X {
  constructor Int() { }
}

method Covariant() {
  var i := new Int.Int();
  var a: Co<Int> := Co(i);
  var b: Co<X>; // compilation error (java only): compilation does not support trait types as a type parameter; consider introducing a ghost
  b := a;
  print a, " and ", b, "\n";

  var s := Co(false);
  var t := s.mD(true);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), Co.sA(t), s.gA(t), "\n"; 
}

method Nonvariant() {
  var i := new Int.Int();
  var j := new Int.Int();
  var a: Non<Int> := Non(i);
  var b: Non<Int>;
  b := a;
  print a, " and ", b, "\n";
  
  var s := Non(false);
  var t := s.mD(true);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), Non.sA(t), s.gA(t), "\n"; 
}

method Contravariant() {
  var i := new Int.Int();
  var a: Cont<X> := Cont(_ => 0);  // compilation error (java only): compilation does not support trait types as a type parameter; consider introducing a ghost
  var b: Cont<Int>;
  b := a;
  print a.z(i), " and ", b.z(i), "\n";

  var s: Cont<X> := Cont(_ => 1);
  var t := s.mD(i);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), Cont.sA(t), s.gA(t), "\n"; 
}

method CCovariant() {
  var i := new Int.Int();
  var a: CCo<Int> := CCo(i);
  var b: CCo<X>; // compilation error (java only): compilation does not support trait types as a type parameter; consider introducing a ghost
  b := a;
  print a, " and ", b, "\n";

  var s := CCo(false);
  var t := s.mD(true);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), CCo.sA(t), s.gA(t), "\n"; 
}

method CNonvariant() {
  var i := new Int.Int();
  var j := new Int.Int();
  var a: CNon<Int> := CNon(i);
  var b: CNon<Int>;
  b := a;
  print a, " and ", b, "\n";
  
  var s := CNon(false);
  var t := s.mD(true);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), CNon.sA(t), s.gA(t), "\n"; 
}

method CContravariant() {
  var a: CCon<X> := CCon(_ => 0); // compilation error (java only): compilation does not support trait types as a type parameter; consider introducing a ghost
  var b: CCon<Int>;
  b := a;
  print a, " and ", b, "\n";

  var s: CCon<X> := CCon(_ => 1);
  var i := new Int.Int();
  var t := s.mD(i);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), CCon.sA(t), s.gA(t), "\n"; 
}

method Main(){
  Covariant();
  Nonvariant();
  Contravariant();
  CCovariant();
  CNonvariant();
  CContravariant();
  print "Done\n";
}
