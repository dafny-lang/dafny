// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// The Java compiler lacks support for this (see dafny0/RuntimeTypeTests0.dfy).

datatype Co<+T> = Co(T){
    const x : int;
    const y : seq<T>;

    function method A(x : T) : int { 0 }
    static function method sA(x : T) : int { 0 }
    function method gA(ghost x : T) : int { 0 }
    function method B(x : seq<T>) : int { 0 }
    function method C(x : int) : seq<T> { [] }
    function method D(x : T) : T { x }

    method mA(x : T) returns (r: int) { r := 0; }
    method mD(x : T) returns (r: T) { r := x; }
}

datatype In<T> = In(T){
    const x : int;
    const y : seq<T>;

    function method A(x : T) : int { 0 }
    static function method sA(x : T) : int { 0 }
    function method gA(ghost x : T) : int { 0 }
    function method B(x : seq<T>) : int { 0 }
    function method C(x : int) : seq<T> { [] }
    function method D(x : T) : T { x }

    method mA(x : T) returns (r: int) { r := 0; }
    method mD(x : T) returns (r: T) { r := x; }
}

datatype Con<-T> = Con {
    const x : int;
    const y : seq<T>;

    function method A(x : T) : int { 0 }
    static function method sA(x : T) : int { 0 }
    function method gA(ghost x : T) : int { 0 }
    function method B(x : seq<T>) : int { 0 }
    function method C(x : int) : seq<T> { [] }
    function method D(x : T) : T { x }

    method mA(x : T) returns (r: int) { r := 0; }
    method mD(x : T) returns (r: T) { r := x; }
}

codatatype CCo<+T> = CCo(T){
    const x : int;
    const y : seq<T>;

    function method A(x : T) : int { 0 }
    static function method sA(x : T) : int { 0 }
    function method gA(ghost x : T) : int { 0 }
    function method B(x : seq<T>) : int { 0 }
    function method C(x : int) : seq<T> { [] }
    function method D(x : T) : T { x }

    method mA(x : T) returns (r: int) { r := 0; }
    method mD(x : T) returns (r: T) { r := x; }
}

codatatype CIn<T> = CIn(T){
    const x : int;
    const y : seq<T>;

    function method A(x : T) : int { 0 }
    static function method sA(x : T) : int { 0 }
    function method gA(ghost x : T) : int { 0 }
    function method B(x : seq<T>) : int { 0 }
    function method C(x : int) : seq<T> { [] }
    function method D(x : T) : T { x }

    method mA(x : T) returns (r: int) { r := 0; }
    method mD(x : T) returns (r: T) { r := x; }
}

codatatype CCon<-T> = CCon {
    const x : int;
    const y : seq<T>;

    function method A(x : T) : int { 0 }
    static function method sA(x : T) : int { 0 }
    function method gA(ghost x : T) : int { 0 }
    function method B(x : seq<T>) : int { 0 }
    function method C(x : int) : seq<T> { [] }
    function method D(x : T) : T { x }

    method mA(x : T) returns (r: int) { r := 0; }
    method mD(x : T) returns (r: T) { r := x; }
}

trait X {}

class Int extends X {
  constructor Int() { }
}

method Covariant() {
  var i := new Int.Int();
  var a: Co<Int> := Co(i);
  var b: Co<X>; // compilation error: compilation does not support trait types as a type parameter; consider introducing a ghost
  b := a;
  print a, " and ", b, "\n";

  var s := Co(false);
  var t := s.mD(true);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), Co.sA(t), s.gA(t), "\n"; 
}

method Invariant() {
  var i := new Int.Int();
  var j := new Int.Int();
  var a: In<Int> := In(i);
  var b: In<Int>;
  b := a;
  print a, " and ", b, "\n";
  
  var s := In(false);
  var t := s.mD(true);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), Co.sA(t), s.gA(t), "\n"; 
}

method Contravariant() {
  var a: Con<X> := Con();
  var b: Con<Int>;
  b := a;
  print a, " and ", b, "\n";

  var s := Con;
  var t := s.mD(true);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), Co.sA(t), s.gA(t), "\n"; 
}

method CCovariant() {
  var i := new Int.Int();
  var a: CCo<Int> := CCo(i);
  var b: CCo<X>; // compilation error: compilation does not support trait types as a type parameter; consider introducing a ghost
  b := a;
  print a, " and ", b, "\n";

  var s := CCo(false);
  var t := s.mD(true);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), Co.sA(t), s.gA(t), "\n"; 
}

method CInvariant() {
  var i := new Int.Int();
  var j := new Int.Int();
  var a: CIn<Int> := CIn(i);
  var b: CIn<Int>;
  b := a;
  print a, " and ", b, "\n";
  
  var s := CIn(false);
  var t := s.mD(true);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), Co.sA(t), s.gA(t), "\n"; 
}

method CContravariant() {
  var a: CCon<X> := CCon();
  var b: CCon<Int>;
  b := a;
  print a, " and ", b, "\n";

  var s := CCon;
  var t := s.mD(true);
  var y := s.mA(t);
  print t, y, s.C(s.x), s.B(s.y), s.A(t), Co.sA(t), s.gA(t), "\n"; 
}

method Main(){
  Covariant();
  Invariant();
  Contravariant();
  CCovariant();
  CInvariant();
  CContravariant();
  print "Done\n";
}