// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Co<+T> = Co(T) | C
datatype ReCo<+T> = ReCo(T)
datatype Contra<-T> = Contra(f: T -> bool) | C
datatype ReContra<-T> = ReContra(f: T -> bool)

trait X {}

class Y extends X {
  constructor () {}
}

class ClassWithFields {
  var y: ReCo<Y>
  constructor (y: ReCo<Y>) {
    this.y := y;
  }
}

method DowncastCo() {
  var i := new Y();
  var a: Co<X> := Co(i);
  var b: Co<Y>;
  b := a;
  print a, " and ", b, "\n";
}

method DowncastReCo() {
  var i := new Y();
  var a: ReCo<X> := ReCo(i);
  var b: ReCo<Y>;
  b := a;
  print a, " and ", b, "\n";

  var s := new ClassWithFields(a);
  print s.y, " "; 
  s.y := a;
  print s.y, "\n";
}

method DowncastContra() {
  var y := new Y();
  var i: Contra<X> := Contra(_ => false);
  var a: Contra<Y> := i;
  var b: Contra<X>;
  b := a;
  print a.f(y), " and ", b.f(y), "\n";
}

method DowncastReContra() {
  var y := new Y();
  var i: ReContra<X> := ReContra(_ => false);
  var a: ReContra<Y> := i;
  var b: ReContra<X>;
  b := a;
  print a.f(y), " and ", b.f(y), "\n";
}

method DowncastFunc() {
  var i := new Y();
  var a: bool -> X := (_ => i);
  var b: bool -> Y;
  b := a;
  print a(false), " and ", b(false), "\n";
}

method Main(){
  DowncastCo();
  DowncastReCo();
  DowncastContra();
  DowncastReContra();
  DowncastFunc();
  print "Done\n";
}
