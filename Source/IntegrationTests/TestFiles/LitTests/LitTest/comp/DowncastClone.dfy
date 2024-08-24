// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --general-newtypes=true --type-system-refresh=true

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
  b := a as Co<Y>;
  print a, " and ", b, "\n";
}

method DowncastReCo() {
  var i := new Y();
  var a: ReCo<X> := ReCo(i);
  var b: ReCo<Y>;
  b := a as ReCo<Y>;
  print a, " and ", b, "\n";

  var s := new ClassWithFields(a as ReCo<Y>);
  print s.y, " "; 
  s.y := a as ReCo<Y>;
  print s.y, "\n";
}

method DowncastContra() {
  var y := new Y();
  var i: Contra<X> := Contra(_ => false);
  var a: Contra<Y> := i;
  var b: Contra<X>;
  b := a as Contra<X>;
  print a.f(y), " and ", b.f(y), "\n";
}

method DowncastReContra() {
  var y := new Y();
  var i: ReContra<X> := ReContra(_ => false);
  var a: ReContra<Y> := i;
  var b: ReContra<X>;
  b := a as ReContra<X>;
  print a.f(y), " and ", b.f(y), "\n";
}

method DowncastFunc() {
  var i := new Y();
  var a: bool -> X := (_ => i);
  var b: bool -> Y;
  b := a as bool -> Y;
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
