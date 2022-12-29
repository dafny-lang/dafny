// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var ca := new ClassA;
  print ca.y, " ", ca.k, " ", ca.l, "\n";
  var cb := new ClassB;
  print cb.y[..], " ", cb.k[..], " ", cb.l[..], "\n";
  var cc := new ClassC;
  print cc.y, " ", cc.k, " ", cc.l, "\n";
}

trait Trait<Y> {
  const y: Y
  const k: Y := y
  const l: Y
}

datatype C<T> = Atom(T) | Nothing

class ClassA extends Trait<bv8> { }
class ClassB extends Trait<array<bv8>> { }
class ClassC extends Trait<C<bv8>> { }
