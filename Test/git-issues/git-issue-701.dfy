// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
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
