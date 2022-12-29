// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

trait Trait<Y> {
  const y: Y
  const k: Y := y
  const l: Y
}

class ClassB extends Trait<array<bv8>> {
  var m: array<bv8>
  constructor () { m := new bv8[42]; }
}

class ClassC extends Trait<array3<bv8>> {
  var m: array3<bv8>
  constructor () { m := new bv8[8, 9, 10]; }
}

method Main() {
  var cb := new ClassB();
  print cb.y.Length, " ", cb.k.Length, " ", cb.l.Length, " ", cb.m.Length, "\n";
  var cc := new ClassC();
  print cc.y.Length1, " ", cc.k.Length1, " ", cc.l.Length1, " ", cc.m.Length1, "\n";
}

