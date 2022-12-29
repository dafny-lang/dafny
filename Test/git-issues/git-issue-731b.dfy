// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Testing issue#731 when the class in question has type parameters

trait Tr2<W, Y> {
  const w: W
  const y: Y
}

class ClassA<Q> extends Tr2<Q, array<bv8>> {
  constructor (q: Q) { w := q; }
}

method Main() {
  var a := new int[42];
  var ca := new ClassA<array<int>>(a);
  print ca.y.Length, " ", ca.w.Length, "\n";
}

