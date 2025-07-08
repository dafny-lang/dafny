// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

// Testing issue#731 when the class in question has type parameters

trait Tr2<W, Y> extends object {
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

