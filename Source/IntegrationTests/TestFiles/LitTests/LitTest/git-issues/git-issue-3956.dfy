// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

datatype AAA<X> = CtorA
datatype BBB<Y> = CtorB
type AaaBbb<R> = AAA<BBB<R>>
datatype MyType<W> = MyType(n: AaaBbb<W>)

method Main() {
  var m: MyType<char> := MyType(CtorA);
  print m, "\n"; // AAA.CtorA
}
