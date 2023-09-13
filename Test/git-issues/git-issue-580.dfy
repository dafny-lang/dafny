// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


trait A {}
trait B {}
class C extends A, B {
  method Foo() {
    assert false; // error: but this once used to pass
  }
}
