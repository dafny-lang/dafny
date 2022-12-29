// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait A {}
trait B {}
class C extends A, B {
  method Foo() {
    assert false; // error: but this once used to pass
  }
}
