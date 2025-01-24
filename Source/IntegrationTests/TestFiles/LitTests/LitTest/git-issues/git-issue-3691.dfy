// RUN: %testDafnyForEachResolver "%s"


trait A {
  predicate f()
  method g() ensures f()
}

class B<T> extends A {
  predicate f() { true }
  method g() ensures f()
}
