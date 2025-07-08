// RUN: %testDafnyForEachResolver "%s"

// this once crashed, because the implicit postcondition didn't include the type parameter
predicate Foo<A>() {
  true
} by method {
  return true;
}
