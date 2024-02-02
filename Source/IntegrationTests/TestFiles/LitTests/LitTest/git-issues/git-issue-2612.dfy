// RUN: %testDafnyForEachResolver "%s"


trait T {
  ghost predicate {:opaque} True() { true }
}

class C extends T {}
