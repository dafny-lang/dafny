// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module V {
  import t = T  // error: T is not visible (and isn't even a module)
}

module A {
  import B = C
}

module C {
  import D = A
}
