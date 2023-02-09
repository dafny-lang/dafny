// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  predicate P()
    reads {this}
}

class C extends T {
  predicate P() // predicate's decreases clause must be below or equal to that in the trait
  {
    true
  }
}
