// RUN: %verify "%s" &> "%t"
// RUN: %diff "%s.expect" "%t"

include "Inputs/producer.dfy"

class X {
  method Bar() {
    Foo();
  }
}