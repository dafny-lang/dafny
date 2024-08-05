// RUN: %run "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Div {
  int Foo(int x) {
    return 3 / x;
  }
}