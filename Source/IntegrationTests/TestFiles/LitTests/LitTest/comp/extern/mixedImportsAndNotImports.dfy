// RUN: ! %build --target java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class {:extern} HalfExtern {
  method {:extern} Foo(x: int) {
    print x;
  }

  method {:extern} Bar(x: int)
}