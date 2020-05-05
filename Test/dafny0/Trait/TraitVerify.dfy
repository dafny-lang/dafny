// RUN: %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Tr<X> { }

class A extends Tr<int> { }
class B extends Tr<real> { }
class C<Y> extends Tr<Y> { }

method M(a: A, b: B) {
  var c: C?;
  var t;  // Tr?<int>
  t := a;
  t := c;
}

method N(a: A, b: B) {
  var c: C?<int>;
  var t: Tr<int>;
  t := a;
  t := c;  // error: c may be null
}

method Q(a: A?) returns (t: Tr<int>) {
  t := a;  // error: a may be null
}

method P(a: A?) {
  var t: A;
  t := a;  // error: a may be null
}

method R(a: A) {
  var t: A?;
  t := a;
}
