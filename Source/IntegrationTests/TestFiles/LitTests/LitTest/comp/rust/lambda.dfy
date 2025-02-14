// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint8 = x: int | 0 <= x < 256 

predicate F(f: bool -> bool) { f(false) }

predicate p(b: bool) { !b }

predicate Fn<T>(f: (T, T) -> bool, a: T) { f(a, a) }

predicate X() { F(p) }

predicate X'() { var f := x => !x; F(f) }

predicate F'(f: seq<bool> -> bool) { f([false]) }

predicate p'(b: seq<bool>) { if |b| > 0 then !b[0] else false }

predicate X''() { F'(p') }

method Main() {
  var f := (a: uint8, b: uint8) => a == b;
  print f, "\n";
  print Fn(f, 2 as uint8), "\n"; 
}