// RUN: %testDafnyForEachResolver "%s"

// Regression test: accessing a const with a default value that calls a static
// function of a generic parent trait caused a Boogie resolution error because
// the type parameter substitution was missing.

trait T<E> {
  static ghost function h(): seq<E>
  ghost const c: seq<E> := h()
  function f(): int ensures |c| >= 0
}
class C<E> extends T<E> {
  function f(): int ensures |c| >= 0 { 0 }
}
