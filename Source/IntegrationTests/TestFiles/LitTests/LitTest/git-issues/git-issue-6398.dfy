// RUN: %testDafnyForEachResolver "%s"

// Regression test: reading a const inherited from a generic trait, whose default value calls a
// static function of that trait, caused a Boogie resolution error ("undeclared identifier:
// _module.T$E") because the type parameter substitution was missing.
//
// All three ingredients are needed, checked by ablation against the base commit: the trait has to
// be generic, the const's default value has to contain the call (a bare `const c: seq<E>` does
// not trigger it), and the function it calls has to be static. Overriding a trait member is not
// needed -- reading the const from any member of the class is enough, as ReadInheritedConst below
// shows.

trait T<E> {
  static ghost function h(): seq<E>
  ghost const c: seq<E> := h()
  function f(): int ensures |c| >= 0
}
class C<E> extends T<E> {
  function f(): int ensures |c| >= 0 { 0 }
}

// No override involved: C declares its own f, which reads the inherited const.
trait T2<E> {
  static ghost function h2(): seq<E>
  ghost const c2: seq<E> := h2()
}
class C2<E> extends T2<E> {
  function f2(): int ensures |c2| >= 0 { 0 }
}
