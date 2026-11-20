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

// No override involved: the class declares a member of its own that reads the inherited const.
trait GenericTrait<E> {
  static ghost function staticCall(): seq<E>
  ghost const inherited: seq<E> := staticCall()
}
class ReadInheritedConst<E> extends GenericTrait<E> {
  function usesIt(): int ensures |inherited| >= 0 { 0 }
}
