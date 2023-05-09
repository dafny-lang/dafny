// RUN: ! %baredafny verify %args --verify-scope=RootFiles --library="%S/library.dfy" "%s" > "%t"
// RUN: ! %baredafny verify %args --verify-scope=IncludeDirectives --library="%S/library.dfy" "%s" >> "%t"
// RUN: ! %baredafny verify %args --verify-scope=Libraries --library="%S/library.dfy" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "./includedByDirective.dfy"
method Foo() {
  assert false;
}