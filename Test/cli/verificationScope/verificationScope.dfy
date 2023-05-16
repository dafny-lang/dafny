// RUN: ! %baredafny verify %args --verify-scope=RootSourcesAndIncludes --library="%S/library.dfy" "%s" 2> "%t"
// RUN: ! %baredafny verify %args --verify-scope=RootSources --library="%S/library.doo" "%s" >> "%t"
// RUN: ! %baredafny verify %args --verify-scope=RootSourcesAndIncludes --library="%S/library.doo" "%s" >> "%t"
// RUN: ! %baredafny verify %args --verify-scope=Everything --library="%S/library.dfy" "%s" >> "%t"
// RUN: ! %baredafny verify %args --verify-scope=Everything --library="%S/library.doo" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "./includedByDirective.dfy"
method Foo() {
  assert false;
}