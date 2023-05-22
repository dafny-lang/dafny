// RUN: ! %baredafny build %args -t:lib "%s" > "%t"
// RUN: %baredafny build %args -t:lib --output="%S/Output" --verify-scope=RootSourcesAndIncludes "%s" >> "%t"
// RUN: ! %baredafny build %args -t:lib --no-verify --verify-scope=RootSourcesAndIncludes "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() {
  assert true;
}