// RUN: %baredafny resolve "" "%s" > "%t"
// RUN: %baredafny resolve '' "%s" >> "%t"
// RUN: %baredafny verify --boogie '' "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() {}
