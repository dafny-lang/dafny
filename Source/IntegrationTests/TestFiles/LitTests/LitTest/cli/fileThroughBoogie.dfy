// RUN: %verify --boogie "noDashAtStart" %s &> %t
// RUN: %diff "%s.expect" "%t"

method Foo() { }