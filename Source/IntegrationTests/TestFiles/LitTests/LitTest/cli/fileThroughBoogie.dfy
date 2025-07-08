// RUN: %verify --boogie "noDashAtStart" %s 2> %t
// RUN: %diff "%s.expect" "%t"

method Foo() { }