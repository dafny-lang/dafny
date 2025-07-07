// RUN: %tobinary %s --library > %t.dbin
// RUN: %verify --input-format Binary --allow-warnings --stdin < %t.dbin > %t
// RUN: %diff "%s.expect" "%t"

method Foo() {
  assert false; // no error, because this is a library
}