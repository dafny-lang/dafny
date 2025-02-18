// RUN: %tobinary %s > %t.assertFalse.dbin
// RUN: ! %verify --input-format Binary --stdin < %t.assertFalse.dbin > %t
// RUN: %diff "%s.expect" "%t"

method Foo() {
  assert false;
}