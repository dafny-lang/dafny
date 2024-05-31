
// RUN: %baredafny translate cs %args %s --translation-record %S/Bar.dtr &> %t
// RUN: %exits-with 3 %baredafny translate cs %args %s --translation-record %S/Foo.dtr &>> %t
// RUN: %exits-with 3 %baredafny translate cs %args %s --translation-record %S/Bar.dtr --translation-record %S/Bar.dtr &>> %t
// RUN: %diff "%s.expect" "%t"

module Foo {
  method Main() {

  }
}