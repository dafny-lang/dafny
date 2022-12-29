// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Foo = Foo(Keys: (), Values: (), Items: (), IsLimit: (), IsSucc: (), Offset: (), IsNat: ())
