// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Foo = Foo(Keys: (), Values: (), Items: (), IsLimit: (), IsSucc: (), Offset: (), IsNat: ())
